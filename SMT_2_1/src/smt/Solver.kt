package smt

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import smt.parser.Expression
import smt.parser.SMTCommand
import smt.parser.SMTModelVisitor
import smt.parser.SMTScript
import smt.parser.gen.SMTLIBv2Lexer
import smt.parser.gen.SMTLIBv2Parser
import java.io.File
import smt.CongruenceClosure.UnionFind.Companion as UF


const val DEBUG_LOG = false

fun readFileDirectlyAsText(fileName: String): String
        = File(fileName).readText(Charsets.UTF_8)


fun main(args: Array<String>) {
    if (args.isEmpty()) {
        println("Usage: SMT_2_2 <file_path>.smt2")
        return
    }

    // Parsing stage
    val file = args[0]
    if (DEBUG_LOG) {
        println("[Info] Parsing file $file")
    }
    val content = readFileDirectlyAsText(file)
    val script = parseScript(content)

    // Script interpretation stage
    interpretScript(script)


    if (DEBUG_LOG) {
        println("Finish execution")
    }
}


/**
 * Parses provided script in SMT-LIBv2 format.
 * @return parsed script tree representation
 * @see SMTScript
 * @see SMTCommand
 */
private fun parseScript(content: String): SMTScript {
    val lexer = SMTLIBv2Lexer(CharStreams.fromString(content))
    val tokens = CommonTokenStream(lexer)
    val parser = SMTLIBv2Parser(tokens)
    val parseTree = parser.start().script()
    val visitor = SMTModelVisitor()
    val smtCommands: MutableList<SMTCommand> = visitor.visit(parseTree)
    val script = SMTScript(smtCommands)
    if (DEBUG_LOG) {
        println("[Info] Parsed script $script")
    }
    return script
}

/**
 * Script interpretation environment.
 * Contains all the entities needed for checking satisfiability of theory.
 */
val env: Environment = Environment()

private fun interpretScript(script: SMTScript) {

    for (command in script.commands) {
        when (command) {
            is SMTCommand.CmdAssert -> {
                val t = expressionToTerm(command.expression)
                assert(t is Term.EqualityFunctionApplication) // only `=` or `distinct` on upper level of expression allowed
                env.addAssert(t as Term.EqualityFunctionApplication)
            }
            is SMTCommand.CmdCheckSat -> {
                val dag = buildDAG()
                val sat = checkSat(dag)
                println(if (sat) "; sat" else "; unsat")
            }
            is SMTCommand.CmdDeclareSort -> {
                val sort = Sort(command.symbol, command.numeral)
                env.addSort(sort)
            }
            is SMTCommand.CmdDeclareFun -> {
                val args = command.args.map { s -> env.getSort(s) }.toList()
                val res = env.getSort(command.res)
                env.addFunction(UninterpretedFunction(command.name, args, res))
            }
            is SMTCommand.CmdSetLogic -> {
                val logic = command.logic
                if (!logic.equals("QF_UF") && !logic.equals("QF_EUF")) {
                    error("Unsupported logic \"$logic\"")
                }
                env.logic = command.logic
            }
            is SMTCommand.CmdGetModel -> {
                val dag = buildDAG()
                val sat = checkSat(dag)
                if (!sat) {
                    println("Could not find model values for unsatisfied model")
                    continue
                }
                env.assertsCongruenceClosure()
                val model = findModel(dag)
                ModelPrinter.printModel(model)

            }

            else -> TODO()
        }
    }
}

private fun buildDAG(): CongruenceClosure.DAG {
    val dag = CongruenceClosure.DAG.create(env.asserts.toList())
    if (DEBUG_LOG) {
        println("Graph: ${dag.graph}")
    }

    // apply all equalities and propagate functional congruence
    for (eq in env.equalities()) {
        val nodeLeft = dag.termToNode(eq.args[0])
        val nodeRight = dag.termToNode(eq.args[1])
        dag.merge(nodeLeft, nodeRight)
    }
    return dag
}

private fun checkSat(dag: CongruenceClosure.DAG): Boolean {
    // check all inequalities
    var sat = true
    for (neq in env.inequalities()) {
        val nodeLeft = dag.termToNode(neq.args[0])
        val nodeRight = dag.termToNode(neq.args[1])
        if (UF.find(nodeLeft) == UF.find(nodeRight)) {
            sat = false
        }
    }
    return sat
}


/**
 * Convert [Expression] (parser model) to [Term] (solver model)
 */
private fun expressionToTerm(exp: Expression): Term {
    when (exp) {
        is Expression.FunApp -> {
            val args = exp.args.map(::expressionToTerm).toList()
            val term = when (exp.identifier.value) {
                "=" -> Term.EqualityFunctionApplication.create(true, args)
                "distinct" -> Term.EqualityFunctionApplication.create(false, args)
                else -> Term.NamedFunctionApplication(env.getFunction(exp.identifier.value), args)
            }
            return term
        }
        is Expression.Identifier -> {
            return Term.NamedFunctionApplication(env.getFunction(exp.value), emptyList())
        }
        else -> throw NotImplementedError("Unsupported expression $exp")
    }
}

private fun findModel(dag: CongruenceClosure.DAG): Model {
    val classes = dag.congruenceClasses()
    val classesWithId = mutableMapOf<Int, MutableSet<Term>>()
    // make an identifier for each congruence class
    for ((id, cls) in classes.withIndex()) {
        classesWithId[id] = cls.toMutableSet()
    }

    // build graph of congruence classes and color it
    val g = GraphColoring.Graph()
    for ((id, _) in classesWithId) {
        g.addNode(id)
    }
    for (neq in env.inequalities()) {
        val left = neq.args[0]
        val right = neq.args[1]
        val leftContainingEntry = classesWithId.filter { (id, cls) -> cls.contains(left) }.toList()
        val rightContainingEntry = classesWithId.filter { (id, cls) -> cls.contains(right) }.toList()
        assert(leftContainingEntry.size == 1) // only one class
        assert(rightContainingEntry.size == 1) // only one class
        val classIdLeft = leftContainingEntry.first().first
        val classIdRight = rightContainingEntry.first().first

        // add edge corresponding to inequality between congruence classes
        g.addEdge(classIdLeft, classIdRight)
    }

    val colors = g.color()

    assert(env.sorts.size == 1) // for now only single sort is supported

    val variables = env.functions.values.filter { f -> f.args.isEmpty() } // variables are 0-ary functions
    val classIdToValuesMap = colors.mapValues { (_, color) -> Model.SortValue(color) }

    val model = Model(classIdToValuesMap.values.toSet())

    // add variables to model
    /*variables.forEach { variable ->
        val containingClass = classesWithId.filter { (id, cls) -> cls.any { term: Term ->
            (term is Term.NamedFunctionApplication) && term.f == variable
        } }
        assert(containingClass.size == 1)
        val classId = containingClass.keys.first()
        val value = classIdToValuesMap.getValue(classId)
        model.addVarValue(variable, emptyList(), value)

        // delete variable from congruence class to simplify model filling
        classesWithId.getValue(classId).removeIf { term -> (term is Term.NamedFunctionApplication) && term.f == variable}
    }*/

    var height = 1 // variables have height of 1
    while (true) {
        val classesBecameEmpty = mutableListOf<Int>()
        for ((id, cls) in classesWithId) {
            val value = classIdToValuesMap.getValue(id)
            val termsToAssignValue =
                cls.filter { term: Term -> dag.heightOfSubGraph(dag.termToExistingNode(term)) == height }.toSet()
            termsToAssignValue.forEach { term: Term ->
                if (term is Term.NamedFunctionApplication) {
                    // add value for term with particular arguments to the model
                    model.addFunApplicationValue(term, value)
                } else {
                    throw IllegalStateException("Unknown term $term")
                }
            }
            // remove processed terms from worklist
            cls.removeAll(termsToAssignValue)
            if (cls.isEmpty()) {
                classesBecameEmpty.add(id)
            }
        }

        // remove classes became empty
        classesBecameEmpty.forEach { id -> classesWithId.remove(id) }

        if (classesWithId.isEmpty()) {
            // nothing left for futher processing
            break
        }

        height++
    }

    if (DEBUG_LOG) {
        println("Model: $model")
    }
    return model
}



