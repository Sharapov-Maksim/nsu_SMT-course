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


const val DEBUG_LOG = true

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
            }
            is SMTCommand.CmdGetModel -> {
                val dag = buildDAG()
                val sat = checkSat(dag)
                if (!sat) {
                    println("Could not find model values for unsatisfied model")
                    continue
                }
                val classes = dag.congruenceClasses()
                assert(false)
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

