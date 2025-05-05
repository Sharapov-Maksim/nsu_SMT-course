package smt

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import smt.parser.Expression
import smt.parser.SMTCommand
import smt.parser.SMTModelVisitor
import smt.parser.SMTScript
import smt.parser.gen.SMTLIBv2Lexer
import smt.parser.gen.SMTLIBv2Parser
import smt.theory.Theory
import smt.theory.TheorySolver
import smt.theory.rdl.Variable
import smt.theory.rdl.LEQ_Apply
import smt.theory.rdl.TheorySolverRDL
import smt.theory.uf.Term
import smt.theory.uf.UninterpretedFunction
import java.io.File


const val DEBUG_LOG = true

fun readFileDirectlyAsText(fileName: String): String
        = File(fileName).readText(Charsets.UTF_8)


fun main(args: Array<String>) {
    if (args.isEmpty()) {
        println("Usage: SMT_2_3 <file_path>.smt2")
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
fun rdl() = env.solverRDL()
fun uf() = env.solverUF()
fun ufrdl() = env.solverUFRDL()


private fun interpretScript(script: SMTScript) {

    for (command in script.commands) {
        when (command) {
            is SMTCommand.CmdAssert -> {
                if (command.expression !is Expression.FunApp) {
                    throw UnsupportedOperationException("Unsupported expression ${command.expression}")
                }
                when (classifyExpression(command.expression)) { // 1. UF and RDL fill
                    Theory.RDL -> {
                        val leq = rdl().expressionToFuncApply(command.expression)
                        assert(leq is LEQ_Apply) // only `<=` on upper level of assert expression allowed
                        rdl().addAssert(leq as LEQ_Apply)
                    }
                    Theory.UF -> {
                        val t = uf().expressionToTerm(command.expression)
                        assert(t is Term.EqualityFunctionApplication) // only `=` or `distinct` on upper level of expression allowed
                        uf().addAssert(t as Term.EqualityFunctionApplication)
                    }
                    else -> error("Should not reach here")
                }
            }
            is SMTCommand.CmdCheckSat -> {
                val sat = ufrdl().solve()
                println(if (sat) "; sat" else "; unsat")
            }
            is SMTCommand.CmdDeclareSort -> {
                throw UnsupportedOperationException("DeclareSort is unsupported")
            }
            is SMTCommand.CmdDeclareFun -> {
                if (command.args.isNotEmpty()) {
                    // add uninterpreted function to UF
                    val args = command.args.map { s -> TheorySolverRDL.type(s) }.toList()
                    val res = TheorySolverRDL.type(command.res)
                    uf().addFunction(UninterpretedFunction(command.name, args, res))
                } else {
                    // add variable to both UF and RDL
                    val res = TheorySolverRDL.type(command.res)
                    val variableRDL = Variable(command.name, res)
                    rdl().addVariable(variableRDL)
                    uf().addFunction(UninterpretedFunction(command.name, emptyList(), res))
                    ufrdl().addEqualitiesUF(listOf(variableRDL, variableRDL)) // variable is equal to itself
                }
            }
            is SMTCommand.CmdSetLogic -> {
                when (val logic = command.logic) {
                    /*"QF_RDL" -> {
                        env.createSolverRDL()
                        env.theory = Theory.RDL
                    }
                    "QF_UF" -> {
                        env.createSolverUF()
                        env.theory = Theory.UF
                    }*/
                    "QF_UFRDL" -> {
                        env.createSolverRDL()
                        env.createSolverUF()
                        env.createSolverUFRDL(uf(), rdl())
                        env.theory = Theory.UFRDL
                    }
                    else -> error("Unsupported logic \"$logic\"")
                }
            }
            is SMTCommand.CmdGetModel -> {
                val sat = rdl().solve()
                if (!sat) {
                    println("Could not find model values for unsatisfied model")
                    continue
                }
                val model = rdl().getModel()
                println(TheorySolverRDL.modelToString(model))
                TODO()
            }

            else -> TODO()
        }
    }
}


fun classifyExpression(exp: Expression.FunApp): Theory {
    val res = when (exp.identifier.value) {
        "<=" -> Theory.RDL
        "=" -> Theory.UF
        "distinct" -> Theory.UF
        else -> throw IllegalArgumentException("Could not classify expression $exp")
    }
    return res
}



