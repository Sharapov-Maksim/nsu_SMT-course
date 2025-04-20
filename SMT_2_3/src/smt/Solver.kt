package smt

import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import smt.parser.SMTCommand
import smt.parser.SMTModelVisitor
import smt.parser.SMTScript
import smt.parser.gen.SMTLIBv2Lexer
import smt.parser.gen.SMTLIBv2Parser
import smt.theory.rdl.Variable
import smt.theory.rdl.LEQ_Apply
import smt.theory.rdl.TheorySolverRDL
import java.io.File


const val DEBUG_LOG = false

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


private fun interpretScript(script: SMTScript) {

    for (command in script.commands) {
        when (command) {
            is SMTCommand.CmdAssert -> {
                val leq = env.solverRDL().expressionToFuncApply(command.expression)
                assert(leq is LEQ_Apply) // only `<=` on upper level of assert expression allowed
                rdl().addAssert(leq as LEQ_Apply)
            }
            is SMTCommand.CmdCheckSat -> {
                val sat = rdl().solve()
                println(if (sat) "; sat" else "; unsat")
            }
            is SMTCommand.CmdDeclareSort -> {
                throw UnsupportedOperationException("DeclareSort is unsupported")
            }
            is SMTCommand.CmdDeclareFun -> {
                if (command.args.isNotEmpty()) {
                    throw UnsupportedOperationException("Non-variable declarations are not supported. " +
                            "Wrong declaration: $command")
                }
                val res = TheorySolverRDL.type(command.res)
                env.solverRDL().addVariable(Variable(command.name, res))
            }
            is SMTCommand.CmdSetLogic -> {
                val logic = command.logic
                if (logic != "QF_RDL") {
                    error("Unsupported logic \"$logic\"")
                }
                env.createSolverRDL()
            }
            is SMTCommand.CmdGetModel -> {
                val sat = rdl().solve()
                if (!sat) {
                    println("Could not find model values for unsatisfied model")
                    continue
                }
                val model = rdl().getModel()
                println(TheorySolverRDL.modelToString(model))
            }

            else -> TODO()
        }
    }
}




