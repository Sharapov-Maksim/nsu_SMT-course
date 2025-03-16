import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import parser.SMTCommand
import parser.SMTModelVisitor
import parser.SMTScript
import parser.gen.SMTLIBv2Lexer
import parser.gen.SMTLIBv2Parser
import smt.Environment
import smt.Sort
import smt.UninterpretedFunction
import java.io.File


val DEBUG_LOG = true

fun readFileDirectlyAsText(fileName: String): String
        = File(fileName).readText(Charsets.UTF_8)


fun main(args: Array<String>) {
    if (args.isEmpty()) {
        println("Usage: SolverKt <smt2_file_path>")
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



            }
            is SMTCommand.CmdCheckSat -> TODO()
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

        }
    }
}
