import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import parser.SMTCommand
import parser.SMTModelVisitor
import parser.SMTScript
import parser.gen.SMTLIBv2Lexer
import parser.gen.SMTLIBv2Parser
import java.io.File


fun readFileDirectlyAsText(fileName: String): String
        = File(fileName).readText(Charsets.UTF_8)


fun main(args: Array<String>) {

    val file = args[0]

    val content = readFileDirectlyAsText(file)

    val lexer = SMTLIBv2Lexer(CharStreams.fromString(content))
    val tokens = CommonTokenStream(lexer)
    val parser = SMTLIBv2Parser(tokens)
    val parseTree = parser.start().script()
    val visitor = SMTModelVisitor()
    val smtCommands: MutableList<SMTCommand> = visitor.visit(parseTree)
    val script = SMTScript(smtCommands)

    println(smtCommands)

}