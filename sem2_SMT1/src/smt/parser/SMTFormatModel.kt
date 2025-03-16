package smt.parser

import smt.parser.gen.SMTLIBv2Parser

data class SMTScript(val commands: List<SMTCommand>)

open class SMTCommand {
    data class CmdAssert(val expression: Expression) : SMTCommand()
    class CmdCheckSat() : SMTCommand()
    data class CmdDeclareSort(val symbol: String, val numeral: Int) : SMTCommand()
    data class CmdDeclareFun(val name: String, val args: List<String>, val res: String) : SMTCommand()
    data class CmdSetLogic(val logic: String) : SMTCommand()

}


open class Expression {
    data class FunApp(val identifier: Identifier, val args: List<Expression>) : Expression()
    data class Identifier(val value: String) : Expression()
}


fun commandConstructor(com: SMTLIBv2Parser.CommandContext): SMTCommand {

    val constructed = when {
        com.cmd_assert() != null -> {
            SMTCommand.CmdAssert(com.term(0).accept(SMTExpressionVisitor()))
        }
        com.cmd_checkSat() != null -> SMTCommand.CmdCheckSat()
        com.cmd_declareFun() != null -> {
            val name = com.symbol(0).text

            val signature = com.sort().map { sortContext -> sortContext.text }.toList()
            val args = signature.subList(0, signature.size - 1)
            val res = signature.last()

            SMTCommand.CmdDeclareFun(name, args, res)
        }
        com.cmd_declareSort() != null -> SMTCommand.CmdDeclareSort(
            com.symbol(0).text,
            com.numeral().Numeral().text.toInt()
        )
        com.cmd_setLogic() != null -> SMTCommand.CmdSetLogic(com.symbol(0).text)
        else -> throw UnsupportedOperationException(com.text)
    }

    return constructed
}

