package parser

data class SMTScript(val commands: List<SMTCommand>)


open class SMTCommand


class CmdSetLogic(val logic: String) : SMTCommand() {

}

class CmdDeclareSort(val symbol: String, val numeral: Int) : SMTCommand() {

}

