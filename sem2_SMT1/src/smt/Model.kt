package smt

class Model(val values: Set<SortValue>) {

    data class SortValue(val value: Int)

    class FunctionDefinition(val f: UninterpretedFunction) {
        val values = mutableMapOf<List<SortValue>, SortValue>()
    }


    val functionDefinitions = mutableMapOf<UninterpretedFunction, FunctionDefinition>()


    fun addVarValue(f: UninterpretedFunction, value: SortValue) {
        assert(f.args.isEmpty())
        if (!functionDefinitions.containsKey(f)) {
            functionDefinitions[f] = FunctionDefinition(f)
        }
        val definition = functionDefinitions.getValue(f)

        // no contradiction assignments allowed
        assert(!definition.values.containsKey(emptyList()) || definition.values.getValue(emptyList()) == value)
    }

}