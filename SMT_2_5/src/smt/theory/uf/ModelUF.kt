package smt.theory.uf

import smt.theory.Model

data class ModelUF(val values: Set<SortValue>): Model {

    data class SortValue(val value: Int)

    data class FunctionDefinition(val f: UninterpretedFunction) {
        val values = mutableMapOf<List<SortValue>, SortValue>()

        override fun toString(): String {
            return "(Definition of $f: $values)"
        }
    }

    val functionDefinitions = mutableMapOf<UninterpretedFunction, FunctionDefinition>()


    /*fun addVarValue(f: UninterpretedFunction, value: SortValue) {
        assert(f.args.isEmpty())
        if (!functionDefinitions.containsKey(f)) {
            functionDefinitions[f] = FunctionDefinition(f)
        }
        val definition = functionDefinitions.getValue(f)

        // no contradiction assignments allowed
        assert(!definition.values.containsKey(emptyList()) || definition.values.getValue(emptyList()) == value)

        definition.values[emptyList()] = value
    }*/

    fun addFunApplicationValue(application: Term.NamedFunctionApplication, value: SortValue) {
        if (!functionDefinitions.containsKey(application.f)) {
            functionDefinitions[application.f] = FunctionDefinition(application.f)
        }
        val definition = functionDefinitions.getValue(application.f)

        val argsValues = application.args.map { t -> valueOfTerm(t) }
        assert(!definition.values.containsKey(argsValues) || definition.values.getValue(argsValues) == value)
        definition.values[argsValues] = value
    }

    /**
     * Get value of term corresponding to existing function definitions.
     */
    fun valueOfTerm(term: Term): SortValue {
        if (term is Term.NamedFunctionApplication) {
            val definition = functionDefinitions.getValue(term.f)
            val argsValues = term.args.map { t -> valueOfTerm(t) }
            if (!definition.values.containsKey(argsValues)) {
                throw IllegalArgumentException("No value for term $term, definition: $definition")
            }
            return definition.values.getValue(argsValues)
        } else {
            throw IllegalArgumentException("Could not find value for term $term")
        }
    }

    override fun toString(): String {
        return "Model (values = $values, definitions = $functionDefinitions)"
    }

}