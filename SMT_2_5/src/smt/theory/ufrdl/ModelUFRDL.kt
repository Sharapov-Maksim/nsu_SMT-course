package smt.theory.ufrdl

import smt.theory.Model
import smt.theory.uf.Term
import smt.theory.uf.UninterpretedFunction


class ModelUFRDL: Model {

    data class FunctionDefinition(val f: UninterpretedFunction) {
        val values = mutableMapOf<List<Double>, Double>()

        override fun toString(): String {
            return "(Definition of $f: $values)"
        }
    }

    val functionDefinitions = mutableMapOf<UninterpretedFunction, FunctionDefinition>()


    fun addFunApplicationValue(application: Term.NamedFunctionApplication, value: Double) {
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
    fun valueOfTerm(term: Term): Double {
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
        return "Model ($functionDefinitions)"
    }

}