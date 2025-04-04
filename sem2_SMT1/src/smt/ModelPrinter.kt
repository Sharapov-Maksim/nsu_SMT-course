package smt

import kotlin.enums.EnumEntries

class ModelPrinter {

    companion object {
        const val SORT_VALUE_INFIX = "_VALUE_"

        fun printModel(model: Model) {
            if (env.logic != Environment.EMPTY_LOGIC) {
                println("(set-logic ${env.logic})")
            }
            env.sorts.forEach { (name, sort) ->
                println("(declare-sort $name ${sort.num})")
            }

            if (model.values.isNotEmpty() && env.sorts.size != 1) {
                throw UnsupportedOperationException("Models with values of multiple (or zero) sorts are unsupported. " +
                        "Sorts: ${env.sorts}")
            }

            if (model.values.isEmpty()) {
                assert(model.functionDefinitions.isEmpty())
                // nothing to print, model is empty
                println("(check-sat)")
                println("(get-model)")
                return
            }

            val singleSort: Sort = env.sorts.values.first()

            val valueNames: Map<Model.SortValue, String> =
                model.values.associateWith { "${singleSort.name}$SORT_VALUE_INFIX${it.value}" }

            // declare values as 0-ary functions
            valueNames.values.forEach { name ->
                println("(declare-fun $name () ${singleSort.name})")
            }

            // all values should be distinct
            for (x in valueNames.values) {
                for (y in valueNames.values) {
                    if (x != y) {
                        println("(assert (distinct $x $y))")
                    }
                }
            }

            // function definitions
            model.functionDefinitions.forEach { func, definition ->
                var res = "(define-fun ${func.name} (" // start of signature
                try {
                    val args = func.args
                    val argNames = args.withIndex().map { "x${it.index}" }
                    argNames.forEach { argName ->
                        res += "($argName ${singleSort.name})" // arguments
                    }
                    res += ") ${func.result.name}\n" // end of signature

                    definition.values.forEach { argValues, resultValue ->
                        when (argValues.size) {
                            0 -> {
                                assert(definition.values.size == 1) // variable
                                res += valueNames.getValue(resultValue)
                            }
                            1 -> {
                                res += "    (ite "
                                argValues.withIndex().forEach { v -> res += "(= ${argNames[v.index]} ${valueNames.getValue(v.value)}" }
                                res += ")"
                            }
                            else -> {
                                res += "    (ite (^ "
                                argValues.withIndex().forEach { v -> res += "(= ${argNames[v.index]} ${valueNames.getValue(v.value)}" }
                                res += "))"
                            }
                        }

                    }

                } finally {
                    res += ")"
                }


            }
        }

        fun appendValue (accumulator: String,
                         entries: List<Map.Entry<List<Model. SortValue>, Model. SortValue>>,
                         valueNames: Map<Model.SortValue, String>,
                         argNames: List<String>) {}
    }


}