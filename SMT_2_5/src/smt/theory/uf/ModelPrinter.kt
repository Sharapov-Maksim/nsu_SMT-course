package smt.theory.uf

import smt.theory.Sort
import smt.theory.TheorySolver
import smt.uf
import kotlin.enums.EnumEntries

class ModelPrinter {

    companion object {
        const val SORT_VALUE_INFIX = "_VALUE_"

        fun printModel(model: ModelUF) {
            /*if (uf().state.logic != TheorySolver.EMPTY_LOGIC) {
                println("(set-logic ${.logic})")
            }
            env.sorts.forEach { (name, sort) ->
                println("(declare-sort $name ${sort.num})")
            }

            if (model.values.isNotEmpty() && env.sorts.size != 1) {
                throw UnsupportedOperationException("Models with values of multiple (or zero) sorts are unsupported. " +
                        "Sorts: ${env.sorts}")
            }*/

            if (model.values.isEmpty()) {
                assert(model.functionDefinitions.isEmpty())
                // nothing to print, model is empty
                println("(check-sat)")
                println("(get-model)")
                return
            }

            /*val singleSort: Sort =
                env.sorts.values.first()

            val valueNames: Map<ModelUF.SortValue, String> =
                model.values.associateWith { "${singleSort.name}$SORT_VALUE_INFIX${it.value}" }

            // declare values as 0-ary functions
            valueNames.values.forEach { name ->
                println("(declare-fun $name () ${singleSort.name})")
            }

            // all values should be distinct
            for (x in valueNames.values.withIndex()) {
                for (y in valueNames.values.withIndex()) {
                    if (x.value != y.value && x.index <= y.index) {
                        println("(assert (distinct ${x.value} ${y.value}))")
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
                    val sb = StringBuilder()
                    appendValue(sb, definition.values.entries.toList(), valueNames, argNames, 0)
                    res += sb.toString()
                } finally {
                    res += ")"
                }
                println(res)

            }

            println("(check-sat)")
            println("(get-model)")*/
        }

        /**
         * @param index - index of entry
         */
        fun appendValue (
            accumulator: StringBuilder,
            entries: List<Map.Entry<List<ModelUF. SortValue>, ModelUF. SortValue>>,
            valueNames: Map<ModelUF.SortValue, String>,
            argNames: List<String>,
            index: Int) {
            if (index > entries.size) {
                return
            }

            if (index == entries.size) {
                // last else branch, can be any value
                accumulator.append("    " + valueNames.values.first())
                return
            }

            val currentEntry = entries[index]
            val args = currentEntry.key
            val result = currentEntry.value

            if (entries.size == 1) {
                // can avoid using ite and just always use value from this args -> res pair
                accumulator.append("    " + valueNames.getValue(result))
                return
            }

            when (args.size) {
                0 -> {
                    assert(entries.size == 1) // variable
                    accumulator.append("    " + valueNames.getValue(result))
                }
                1 -> {
                    accumulator.append("    (ite ")
                    args.withIndex().forEach { v -> accumulator.append("(= ${argNames[v.index]} ${valueNames.getValue(v.value)}) ") }
                    accumulator.append(valueNames.getValue(result) + "\n")
                    appendValue(accumulator, entries, valueNames, argNames, index + 1)
                    accumulator.append(")")
                }
                else -> {
                    accumulator.append("    (ite (^ ")
                    args.withIndex().forEach { v -> accumulator.append("(= ${argNames[v.index]} ${valueNames.getValue(v.value)}) ") }
                    accumulator.append(") ")
                    accumulator.append(valueNames.getValue(result) + "\n")
                    appendValue(accumulator, entries, valueNames, argNames, index + 1)
                    accumulator.append(")")
                }
            }

        }
    }


}