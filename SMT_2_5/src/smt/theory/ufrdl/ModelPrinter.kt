package smt.theory.ufrdl

import smt.theory.Real
import smt.theory.Sort
import smt.theory.TheorySolver
import smt.uf
import kotlin.enums.EnumEntries

class ModelPrinter {

    companion object {
        fun printModel(model: ModelUFRDL) {
            println("(set-logic QF_UFRDL)")


            if (model.functionDefinitions.isEmpty()) {
                // nothing to print, model is empty
                println("(check-sat)")
                println("(get-model)")
                return
            }

            val allValues: Set<Double> =
                model.functionDefinitions.values.map { it.values.values }.flatten().toMutableSet() +
                model.functionDefinitions.values.map { it.values.keys.flatten() }.flatten().toMutableSet()

            // function definitions
            model.functionDefinitions.forEach { func, definition ->
                var res = "(define-fun ${func.name} (" // start of signature
                try {
                    val args = func.args
                    val argNames = args.withIndex().map { "arg${it.index}" }
                    argNames.forEach { argName ->
                        res += "($argName $Real)" // arguments
                    }
                    res += ") ${Real}\n" // end of signature
                    val sb = StringBuilder()
                    appendValue(sb, definition.values.entries.toList(), allValues, argNames, 0)
                    res += sb.toString()
                } finally {
                    res += ")"
                }
                println(res)

            }

            println("(check-sat)")
            println("(get-model)")
        }

        /**
         * @param index - index of entry
         */
        fun appendValue (
            accumulator: StringBuilder,
            entries: List<Map.Entry<List<Double>, Double>>,
            allValues: Set<Double>,
            argNames: List<String>,
            index: Int) {
            if (index > entries.size) {
                return
            }

            if (index == entries.size) {
                // last else branch, can be any value
                accumulator.append("    " + allValues.first())
                return
            }

            val currentEntry = entries[index]
            val args = currentEntry.key
            val result = currentEntry.value

            if (entries.size == 1) {
                // can avoid using ite and just always use value from this args -> res pair
                accumulator.append("    $result")
                return
            }

            when (args.size) {
                0 -> {
                    assert(entries.size == 1) // variable
                    accumulator.append("    $result")
                }
                1 -> {
                    accumulator.append("    (ite ")
                    args.withIndex().forEach { v -> accumulator.append("(= ${argNames[v.index]} ${v.value}) ") }
                    accumulator.append("$result\n")
                    appendValue(accumulator, entries, allValues, argNames, index + 1)
                    accumulator.append(")")
                }
                else -> {
                    accumulator.append("    (ite (^ ")
                    args.withIndex().forEach { v -> accumulator.append("(= ${argNames[v.index]} ${v.value}) ") }
                    accumulator.append(") ")
                    accumulator.append("$result\n")
                    appendValue(accumulator, entries, allValues, argNames, index + 1)
                    accumulator.append(")")
                }
            }

        }
    }


}