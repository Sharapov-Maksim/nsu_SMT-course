package smt

import kotlin.enums.EnumEntries

class ModelPrinter {

    companion object {
        const val SORT_VALUE_INFIX = "_VALUE_"

        fun printModel() {
            if (env.logic != Environment.EMPTY_LOGIC) {
                println("(set-logic ${env.logic})")
            }
            env.sorts.forEach { (name, sort) ->
                println("(declare-sort $name ${sort.num})")
            }






            println("(check-sat)")
            println("(get-model)")
        }
    }


}