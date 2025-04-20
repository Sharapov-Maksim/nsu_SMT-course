package smt.theory.rdl

import smt.Environment
import smt.env

class ModelPrinter {

    companion object {

        fun printModel() {
//            if (env.logic != Environment.EMPTY_LOGIC) {
//                println("(set-logic ${env.logic})")
//            }
//            env.sorts.forEach { (name, sort) ->
//                println("(declare-sort $name ${sort.num})")
//            }






            println("(check-sat)")
            println("(get-model)")
        }
    }


}