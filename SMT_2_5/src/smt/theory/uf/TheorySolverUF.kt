package smt.theory.uf

import smt.DEBUG_LOG
import smt.env
import smt.theory.Model
import smt.theory.TheorySolver.Companion.EMPTY_LOGIC
import smt.theory.Sort
import smt.theory.TheorySolver

class TheorySolverUF : TheorySolver {

    class State {
        val sorts: MutableMap<String, Sort> = mutableMapOf()
        val functions: MutableMap<String, UninterpretedFunction> = mutableMapOf()

        val asserts: MutableSet<Term.EqualityFunctionApplication> = mutableSetOf()

        var logic: String = EMPTY_LOGIC

        fun equalities() = asserts.filter { x -> x.isEqual }
        fun inequalities() = asserts.filter { x -> !x.isEqual }

        fun addSort(sort: Sort) {
            if(sorts.containsKey(sort.name)) {
                throw IllegalArgumentException("Sort $sort was already added")
            }
            sorts[sort.name] = sort
        }

        fun getSort(name: String): Sort =
            sorts.getOrElse(name) { throw IllegalArgumentException("Unknown sort $name") }


        fun addFunction(function: UninterpretedFunction) {
            if(functions.containsKey(function.name)) {
                throw IllegalArgumentException("Function $function was already added")
            }
            functions[function.name] = function
        }

        fun getFunction(name: String): UninterpretedFunction =
            functions.getOrElse(name) { throw IllegalArgumentException("Unknown function $name") }


        fun addAssert(term: Term.EqualityFunctionApplication) {
            if (asserts.contains(term)) {
                throw IllegalArgumentException("Term $term was already added")
            }
            asserts.add(term)
        }

        // fix for inequalities problem
        fun assertsCongruenceClosure() {
            while (true) {
                val inequalities = inequalities()
                val sizePrevious = inequalities.size
                for (ineq in inequalities) {
                    val left = ineq.args[0]
                    val right = ineq.args[1]
                    if ((left as Term.NamedFunctionApplication).f == (right as Term.NamedFunctionApplication).f) {
                        if (left.args.size == 1) {
                            asserts.add(
                                Term.EqualityFunctionApplication.create(
                                    false,
                                    listOf(left.args.first(), right.args.first())
                                )
                            )
                        }
                    }
                }
                if (inequalities().size == sizePrevious) {
                    // nothing added
                    break
                }
            }
        }


    }


    override fun solve(): Boolean {
        TODO("Not yet implemented")
    }

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }

    private fun buildDAG(): CongruenceClosure.DAG {
        val dag = CongruenceClosure.DAG.create(env.asserts.toList())
        if (DEBUG_LOG) {
            println("Graph: ${dag.graph}")
        }

        // apply all equalities and propagate functional congruence
        for (eq in env.equalities()) {
            val nodeLeft = dag.termToNode(eq.args[0])
            val nodeRight = dag.termToNode(eq.args[1])
            dag.merge(nodeLeft, nodeRight)
        }
        return dag
    }

}