package smt

import java.util.Objects


class Environment {

    companion object {
        const val EMPTY_LOGIC = ""
    }

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


data class Sort(val name: String, val num: Int) {

    override fun toString(): String {
        return "Sort($name)"
    }
}

data class UninterpretedFunction(val name: String, val args: List<Sort>, val result: Sort) {
    override fun toString(): String {
        return "Function (\"$name\" $args -> $result)"
    }
}

open class Term {

    open class FunctionApplication(open val args: List<Term>): Term() {
        override fun equals(other: Any?): Boolean {
            if (other !is FunctionApplication) {
                return false
            }
            return args == other.args
        }

        override fun hashCode(): Int {
            return Objects.hash(args)
        }
    }

    class NamedFunctionApplication(
        val f: UninterpretedFunction,
        override val args: List<Term>): FunctionApplication(args) {

        override fun equals(other: Any?): Boolean {
            if (other !is NamedFunctionApplication) {
                return false
            }
            if (this.f != other.f) {
                return false
            }
            return super.equals(other)
        }

        override fun hashCode(): Int {
            return Objects.hash(f, super.hashCode())
        }

    }

    class EqualityFunctionApplication private constructor(val isEqual: Boolean, override val args: List<Term>): FunctionApplication(args) {

        override fun equals(other: Any?): Boolean {
            if (!(other is EqualityFunctionApplication)) {
                return false
            }
            if (this.isEqual != other.isEqual) {
                return false
            }
            return super.equals(other)
        }

        override fun hashCode(): Int {
            return Objects.hash(isEqual, super.hashCode())
        }

        companion object {
            fun create(isEqual: Boolean, args: List<Term>): EqualityFunctionApplication {
                if (args.size != 2) {
                    throw IllegalArgumentException("Wrong ${ if (isEqual) "equality" else "inequality" } args $args")
                }
                return EqualityFunctionApplication(isEqual, args)
            }
        }
    }


}




