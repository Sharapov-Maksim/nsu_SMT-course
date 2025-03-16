package smt


open class Sort(val name: String, val num: Int) {

    class Void() : Sort("Void", -1)

}

open class UninterpretedFunction(val name: String, open val args: List<Sort>, val result: Sort) {

    class Equal(override val args: List<Sort>) : UninterpretedFunction(name = "=", args = args, result = Sort.Void())
    class Distinct(override val args: List<Sort>) : UninterpretedFunction(name = "distinct", args = args, result = Sort.Void())

}

open class Term {


    open class FunctionApplication(f: UninterpretedFunction, val args: List<Term>)

    //open class Equality() : FunctionApplication()

}


class Environment {


    val sorts: MutableMap<String, Sort> = mutableMapOf()
    val functions: MutableMap<String, UninterpretedFunction> = mutableMapOf()

    //val equalities = mutableSetOf()

    fun addSort(sort: Sort) {
        assert(sorts.containsKey(sort.name))
        sorts[sort.name] = sort
    }

    fun getSort(name: String): Sort =
        sorts.getOrElse(name) { throw IllegalArgumentException("Unknown sort $name") }


    fun addFunction(function: UninterpretedFunction) {
        assert(functions.containsKey(function.name))
        functions[function.name] = function
    }


}


