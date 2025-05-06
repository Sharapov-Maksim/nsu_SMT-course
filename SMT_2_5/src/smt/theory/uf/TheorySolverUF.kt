package smt.theory.uf

import smt.DEBUG_LOG
import smt.parser.Expression
import smt.theory.Model
import smt.theory.TheorySolver.Companion.EMPTY_LOGIC
import smt.theory.Sort
import smt.theory.TheorySolver
import smt.theory.rdl.Variable
import smt.theory.ufrdl.ModelUFRDL

class TheorySolverUF : TheorySolver {

    private val state = State()
    private var dag: CongruenceClosure.DAG? = null

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
        dag = buildDAG()
        val sat = checkSat(dag!!)
        return sat
    }

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }

    fun getModel(assignmentRDL: MutableMap<Variable, Double>): ModelUFRDL {
        state.assertsCongruenceClosure()
        assert(dag != null)
        val model = findModel(dag!!, assignmentRDL)
        return model
    }

    /**
     * Convert [Expression] (parser model) to [Term] (solver model)
     */
    fun expressionToTerm(exp: Expression): Term {
        when (exp) {
            is Expression.FunApp -> {
                val args = exp.args.map(::expressionToTerm).toList()
                val term = when (exp.identifier.value) {
                    "=" -> Term.EqualityFunctionApplication.create(true, args)
                    "distinct" -> Term.EqualityFunctionApplication.create(false, args)
                    else -> Term.NamedFunctionApplication(state.getFunction(exp.identifier.value), args)
                }
                return term
            }
            is Expression.Identifier -> {
                return Term.NamedFunctionApplication(state.getFunction(exp.value), emptyList())
            }
            else -> throw NotImplementedError("Unsupported expression $exp")
        }
    }

    private fun buildDAG(): CongruenceClosure.DAG {
        val dag = CongruenceClosure.DAG.create(state.asserts.toList())
        if (DEBUG_LOG) {
            println("Graph: ${dag.graph}")
        }

        // apply all equalities and propagate functional congruence
        for (eq in state.equalities()) {
            val nodeLeft = dag.termToNode(eq.args[0])
            val nodeRight = dag.termToNode(eq.args[1])
            dag.merge(nodeLeft, nodeRight)
        }
        return dag
    }

    private fun findModel(dag: CongruenceClosure.DAG, assignmentRDL: MutableMap<Variable, Double>): ModelUFRDL {
        val classes = dag.congruenceClasses()
        val classesWithId = mutableMapOf<Int, MutableSet<Term>>()
        // make an identifier for each congruence class
        for ((id, cls) in classes.withIndex()) {
            classesWithId[id] = cls.toMutableSet()
        }

        // build graph of congruence classes and color it
        val g = GraphColoring.Graph()
        for ((id, _) in classesWithId) {
            g.addNode(id)
        }
        for (neq in state.inequalities()) {
            val left = neq.args[0]
            val right = neq.args[1]
            val leftContainingEntry = classesWithId.filter { (id, cls) -> cls.contains(left) }.toList()
            val rightContainingEntry = classesWithId.filter { (id, cls) -> cls.contains(right) }.toList()
            assert(leftContainingEntry.size == 1) // only one class
            assert(rightContainingEntry.size == 1) // only one class
            val classIdLeft = leftContainingEntry.first().first
            val classIdRight = rightContainingEntry.first().first

            // add edge corresponding to inequality between congruence classes
            g.addEdge(classIdLeft, classIdRight)
        }

        val colors = g.color()

        assert(state.sorts.isEmpty()) // sorts are unsupported in UFRDL

        val variables = state.functions.values.filter { f -> f.args.isEmpty() } // variables are 0-ary functions
        var maxPredefined = colors.values.filterIsInstance<GraphColoring.ColorPredefined>()
            .maxOfOrNull { it.value }?: 0.0

        // associate colors with unique Real values
        val colorIdToValue = colors.values.filterIsInstance<GraphColoring.ColorUnique>()
            .map { it.id }.toSet()
            .associateWith { maxPredefined + it + 1.0 }

        val classIdToValuesMap = colors.mapValues { (_, color) ->
            if (color is GraphColoring.ColorPredefined) {
                color.value
            } else if (color is GraphColoring.ColorUnique) {
                colorIdToValue.getValue(color.id)
            } else {
                throw IllegalArgumentException("Invalid color $color")
            }

        }

        val model = ModelUFRDL()

        var height = 1 // variables have height of 1
        while (true) {
            val classesBecameEmpty = mutableListOf<Int>()
            for ((id, cls) in classesWithId) {
                val value = classIdToValuesMap.getValue(id)
                val termsToAssignValue =
                    cls.filter { term: Term -> dag.heightOfSubGraph(dag.termToExistingNode(term)) == height }.toSet()
                termsToAssignValue.forEach { term: Term ->
                    if (term is Term.NamedFunctionApplication) {
                        // add value for term with particular arguments to the model
                        model.addFunApplicationValue(term, value)
                    } else {
                        throw IllegalStateException("Unknown term $term")
                    }
                }
                // remove processed terms from worklist
                cls.removeAll(termsToAssignValue)
                if (cls.isEmpty()) {
                    classesBecameEmpty.add(id)
                }
            }

            // remove classes became empty
            classesBecameEmpty.forEach { id -> classesWithId.remove(id) }

            if (classesWithId.isEmpty()) {
                // nothing left for further processing
                break
            }

            height++
        }

        if (DEBUG_LOG) {
            println("Model: $model")
        }
        return model
    }

    public fun variableEqualityClasses(): Set<Set<Term>> {
        val dag = dag?: throw IllegalStateException("DAG is null")
        val classes = dag.congruenceClasses()
        val varClasses = mutableSetOf<Set<Term>>()

        for (cls in classes) {
            val varClass =
                cls.filter { term: Term -> dag.heightOfSubGraph(dag.termToExistingNode(term)) == 1 } // variables
                    .toSet()
            if (varClass.isNotEmpty()) {
                varClasses += varClass
            }
        }
        return varClasses
    }

    public fun variableInequalityPairs(): Set<Pair<UninterpretedFunction, UninterpretedFunction>> {
        val res: MutableSet<Pair<UninterpretedFunction, UninterpretedFunction>> = mutableSetOf()
        for (neq in inequalities()) {
            val left = neq.args[0] as Term.NamedFunctionApplication
            val right = neq.args[1] as Term.NamedFunctionApplication
            if (left.args.isEmpty() && right.args.isEmpty()) { // variables
                res += (left.f to right.f)
            }
        }

        return res
    }


    private fun checkSat(dag: CongruenceClosure.DAG): Boolean {
        // check all inequalities
        var sat = true
        for (neq in state.inequalities()) {
            val nodeLeft = dag.termToNode(neq.args[0])
            val nodeRight = dag.termToNode(neq.args[1])
            if (CongruenceClosure.UnionFind.find(nodeLeft) == CongruenceClosure.UnionFind.find(nodeRight)) {
                sat = false
            }
        }
        return sat
    }



    fun addAssert(term: Term.EqualityFunctionApplication) {
        state.addAssert(term)
    }


    fun addFunction(function: UninterpretedFunction) {
        state.addFunction(function)
    }

    fun inequalities() = state.inequalities()
    fun assertsCongruenceClosure() {
        state.assertsCongruenceClosure()
    }

    fun getFunction(name: String) = state.getFunction(name)

}