package smt.theory.rdl

import smt.DEBUG_LOG
import smt.parser.Expression
import smt.theory.*

class TheorySolverRDL : TheorySolver {

    private val state = State()
    var graph: ConstraintGraph? = null
    var searchResult: ConstraintGraph.SingleSourceShortestPath.SearchResult? = null

    class State {

        val variables: MutableMap<String, Variable> = mutableMapOf()
        val asserts: MutableSet<LEQ_Apply> = mutableSetOf()

    }

    open class ConstraintGraph() {
        companion object {
            val rootVariable = Variable("ROOT", Void)
        }

        /**
         * Nodes contained in graph.
         */
        val nodes: MutableMap<Variable, Node> = mutableMapOf()
        /**
         * Edges contained in graph.
         */
        open val edges: MutableSet<Edge> = mutableSetOf()

        class InducedGraph(baseGraph: ConstraintGraph): ConstraintGraph() {

            

        }

        init { // add root node at graph creation
            nodes[rootVariable] = Node(rootVariable)
        }

        private val rootNode = nodes.getValue(rootVariable)


        data class Node(public val variable: Variable) {
            val edges: MutableSet<Edge> = mutableSetOf()

            override fun toString(): String {
                return "Node ${variable.name} ($edges)"
            }
        }

        /**
         * Edge of oriented graph with weight
         */
        data class Edge(val from: Node, val to: Node, val w: Double) {
            override fun toString(): String {
                return "${from.variable.name} --($w)-> ${to.variable.name}"
            }
        }


        fun addNode(variable: Variable) {
            nodes.computeIfAbsent(variable) {
                val newNode = Node(variable)
                newNode
            }
            // add edge from root node with zero weight
            addEdge(rootVariable, variable, 0.0)
        }

        fun addEdge(from: Variable, to: Variable, weight: Double) {
            val left = nodes.getOrPut(from) { Node(from) }
            val right = nodes.getOrPut(to) { Node(from) }
            val e = Edge(left, right, weight)
            left.edges.add(e)
            edges.add(e)
        }

        fun searchShortestPathsFromRoot(): SingleSourceShortestPath.SearchResult {
            return SingleSourceShortestPath(this).search(rootNode)
        }

        class SingleSourceShortestPath(private val graph: ConstraintGraph) {

            data class SearchResult(val d: Map<Node, Double>, val hasNegativeCycle: Boolean)

            /**
             * Calculate distances to all nodes from [source] node.
             */
            fun search(source: Node): SearchResult {
                val d: MutableMap<Node, Double> = mutableMapOf()
                /*if (d.isNotEmpty()) {
                    d = mutableMapOf()
                }*/
                for (v in graph.nodes.values) {
                    d[v] = Double.MAX_VALUE;
                }
                d[source] = 0.0

                for (i in 0 ..< graph.nodes.size - 1) {
                    optimizeDistances(d)
                }

                // if there is no negative cycle in graph, optimization could not change anything
                val hasNegativeCycle = optimizeDistances(d)

                return SearchResult(d, hasNegativeCycle)
            }

            /**
             * Cycle of distances optimization in Bellman–Ford algorithm.
             *
             * @return true if at least one of distances decreased.
             */
            private fun optimizeDistances(d: MutableMap<Node, Double>): Boolean {
                var changed = false
                for (e in graph.edges) {
                    val w = e.from
                    val v = e.to
                    val weight = e.w
                    if (d[v]!! > (d[w]!! + weight)) {
                        d[v] = d[w]!! + weight
                        changed = true
                    }
                }
                return changed
            }

        }

    }

    override fun solve(): Boolean {
        val graph = ConstraintGraph()

        // add all variables as nodes
        for (v in state.variables.values) {
            graph.addNode(v)
        }

        // add edges from asserts
        for (leq in state.asserts) {
            val sub = leq.left as Sub_Apply
            val const = leq.right as Constant
            val x = sub.left as VariableApply
            val y = sub.right as VariableApply
            graph.addEdge(x.variableDefinition, y.variableDefinition, const.value)
        }

        if (DEBUG_LOG) {
            println("[Info] RDL graph constructed: ${graph.nodes.values}")
        }

        val searchResult = graph.searchShortestPathsFromRoot()

        if (DEBUG_LOG) {
            println("[Info] Search result: $searchResult")
        }

        val sat = !searchResult.hasNegativeCycle

        this.graph = graph
        this.searchResult = searchResult

        return sat
    }

    /**
     * Get model for theory. Theory should be already solved by [solve].
     */
    override fun getModel(): ModelRDL {
        assert(this.searchResult != null)
        val searchResult = this.searchResult!!
        assert(!searchResult.hasNegativeCycle)
        val d = searchResult.d.mapKeys { (node, _) -> node.variable }
        val assignment: MutableMap<Variable, Double> = mutableMapOf()

        state.variables.values.forEach {variable: Variable ->
            val variableValue: Double
            if (d.getValue(variable) == 0.0) {
                variableValue = 0.0
            } else {
                variableValue = -1 * d.getValue(variable)
            }
            assignment[variable] = variableValue
        }
        return ModelRDL(assignment)
    }

    class EqGen(val delta: Map<ConstraintGraph.Node, Double>, val graph: ConstraintGraph) {

        fun findEqualVariables() {
            val edgesWithZeroSlack = graph.edges.filter { sl(it) == 0.0 } // E'


        }

        /**
         * Slack function.
         */
        private fun sl(u: ConstraintGraph.Node, v: ConstraintGraph.Node): Double =
            delta.getValue(u) - delta.getValue(v) + edge(u, v).w

        private fun sl(edge: ConstraintGraph.Edge) = sl(edge.from, edge.to)

        private fun edge(u: ConstraintGraph.Node, v: ConstraintGraph.Node) =
            u.edges.filter { e -> e.from == u && e.to == v }[0]

    }


    fun addVariable(variable: Variable) {
        state.variables[variable.name] = variable
    }

    fun addAssert(function: LEQ_Apply) {
        state.asserts.add(function)
    }

    /**
     * Convert [Expression] (parser model) to [ExpressionReal] (RDL solver model)
     */
    fun expressionToFuncApply(exp: Expression): ExpressionReal {
        when (exp) {
            is Expression.FunApp -> {
                val args = exp.args.map(::expressionToFuncApply).toList()
                val application = when (val identifier = exp.identifier.value) {
                    "<=" -> {
                        assert(args.size == 2)
                        LEQ_Apply(args[0], args[1])
                    }
                    "-" -> {
                        assert(args.size == 2)
                        Sub_Apply(args[0], args[1])
                    }
                    else -> {
                        if (args.isNotEmpty()) {
                            throw UnsupportedOperationException("Named functions with arguments are not supported in RDL")
                        }
                        // it is variable in format `x()`
                        if (!state.variables.containsKey(identifier)) {
                            throw IllegalStateException("Unknown variable \"$identifier\"")
                        }
                        VariableApply(state.variables.getValue(identifier))
                    }
                }
                return application
            }
            is Expression.Identifier -> {
                val identifier = exp.value
                if (!state.variables.containsKey(identifier)) {
                    throw IllegalStateException("Unknown variable \"$identifier\"")
                }
                return VariableApply(state.variables.getValue(identifier))
            }
            is Expression.DecimalConstant -> return Constant(exp.value)
            else -> throw NotImplementedError("Unsupported expression $exp")
        }
    }

    companion object {
        fun type(name: String): TypeRDL {
            when(name) {
                "Real" -> return Real
                else -> throw IllegalArgumentException("Unknown RDL type $name")
            }
        }

        fun modelToString(model: ModelRDL): String {
            var result = "(set-logic QF_RDL)\n"
            model.variableValues.forEach { (variable, value) ->
                result += "(define-fun ${variable.name} () ${variable.result}\n"
                result += "    $value)\n"
            }
            result += "(check-sat)\n"
            result += "(get-model)\n"
            return result
        }

    }





}