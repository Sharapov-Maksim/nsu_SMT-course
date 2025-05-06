package smt.theory.rdl

import smt.DEBUG_LOG
import smt.env
import smt.parser.Expression
import smt.theory.*
import smt.theory.rdl.TheorySolverRDL.ConstraintGraph.Edge
import smt.theory.rdl.TheorySolverRDL.ConstraintGraph.Node

class TheorySolverRDL : TheorySolver {

    private val state = State()
    var graph: ConstraintGraph? = null
    var inducedGraph: ConstraintGraph.InducedGraph? = null
    var searchResult: ConstraintGraph.SingleSourceShortestPath.SearchResult? = null

    class State {

        val variables: MutableMap<String, Variable> = mutableMapOf()
        val asserts: MutableSet<LEQ_Apply> = mutableSetOf()

    }

    open class ConstraintGraph() {
        companion object {
            val rootVariable = Variable("ROOT", Void)

            fun edge(u: Node, v: Node) =
                u.edges.filter { e -> e.from == u && e.to == v }[0]
        }

        /**
         * Nodes contained in graph.
         */
        private val nodes: MutableMap<Variable, Node> = mutableMapOf()
        /**
         * Edges contained in graph.
         */
        private val edges: MutableSet<Edge> = mutableSetOf()

        init { // add root node at graph creation
            nodes[rootVariable] = Node(rootVariable)
        }

        open fun edgesFrom(n: Node): Set<Edge> = n.edges
        open fun nodes() = nodes
        open fun edges() = edges

        /**
         * Graph induced by subset of edges.
         */
        class InducedGraph private constructor(val baseGraph: ConstraintGraph, val edgesInduced: Set<Edge>): ConstraintGraph() {

            companion object {
                fun create(baseGraph: ConstraintGraph, edgesInduced: Set<Edge>): InducedGraph {
                    if (!baseGraph.edges().containsAll(edgesInduced)) {
                        throw IllegalArgumentException("Wrong edges subset, $edgesInduced is not subset of ${baseGraph.edges()}")
                    }
                    return InducedGraph(baseGraph, edgesInduced)
                }
            }

            /**
             * Returns outgoing edges contained in induced set of edges.
             */
            override fun edgesFrom(n: Node): Set<Edge> {
                return baseGraph.edgesFrom(n).filter { edgesInduced.contains(it) }.toSet()
            }

            override fun nodes(): MutableMap<Variable, Node> = baseGraph.nodes()
            override fun edges(): MutableSet<Edge> = baseGraph.edges()

        }

        /**
         * Graph with inverted edges.
         *
         * @see SCC
         */
        class InvertedGraph(val baseGraph: ConstraintGraph): ConstraintGraph() {
            private val edgesInverted = baseGraph.edges().map { e -> Edge(e.to, e.from, e.w) }.toSet()

            override fun nodes(): MutableMap<Variable, Node> = baseGraph.nodes()
            override fun edges(): MutableSet<Edge> = baseGraph.edges()

            override fun edgesFrom(n: Node): Set<Edge> {
                return edgesInverted.filter { it.from == n }.toSet()
            }
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
                for (v in graph.nodes().values) {
                    d[v] = Double.MAX_VALUE;
                }
                d[source] = 0.0

                for (i in 0 ..< graph.nodes().size - 1) {
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
                for (e in graph.edges()) {
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

        /**
         * Strong connected components finder.
         *
         * http://e-maxx.ru/algo/strong_connected_components
         */
        class SCC {
            companion object {
                /**
                 * Search SCCs from [graph].
                 * @return mapping of node to SCC index.
                 */
                fun search(graph: ConstraintGraph): Map<Node, Int> {
                    val graphInverted = InvertedGraph(graph)
                    val ord = ArrayDeque<Node>() // order in which DFS1 finishes traversal
                    val visited = mutableSetOf<Node>()

                    for (node in graph.nodes().values) {
                        dfsWithOrder(graph, node, visited, ord)
                    }

                    val components: MutableMap<Node, Int> = mutableMapOf()
                    var sccIdx = 0
                    var node = ord.removeLastOrNull()
                    while (node != null)  {
                        if (!components.containsKey(node)) {
                            dfsMarkComponents(graphInverted, node, components, sccIdx)
                            sccIdx++
                        }
                        node = ord.removeLastOrNull()
                    }

                    return components
                }

                private fun dfsWithOrder(graph: ConstraintGraph, start: Node, visited: MutableSet<Node>, ord: ArrayDeque<Node>) {
                    if(visited.contains(start)) {
                        return
                    }
                    visited += start
                    for (edge in graph.edgesFrom(start)) {
                        if (!visited.contains(edge.to)) {
                            dfsWithOrder(graph, edge.to, visited, ord)
                        }
                    }
                    ord.addLast(start)
                }

                private fun dfsMarkComponents(graph: ConstraintGraph, start: Node, components: MutableMap<Node, Int>, compIdx: Int) {
                    assert(!components.containsKey(start))
                    components[start] = compIdx

                    for (edge in graph.edgesFrom(start)) {
                        if (!components.containsKey(edge.to)) {
                            dfsMarkComponents(graph, edge.to, components, compIdx)
                        }
                    }
                }

            }
        }

        class SCCGraph() {

            public val nodes: MutableMap<Int, SCCNode> = mutableMapOf()
            public val edges: MutableSet<SCCEdge> = mutableSetOf()

            data class SCCNode(val component: Set<Node>, val id: Int) {
                val edges: MutableSet<SCCEdge> = mutableSetOf()

                override fun toString(): String {
                    return "SCC#${id} (${component.map { it.variable.name }.toList()}) ($edges)"
                }
            }

            data class SCCEdge(val from: SCCNode, val to: SCCNode) {
                override fun toString(): String {
                    return "#${from.id} ---> #${to.id}"
                }
            }

            fun addNode(component: Set<Node>, id: Int) {
                assert(!nodes.containsKey(id))
                nodes[id] = SCCNode(component, id)
            }

            fun addEdge(from: SCCNode, to: SCCNode) {
                val edge = SCCEdge(from, to)
                edges.add(edge)
                from.edges.add(edge)
            }

            override fun toString(): String {
                return "SCCGraph(${nodes.values})"
            }

            fun topsort(): ArrayDeque<SCCNode> {
                val result = ArrayDeque<SCCNode>()
                val notVisited = nodes.values.toMutableSet()

                fun visit(n: SCCNode) {
                    assert(notVisited.remove(n))

                    for (next in n.edges.map { it.to }) {
                        if (notVisited.contains(next)) {
                            visit(next)
                        }
                    }
                    result.addFirst(n)
                }

                while (notVisited.isNotEmpty()) {
                    val start = notVisited.first()

                    visit(start)
                }

                return result
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
            println("[Info] RDL graph constructed: ${graph.nodes().values}")
        }

        val searchResult = graph.searchShortestPathsFromRoot()

        if (DEBUG_LOG) {
            println("[Info] Search result: $searchResult")
        }

        val sat = !searchResult.hasNegativeCycle

        this.graph = graph
        this.searchResult = searchResult
        if (sat) {
            inducedGraph = EqGen(searchResult.d, graph).inducedGraph()
        }

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

    fun getEqualVariables(): Set<Set<Variable>> {
        assert(this.searchResult != null)
        assert(this.graph != null)
        val searchResult = this.searchResult!!
        assert(!searchResult.hasNegativeCycle)
        return EqGen(searchResult.d, graph!!).findEqualVariables()
    }

    class EqGen(val delta: Map<Node, Double>, val graph: ConstraintGraph) {
        /**
         * Equality Generation for Difference Constraints
         */
        fun findEqualVariables(): Set<Set<Variable>> {
            val inducedSubgraph = inducedGraph() // (i) (ii) G'
            val componentsRaw = ConstraintGraph.SCC.search(inducedSubgraph) // (iii) SCCs

            // (iv) group by {x in SCC and delta(x)==d}
            val components = componentsRaw.keys.groupBy { componentsRaw.getValue(it) }
            val variableEqualities: MutableSet<Set<Variable>> = mutableSetOf()
            for ((_, comp) in components) {
                val groupsWithEqualDelta = mutableListOf<List<Node>>()
                val groups = comp.groupBy { delta.getValue(it) } // group of nodes in same SCC with equal delta
                // (v) generate equalities
                for (g in groups.values) {
                    if (g.size >= 2) {
                        variableEqualities += g.map { node -> node.variable }.toSet()
                    }
                }
            }

            return variableEqualities
        }

        public fun inducedGraph(): ConstraintGraph.InducedGraph {
            val edgesWithZeroSlack = graph.edges().filter { env.solverRDL().sl(it) == 0.0 }.toSet() // (i) E'
            val inducedSubgraph = ConstraintGraph.InducedGraph.create(graph, edgesWithZeroSlack) // (ii) G'
            return inducedSubgraph
        }



    }

    /**
     * Slack function.
     */
    public fun sl(u: Node, v: Node): Double {
        assert(!searchResult!!.hasNegativeCycle)
        val delta = searchResult!!.d
        return delta.getValue(u) - delta.getValue(v) + ConstraintGraph.edge(u, v).w
    }
    fun sl(edge: Edge) = sl(edge.from, edge.to)

    fun addVariable(variable: Variable) {
        state.variables[variable.name] = variable
    }

    fun variables() = state.variables.toMap()

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