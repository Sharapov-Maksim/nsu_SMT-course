package smt.theory.rdl

import smt.DEBUG_LOG
import smt.parser.Expression
import smt.theory.Real
import smt.theory.TypeRDL
import smt.theory.Void

class TheorySolverRDL {

    private val state = State()
    var graph: ConstraintGraph? = null

    class State {

        val variables: MutableMap<String, Variable> = mutableMapOf()
        val asserts: MutableSet<LEQ_Apply> = mutableSetOf()

    }

    class ConstraintGraph() {
        companion object {
            val rootVariable = Variable("ROOT", Void)
        }

        /**
         * Graph represented as set of nodes (organized as a map).
         */
        val nodes: MutableMap<Variable, Node> = mutableMapOf()


        init { // add root node at graph creation
            nodes[rootVariable] = Node(rootVariable)
        }

        private val rootNode = nodes.getValue(rootVariable)


        data class Node(val variable: Variable) {
            val edges: MutableSet<Edge> = mutableSetOf()
        }

        /**
         * Edge of oriented graph with weight
         */
        data class Edge(val from: Node, val to: Node, val w: Double)


        fun addNode(variable: Variable) {
            nodes.computeIfAbsent(variable) {
                val newNode = Node(variable)
                // add edge from root node with zero weight
                rootNode.edges.add(Edge(rootNode, newNode, 0.0))
                newNode
            }
        }

        fun addEdge(from: Variable, to: Variable, weight: Double) {
            val left = nodes.getOrPut(from) { Node(from) }
            val right = nodes.getOrPut(to) { Node(from) }
            left.edges.add(Edge(left, right, weight))
        }

    }

    fun solve() {

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
            println("RDL graph constructed: ${graph.nodes.values}")
        }

        this.graph = graph
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
    }





}