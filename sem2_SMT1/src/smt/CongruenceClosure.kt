package smt

class CongruenceClosure {



    companion object {


    }


    class DAG {

        val graph: MutableSet<Node> = mutableSetOf()


        data class Node(val label: UninterpretedFunction, val edges: List<Node>) {
            var parent: Node = this // base state of Union-Find algorithm
        }


        fun addNode(n: Node) {
            graph.add(n) // add current node
            n.edges.forEach(::addNode) // add all connected nodes
        }


        companion object {
            fun create(assertions: List<Term.EqualityFunctionApplication>): DAG {
                val dag = DAG()

                // convert left and right parts of (in)equalities to DAG nodes, and add them
                assertions.forEach { asrt: Term.EqualityFunctionApplication ->
                    asrt.args.map(::termToNode).forEach { n -> dag.addNode(n) }
                }
                return dag
            }

            private fun termToNode(t: Term): Node {
                if (t !is Term.NamedFunctionApplication) {
                    throw UnsupportedOperationException("Unsupported term $t")
                }
                val edges = t.args.map(::termToNode).toList()
                val n = Node(t.f, edges)

                return n
            }
        }

    }

    /**
     * Implementation of Union-Find algorithm
     */
    class UnionFind {
        companion object {
            fun find(node: DAG.Node): DAG.Node = if (node.parent == node) node else find(node.parent)

            fun union(x: DAG.Node, y: DAG.Node) {
                find(y).parent = find(x) // works even if x ~ y already
            }
        }
    }


}