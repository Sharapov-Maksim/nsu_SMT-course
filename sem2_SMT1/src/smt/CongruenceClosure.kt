package smt

import smt.CongruenceClosure.UnionFind.Companion as UF

class CongruenceClosure {



    companion object {


    }


    class DAG {

        /**
         * The graph itself represented as set of nodes.
         */
        val graph: MutableSet<Node> = mutableSetOf()

        /**
         * Mapping from term to node, used for deduplication of nodes.
         */
        val termToNodeMap: MutableMap<Term, Node> = mutableMapOf()


        data class Node(val label: UninterpretedFunction, val edges: List<Node>) {
            var parent: Node = this // base state of Union-Find algorithm
        }


        fun addNode(n: Node) {
            graph.add(n) // add current node
            n.edges.forEach(::addNode) // add all connected nodes
        }

        /**
         * Converts term to node.
         * Also registers this node, so for any fixed [DAG] and any equal terms resulting node will be the **same**.
         *
         * Note: node deduplication is required for correctness of [UnionFind] algorithm since node
         * has [Node.parent] field.
         */
        fun termToNode(t: Term): Node {
            if (t !is Term.NamedFunctionApplication) {
                throw UnsupportedOperationException("Unsupported term $t")
            }
            val edges = t.args.map(::termToNode).toList()
            val n = termToNodeMap.getOrPut(t) { Node(t.f, edges) }

            return n
        }

        /**
         * Determine if two nodes represent congruent subterms.
         */
        fun congruent(u: Node, v: Node): Boolean {
            if ((u.label != v.label) || (u.edges.size != v.edges.size)) {
                return false
            }
            for (i in 0 ..< u.edges.size) {
                if (UF.find(u.edges[i]) != UF.find(v.edges[i])) {
                    return false
                }
            }
            return true
        }

        /**
         * Merge uses the Union operation and additionally propagates functional congruence.
         */
        fun merge(u: Node, v: Node): Unit {
            if (UF.find(u) != UF.find(v)) {
                val predecessorsU = predecessors(u)
                val predecessorsV = predecessors(v)

                UF.union(u, v)

                for (x in predecessorsU) {
                    for (y in predecessorsV) {
                        if (UF.find(x) != UF.find(y) && congruent(x, y)) {
                            merge(x, y)
                        }
                    }
                }
            }

        }

        /**
         * Find all congruent predecessors of node.
         */
        fun predecessors(x: Node): MutableList<Node> {
            val direct = directPredecessors(x) // find direct predecessors of node
            val allPredecessors = direct.toMutableList()

            // recursively find predecessors of direct predecessors
            // add them to the end of list
            direct.forEach { dirPred -> allPredecessors += predecessors(dirPred) }
            return allPredecessors
        }

        /**
         * Find all direct predecessors of node [x] e.g. nodes with some edge that points to [x].
         */
        fun directPredecessors(x: Node): List<Node> =
            termToNodeMap.values.filter { node -> node.edges.contains(x) }.toList()


        companion object {
            fun create(assertions: List<Term.EqualityFunctionApplication>): DAG {
                val dag = DAG()

                // convert left and right parts of (in)equalities to DAG nodes, and add them
                assertions.forEach { asrt: Term.EqualityFunctionApplication ->
                    asrt.args.map { x -> dag.termToNode(x) }.forEach { n -> dag.addNode(n) }
                }
                return dag
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