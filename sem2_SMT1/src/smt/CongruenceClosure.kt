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
         * Converts term to node.
         *
         * @throws IllegalArgumentException if there is no node for such term.
         */
        fun termToExistingNode(t: Term): Node {
            if (t !is Term.NamedFunctionApplication) {
                throw UnsupportedOperationException("Unsupported term $t")
            }
            val n = termToNodeMap[t] ?: throw IllegalArgumentException("No such term in DAG: $t")

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
                val predecessorsU = congruentPredecessors(u)
                val predecessorsV = congruentPredecessors(v)

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
         *
         * Every congruence class has an associated set that contains all
         * nodes that are predecessors to any node in the congruence class.
         */
        fun congruentPredecessors(x: Node): Set<Node> {
            return congruenceClass(x)
                .map(::predecessors)
                .fold<MutableList<Node>, MutableSet<Node>>(mutableSetOf()) { acc, nodes -> acc += nodes; acc }
                .toSet()
        }

        /**
         * Find congruence class of nodes containing node [x].
         */
        fun congruenceClass(x: Node): Set<Node> =
            termToNodeMap.values.filter { node -> UF.find(x) == UF.find(node) }.toSet()
        /**
         * Find congruence class containing node [x].
         */
        fun congruenceClass(t: Term): Set<Term> =
            termToNodeMap.keys.filter { term ->
                UF.find(termToExistingNode(t)) == UF.find(termToExistingNode(term))
            }.toSet()

        fun congruenceClasses(): Set<Set<Term>> {
            val res: MutableSet<Set<Term>> = mutableSetOf()
            termToNodeMap.keys.forEach { t ->
                res.add(congruenceClass(t))
            }
            return res
        }

        /**
         * Find all predecessors of node.
         *
         * TODO Every congruence class has an associated set that contains all
         * nodes that are predecessors to any node in the congruence class.
         *
         * Построить мн-во всех предков всех вершин из класса эквивалентности
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