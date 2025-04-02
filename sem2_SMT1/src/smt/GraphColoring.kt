package smt

class GraphColoring {

    companion object {
        const val COLOR_UNKNOWN = -1
        const val COLOR_FIRST = 0
    }

    class Graph {

        /**
         * The graph itself represented as map from node id to node.
         */
        private val nodes: MutableMap<Int, Node> = mutableMapOf()

        data class Node(val id: Int, val edges: MutableSet<Node>) {
            var color: Int = COLOR_UNKNOWN
        }

        fun addNode(id: Int) {
            assert(!nodes.containsKey(id)) // check that no node with given id exists in graph
            nodes[id] = Node(id, mutableSetOf())
        }

        fun addEdge(id0: Int, id1: Int) {
            assert(nodes.containsKey(id0))
            assert(nodes.containsKey(id1))
            nodes.getValue(id0).edges.add(nodes.getValue(id1))
            nodes.getValue(id1).edges.add(nodes.getValue(id0))
        }

        /**
         * Colors graph and returns coloring in map(id -> color)
         */
        fun color(): Map<Int, Int> {
            for (colorsCount in 1..nodes.size) {
                if (colorSubgraph(0, colorsCount-1)) {
                    // graph is successfully colored
                    return nodes.mapValues { (id, node) -> node.color }.toMap()
                }
            }
            throw IllegalStateException("Could not find a coloring for graph $nodes")
        }

        private fun colorSubgraph(currentId: Int, maximalColor: Int): Boolean {
            if (currentId >= nodes.size) {
                return true
            }

            for (c in COLOR_FIRST..maximalColor) {
                if (isSafeToColor(currentId, c)) {
                    val node = nodes.getValue(currentId)
                    node.color = c
                    if (colorSubgraph(currentId + 1, maximalColor)) {
                        return true
                    }
                    node.color = COLOR_UNKNOWN // backtrack
                }
            }
            return false
        }

        private fun isSafeToColor(nodeId: Int, color: Int): Boolean =
            !nodes.getValue(nodeId).edges.map { n -> n.color }.toSet().contains(color)

    }



}