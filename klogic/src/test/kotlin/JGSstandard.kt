@file:Suppress("SpellCheckingInspection")

import org.jgrapht.Graph
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.EmptyClassTable
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import utils.JGS.*
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import kotlin.system.measureTimeMillis

class JGSstandard {
    @Test
    @DisplayName("asasdf")
    fun test0() {
        var ct: ClassesTable =  extractClassesTable()
//        for ((k,v) in ct.table.toSortedMap())
//            println("$k -> $v")
        println("${ct.table[1]} ")
        println("${ct.table[2]} ")
        println("${ct.table[3]} ")
    }
    @Test
    @DisplayName("111")
    fun test1() {
        var ct : ClassesTable = EmptyClassTable
        println (measureTimeMillis {
            ct = extractClassesTable()
        })
//        println ( ct.table.values.take(10));

        val directedGraph: Graph<LogicInt, DefaultEdge> =
                DirectedAcyclicGraph(DefaultEdge::class.java)

        fun addEdge(from: LogicInt, to: Class_<LogicInt>) {
            if (from == to.id)
                return
            directedGraph.addVertex(to.id.asReified())
//            println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified())
        }
        fun addEdge(from: LogicInt, to: Interface<LogicInt>) {
            if (from == to.id)
                return
            directedGraph.addVertex(to.id.asReified())
//            println("Add edge $from  -> ${to.id.asReified()} (${to.humanName})")
            directedGraph.addEdge(from, to.id.asReified())
        }
        for ( (id, decl) in ct.table) {
            directedGraph.addVertex(id.toLogic())
            when (decl) {
                is C -> when (decl.superClass) {
                    is Class_ -> addEdge(id.toLogic(), decl.superClass)
                    is Array_ -> println("TODO ${Thread.currentThread().stackTrace[2].lineNumber}")
                    else -> {}
                }
                is I ->
                    for (i in decl.supers.asReified().toList()) {
                        when (i) {
                            is Interface -> addEdge(id.toLogic(), i)
                            else -> {}
                        }
                    }
            }
        }
        val moreDependencyFirstIterator = TopologicalOrderIterator(directedGraph)
        moreDependencyFirstIterator.forEachRemaining { task: LogicInt ->
            println("$task -> ${ct.table[task.asReified().n]}")
        }

    }
}
