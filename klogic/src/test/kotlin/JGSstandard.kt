@file:Suppress("SpellCheckingInspection")

import JGSBackward.ClosureType
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.logicTo
import utils.JGS.*
import utils.JGS.Closure.Closure
import utils.JGS.Wildcard
import utils.JtypePretty
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption
import utils.Some
import utils.freshTypedVars

class JGSstandard {
    fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    fun checkClassTable(ct: ClassesTable) {
        val nameToId = mutableMapOf<Int, String>()
        for ((typ, id) in ct.classNames) {
            if (nameToId.containsKey(id)) TODO("FUCK")
            else nameToId.put(id, typ.simpleName)
        }
    }

    @Test
    @DisplayName("Class table is well founded")
    fun test0() {
        val ct: ClassesTable = data.first //        for ((k,v) in ct.table.toSortedMap())
        //            println("$k -> $v")
        println("${ct.table[1]} ")
        println("${ct.table[2]} ")
        println("${ct.table[3]} ")
        checkClassTable(ct)
    }

    private val data = prepareGraph(verbose = false)
    private fun prepareGraph(
        verbose: Boolean = false
    ): Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> {
        var ct: ClassesTable = extractClassesTable()
        val directedGraph: DirectedAcyclicGraph<Int, DefaultEdge> = DirectedAcyclicGraph(
            DefaultEdge::class.java
        )

        fun addEdge(from: Int, to: Class_<LogicInt>) {
            val destID = to.id.asReified().n
            if (from == destID)
                return
            directedGraph.addVertex(destID)
            if (verbose) {
                val destName = ct.nameOfId[destID]!!
                println("Add edge $from  -> ${to.id.asReified()} ($destName)")
            }
            directedGraph.addEdge(from, destID)
        }

        fun addEdge(from: Int, to: Interface<LogicInt>) {
            val destID = to.id.asReified().n
            if (from == destID)
                return
            directedGraph.addVertex(destID)
            if (verbose) {
                val destName = ct.nameOfId[destID]!!
                println("Add edge $from  -> ${to.id.asReified()} ($destName)")
            }
            directedGraph.addEdge(from, to.id.asReified().n)
        }
        for ((id, decl) in ct.table) {
            if (verbose) println("WIP: $id    with `$decl`")
            directedGraph.addVertex(id)
            when (decl) {
                is C -> when (decl.superClass) {
                    is Class_ -> addEdge(id, decl.superClass)
                    is Array_ -> println("TODO ${Thread.currentThread().stackTrace[2].lineNumber}")
                    else -> {}
                }

                is I -> for (i in decl.supers.asReified().toList()) {
                    when (i) {
                        is Interface -> addEdge(id, i)
                        else -> {}
                    }
                }
            }
        }
        with(directedGraph) {
            val moreDependencyFirstIterator = TopologicalOrderIterator(
                directedGraph
            ) // Some class are generated withoout information. Possible Bug
            val toRemove: MutableSet<Int> = mutableSetOf()
            moreDependencyFirstIterator.forEachRemaining { id: Int ->
                if (ct.table[id] == null) toRemove.add(id)
            }
            toRemove.forEach { directedGraph.removeVertex(it) }
        }
        println("Graph prepareted")
        println(" Total ${ct.table.size} classes")
        println(" Orphaned types: ${ct.missingTypes} ")
//        println(" nameOfId size =  ${ct.da} ")

        println("Id of 'java.lang.Object' =  ${ct.idOfName["java.lang.Object"]}")
        println(" Object with id=1 is ${ct.table[1]}")
        println(" Object with id=7671 is ${ct.table[7671]}")
        return (ct to directedGraph)
    }

    fun testSingleConstraint(
        expectedResult: (CLASSTABLE) -> Collection<String>, count: Int = 10,
        boundKind: ClosureType = ClosureType.Subtyping,
        bound: (ConvenientCT) -> Term<Jtype<ID>>, verbose: Boolean = false
    ) {
        val classTable = BigCT(data.second, data.first)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q), (when (boundKind) {
                        ClosureType.Subtyping -> JGSBackward.MakeClosure2(closureBuilder)
                            .closure({ a, b, c, d ->
                                v.minus_less_minus(a, b, c, d)
                            }, q, bound(classTable))

                        ClosureType.SuperTyping -> TODO()
                    })
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(count, answers.count())
            val expectedTerm = expectedResult(classTable).toCountMap()
            val pp = JtypePretty{classTable.nameOfId(it)}
            val answers2 = answers.map { pp.ppJtype(it) }
            answers2.run {
                forEachIndexed { i, x -> println("$i : $x") }
            }
            assertEquals(expectedTerm, answers2.toCountMap())
        }
    }

    @Test
    @DisplayName("111")
    fun test1() {
        val ct = data.first
        val moreDependencyFirstIterator = TopologicalOrderIterator(data.second)
        moreDependencyFirstIterator.forEachRemaining { id: Int ->
            assert(ct.table.containsKey(id))
            val dest = ct.table[id]
            println("$id -> $dest")
        }
    }

    @Test
    @DisplayName("Subclasses of Object")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { ct ->
            listOf( //                ct.object_t, Array_(ct.object_t), Array_(Array_(ct.object_t)), Array_(Null) as Jtype<ID>
                "Class java.lang.Object",
                "Array<Class java.lang.Object>",
                "Class NonBaseLocaleDataMetaInfo",
                "Class CLDRLocaleDataMetaInfo",
                "Array<Array<Class java.lang.Object>>",
            )
        }
        testSingleConstraint(
            expectedResult,
            count = 5,
            ClosureType.Subtyping, { it.object_t },
            verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of List<Object>")
    fun test3() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { ct ->
            listOf( //                ct.object_t, Array_(ct.object_t), Array_(Array_(ct.object_t)), Array_(Null) as Jtype<ID>
            )
        }
        //  An operation is not implemented: Not implemented. Asked integer 7685 which is not in the table
        testSingleConstraint(
            expectedResult, count = 4,
            ClosureType.Subtyping, { ct ->
                val humanName = "java.util.AbstractList"
                val listID = ct.idOfName(humanName)!!
                Class_(listID, logicListOf(Type(ct.object_t)))
            },
            verbose = false
        )
    }


    interface ConvenientCT : CLASSTABLE {
        fun idOfName(name: String): ID?
        fun nameOfId(id: Int): String?
    }

    class BigCT : ConvenientCT {
        private var lastId: Int = 0
        private fun newId(): Int {
            lastId++
            return lastId
        }

        private val graph: DirectedAcyclicGraph<Int, DefaultEdge>
        public val data: ClassesTable
        private val topId: Int
        private val objectId: Int
        private val cloneableId: Int
        private val serializableId: Int


        override fun idOfName(name: String): ID? {
            println("idOfName? $name when there are ${data.idOfName.size}")
            data.idOfName.forEach {
                if (it.key.contains("java.util.List"))
                    println(it.key)
            }
            return when (val d = data.idOfName[name]) {
                null -> null
                else -> d.toLogic()
            }
        }

        override fun nameOfId(id: Int): String? {
            return data.nameOfId[id]
        }

        private val top_t: Term<Jtype<ID>>
        override val object_t: Term<Jtype<LogicInt>>
        override val cloneable_t: Term<Jtype<LogicInt>>
        override val serializable_t: Term<Jtype<LogicInt>>

        constructor(g: DirectedAcyclicGraph<Int, DefaultEdge>, ct: ClassesTable) {
            assert(ct.table.isNotEmpty())
            assert(ct.idOfName.isNotEmpty())
            graph = g
            data = ct //            top = Class_<ID>(0.toLogic(), LogicList.logicListOf());
            //            addClass(LogicList.logicListOf(), top, LogicList.logicListOf())
            //            lastId = 0;

            // TODO: add assertions that hardcoded classes correspond to class table
            topId = 0
            top_t = Class_(topId.toLogic(), LogicList.logicListOf())
            objectId = 1
            assert(objectId == 1)
            object_t = Class_(objectId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(objectId))

            cloneableId = 2
            assert(cloneableId == 2)
            cloneable_t = Interface(cloneableId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(cloneableId))

            serializableId = 3
            assert(serializableId == 3)
            serializable_t = Interface(serializableId.toLogic(), LogicList.logicListOf())
            assert(ct.table.containsKey(serializableId))
        }

        context(RelationalContext) override fun new_var(): Term<LogicInt> {
            return newId().toLogic()
        }


        context(RelationalContext)
        override fun decl_by_id(
            v1: Term<LogicInt>,
            rez: Term<Decl<LogicInt>>
        ): Goal {
            //        println("decl_by_id: $v1, $rez")
            return debugVar(v1, { id -> id.reified() }) { it ->
                val v = it.term
                when (v) {
                    is Var<*> -> TODO("not implemented. Got a var")
                    is LogicInt -> if (data.table.containsKey(v.n)) rez `===` data.table.get(v.n)!!
                    else {
                        println("Asking for ${data.table[v.n]}")
                        println("Asking for ${data.table[v.n]}")
                        //TODO("Not implemented. Asked integer ${v.n} which is not in the table")
                        val kind = data.kindOfId[v.n]!!
                        when (kind){
                            is Class_kind ->  rez `===` C(logicListOf(), top_t, logicListOf())
                            is Interface_kind ->
                                rez `===` I(logicListOf(), logicListOf())
//                            failure
                        }

                    }

                    else -> TODO("?")
                }

            }
        }

        context(RelationalContext)
        fun getSuperclassByIdFreeFree(
            subId: Term<LogicInt>,
            subKind: Term<Jtype_kind>,
            superId: Term<LogicInt>,
            superKind: Term<Jtype_kind>,
            rez: Term<Jtype<LogicInt>>
        ): Goal {
            val parents: (Decl<ID>) -> List<Jtype<ID>> = { it ->
                when (it) {
                    is I -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it -> it as Jtype<ID> }

                        is UnboundedValue -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    }

                    is C -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it as Jtype<ID> }

                        is Var -> TODO("")
                        is Wildcard<*> -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    } + when (it.superClass) {
                        is Jtype<ID> -> listOf(it.superClass)

                        is Var -> TODO("")
                        is Wildcard<*> -> TODO("Should not be reachable")
                        else -> TODO("Should not be reachable 100%")
                    }
                }
            }
            return data.table.entries.fold(failure) { acc, entry ->
                val curId = entry.key
                if (curId == objectId) acc
                else {
                    val d: Term<Decl<ID>> = entry.value
                    val entryKind = entry.value.getKind()
                    val parentsList = parents(d as Decl<ID>)

                    parentsList.fold(acc) { acc, jtyp ->
                        when (jtyp) {
                            is Interface -> acc `|||` and(
                                jtyp.id `===` superId,
                                    superKind `===` Interface_kind,
                                    subKind `===` entryKind,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            is Class_ -> acc `|||` and(
                                jtyp.id `===` superId,
                                    superKind `===` Class_kind,
                                    subKind `===` entryKind,
                                curId.toLogic() `===` subId, rez `===` jtyp
                            )

                            else -> TODO("ancestor of the interface should be an interface")
                        }
                    }
                }
            }
        }

        context(RelationalContext) @Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
        override fun get_superclass_by_id(
            subId: Term<LogicInt>,
            subKind: Term<Jtype_kind>,
            superId: Term<LogicInt>,
            superKind: Term<Jtype_kind>,
            rez: Term<LogicOption<Jtype<LogicInt>>>
        ): Goal {

            return debugVar(subId logicTo superId, reifier = { it.reified() }) {
//                println("get_superclass_by_id ${it.term} ~~> $rez\n")
                freshTypedVars { answerJtyp: Term<Jtype<LogicInt>> ->
                    and(
                        rez `===` Some(answerJtyp),
                        getSuperclassByIdFreeFree(subId, subKind, superId, superKind, answerJtyp)
                    )
                }
            }
       }
    }
}
