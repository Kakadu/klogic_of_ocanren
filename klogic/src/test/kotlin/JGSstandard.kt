@file:Suppress("SpellCheckingInspection", "MUST_BE_INITIALIZED_OR_FINAL_OR_ABSTRACT_WARNING")

import JGSBackward.ClosureType
import org.jacodb.api.JcClassOrInterface
import org.jacodb.api.JcClassType
import org.jacodb.api.JcClasspath
import org.jacodb.api.JcTypeVariableDeclaration
import org.jacodb.api.ext.findClass
import org.jacodb.api.ext.findTypeOrNull
import org.jgrapht.graph.DefaultEdge
import org.jgrapht.graph.DirectedAcyclicGraph
import org.jgrapht.traverse.TopologicalOrderIterator
import org.jgs.classtable.ClassesTable
import org.jgs.classtable.TypeSolver
import org.jgs.classtable.extractClassesTable
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.*
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import utils.JGS.*
import utils.JGS.Closure.Closure
import utils.JGS.Wildcard
import utils.JtypePretty
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption
import utils.Some
import utils.freshTypedVars
import kotlin.time.ExperimentalTime
import kotlin.time.TimeSource

class JGSstandard {
    companion object {
        private var data: Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> =
                ClassesTable(mutableMapOf()) to DirectedAcyclicGraph(
                        DefaultEdge::class.java
                )

        @JvmStatic
        @BeforeAll
        fun initClasses() {
            val ct: ClassesTable = extractClassesTable()
            println(" Classes are loaded")
            println("java.util.AbstractList's ID = ${ct.idOfName["java.util.AbstractList"]}")

            data = prepareGraph(ct, verbose = false)
        }

        fun prepareGraph(
                ct: ClassesTable,
                verbose: Boolean = false
        ): Pair<ClassesTable, DirectedAcyclicGraph<Int, DefaultEdge>> {

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
                        is Array_ -> println(
                                "TODO ${Thread.currentThread().stackTrace[2].lineNumber}"
                        )

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
            println("Id of 'java.lang.Iterable' =  ${ct.idOfName["java.lang.Iterable"]}")
            println("Id of 'java.util.List' =  ${ct.idOfName["java.util.List"]}")
            println(" Object with id=1 is ${ct.table[1]}")
            //        println(" Object with id=7671 is ${ct.table[7671]}")
            return (ct to directedGraph)
        }

        fun toJCDBType(x:  Term<Jtype<ID>>, jcClasspath: JcClasspath, nameOfID: (Term<LogicInt>) -> String?): JcClassOrInterface? {
            return when (x) {
                is Class_ ->
                    jcClasspath.findClass(nameOfID(x.id)!!)
                is Interface ->
                    jcClasspath.findClass(nameOfID(x.id)!!)
                else -> TODO("Not implemented")
            }
        }

        @OptIn(ExperimentalTime::class)
        fun solverOfBigCT(classTable: BigCT, classpath: JcClasspath,
                          toJCDBType: (Term<Jtype<ID>>, JcClasspath, (Term<LogicInt>) -> String? ) -> JcClassOrInterface?
                          ): TypeSolver {
            return object: TypeSolver {
                override fun getSuitableTypes(type: JcTypeVariableDeclaration, printTime: Boolean): JcClassOrInterface? {
                    val index = 0 // TODO: Fix this dummy index.
                    val superBound = classTable.data.toJtype(type, index, classpath, 0)
                    val v = Verifier(classTable)
                    val closureBuilder = Closure(classTable)
                    println("superBound = $superBound")

                    withEmptyContext {
                        val g = { q: Term<Jtype<ID>> ->
                            val direct: (v29: (Term<Jtype<LogicInt>>, Term<Jtype<LogicInt>>, Term<LogicBool>) -> Goal, v30: Term<Jtype<LogicInt>>, v31: Term<Jtype<LogicInt>>, v32: Term<LogicBool>) -> (State) -> RecursiveStream<State> =
                                { a, b, c, d ->
                                    v.minus_less_minus(a, b, c, d)
                                }
                            and(
                                only_classes_interfaces_and_arrays(q),
                                JGSBackward.MakeClosure2(closureBuilder)
                                    .closure(direct, superBound, q)
                            )
                        }

                        var answerStartTimeMark =
                            if (printTime) (TimeSource.Monotonic.markNow()) else null
//
                        val elementConsumer: State.() -> Unit =
                            if (printTime) { {
                                val nextMark = TimeSource.Monotonic.markNow()
                                val delta = (nextMark - answerStartTimeMark!!).inWholeMilliseconds
                                answerStartTimeMark = nextMark
                                println("... in $delta ms")
                            }}
                            else { { } }
                        val answers = run(1, g, elementConsumer = elementConsumer).map { p -> p.term }.toList()
                        if (answers.isEmpty()) {
                            println("No answers")
                            return null
                        }

                        val pp = JtypePretty { classTable.nameOfId(it) }
                        val answer2 = pp.ppJtype(answers[0])
                        println(answer2)
                        return toJCDBType(answers[0], classpath) {
                            when (it) {
                                is LogicInt -> classTable.nameOfId(it.n)
                                else -> TODO("Logical unspecified ID")
                            }
                        }
                    }
                }

                override fun getRandomSubclassOf(superClasses: List<JcClassOrInterface>, printTime: Boolean): JcClassOrInterface? {
                    val superBounds = superClasses.map {
                        classTable.data.toJtype(it, classpath, 0)
                    }
                    println("superBounds = $superBounds")
                    val v = Verifier(classTable)
                    val closureBuilder = Closure(classTable)

                    withEmptyContext {
                        val g = { q: Term<Jtype<ID>> ->
                            val direct: (v29: (Term<Jtype<LogicInt>>, Term<Jtype<LogicInt>>, Term<LogicBool>) -> Goal, v30: Term<Jtype<LogicInt>>, v31: Term<Jtype<LogicInt>>, v32: Term<LogicBool>) -> (State) -> RecursiveStream<State> =
                                { a, b, c, d ->
                                    v.minus_less_minus(a, b, c, d)
                                }
                            and(
                                only_classes_interfaces_and_arrays(q),
                                superBounds.fold(success) { acc, bound ->
                                    acc and
                                            JGSBackward.MakeClosure2(closureBuilder)
                                                .closure(direct, bound, q)
                                }
                            )
                        }


                        var answerStartTimeMark =
                            if (printTime) (TimeSource.Monotonic.markNow()) else null
//
                        val elementConsumer: State.() -> Unit =
                            if (printTime) { {
                                val nextMark = TimeSource.Monotonic.markNow()
                                val delta = (nextMark - answerStartTimeMark!!).inWholeMilliseconds
                                answerStartTimeMark = nextMark
                                println("... in $delta ms")
                            }}
                            else { { } }
                        val answers = run(1, g, elementConsumer = elementConsumer).map { p -> p.term }.toList()
                        if (answers.isEmpty())
                            return null
                        val answer = answers[0]

                        val pp = JtypePretty { classTable.nameOfId(it) }
                        val answer2 = pp.ppJtype(answer)
                        println(answer2)
                        return toJCDBType(answer, classpath) {
                            when (it) {
                                is LogicInt -> classTable.nameOfId(it.n)
                                else -> TODO("Logical unspecified ID")
                            }
                        }
                    }
                }

            }
        }
    }

    private fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    private fun checkClassTable(ct: ClassesTable) {
        val nameToId = mutableMapOf<Int, String>()
        for ((typ, id) in ct.classNames) {
            if (nameToId.containsKey(id)) TODO("FUCK")
            else nameToId[id] = typ.simpleName
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


    private fun testSingleConstraint(
            expectedResult: (CLASSTABLE) -> Collection<String>, count: Int = 10,
            boundKind: ClosureType = ClosureType.Subtyping,
            bound: (RelationalContext, ConvenientCT) -> Term<Jtype<ID>>, verbose: Boolean = false
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
                            }, q, bound(this, classTable))

                    ClosureType.SuperTyping -> JGSBackward.MakeClosure2(closureBuilder)
                            .closure({ a, b, c, d ->
                                v.minus_less_minus(a, b, c, d)
                            }, bound(this, classTable), q)
                })
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            val expectedTerm = expectedResult(classTable).toCountMap()
            val pp = JtypePretty { classTable.nameOfId(it) }
            val answers2 = answers.map { pp.ppJtype(it) }
            answers2.run {
                forEachIndexed { i, x -> println("//$i\n\"${x.toString().replace("$", "\\$")}\",") }
            }
            assertEquals(count, answers.count())
            assertEquals(expectedTerm, answers2.toCountMap())
        }
    }
    /*
    fun <T: Term<T>> iterKlogicStream(query: (Term<T>) -> Goal, n: Int, before: (Int) -> Unit, after: (Int) -> Unit)
            : List<ReifiedTerm<T>> {
        val q = freshTypedVar<T>()
        var stream = query(q)(State.empty)
        var i = 0
        val answers = mutableListOf<ReifiedTerm<T>>()
        while (i < n) {
            before(i)
            var rez = stream.msplit() // gives stack overflow somewher
            after(i)
            if (rez == null)
                break
            else {
                i++
                stream = rez.second
                answers.add(rez.first.reify(q))
            }
        }
        return answers
    }

    @OptIn(ExperimentalTime::class)
    fun <T: Term<T>> iterAndMeasure(query: (Term<T>) -> Goal, n: Int)
            : List<Pair< ReifiedTerm<T>, Long>> {

        var updatedTimeMark = TimeSource.Monotonic.markNow()
        val timings = mutableListOf<Long>()
        val answers =
            iterKlogicStream(query, n, before = { updatedTimeMark = TimeSource.Monotonic.markNow() }) {
                timings += ( TimeSource.Monotonic.markNow() - updatedTimeMark).inWholeMilliseconds
            }
        assert(answers.count() == timings.count())
        return answers.zip(timings.reversed()) { l, r -> l to r }
    }
    */

    @Test
    @DisplayName("111 Iterable")
    fun testIntegration1() {
        // TODO: dirty hack
        val classTable = BigCT(data.second, data.first)
        val classpath = data.first.classPath!!
        val solver = solverOfBigCT(classTable, classpath, ::toJCDBType)

        val className1 = "java.lang.Iterable"
        val aList = classpath.findClassOrNull(className1) as JcClassOrInterface
        val answer = solver.getRandomSubclassOf(listOf(aList), printTime = true)
        println("... $answer")
        assert(answer.toString().contains("java.lang.Iterable"))

//        val className2 = "javax.print.attribute.standard.PrinterStateReasons"
//        val printerState = classpath.findClassOrNull(className2) as JcClassOrInterface
//        val answer2 = solver.getRandomSubclassOf(listOf(printerState))
//        println("... $answer2")
//        assert(answer.toString().contains(className2))

    }
    @Test
    @DisplayName("222")
    fun testIntegration2() {
        // TODO: dirty hack
        val classTable = BigCT(data.second, data.first)
        val classpath = data.first.classPath!!
        val solver = solverOfBigCT(classTable, classpath, ::toJCDBType)

        val className1 = "java.lang.Iterable"
        val jcList = classpath.findTypeOrNull<List<*>>() as JcClassType
//        val answer = solver.getRandomSubclassOf(listOf(aList), printTime = true)
        println( jcList.typeParameters.first() )
        val randomConcreteType = solver.getSuitableTypes(jcList.typeParameters.first())
        println("... $randomConcreteType")
        assert(randomConcreteType.toString().contains("java.lang.List"))

//        val className2 = "javax.print.attribute.standard.PrinterStateReasons"
//        val printerState = classpath.findClassOrNull(className2) as JcClassOrInterface
//        val answer2 = solver.getRandomSubclassOf(listOf(printerState))
//        println("... $answer2")
//        assert(answer.toString().contains(className2))

    }

    @OptIn(ExperimentalTime::class)
    private fun testManyConstraints(
            expectedResult: (CLASSTABLE) -> Collection<String>,
            count: Int = 10,
            verbose: Boolean,
            bounds:
            (RelationalContext, ConvenientCT) -> Collection<Pair<ClosureType, Term<Jtype<ID>>>>
    ) {
        val classTable = BigCT(data.second, data.first)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)

        withEmptyContext {
            val (subs, supers) = bounds(this, classTable).partition {
                when (it.first) {
                    ClosureType.Subtyping -> true
                    ClosureType.SuperTyping -> false
                }
            }
            val g = { q: Term<Jtype<ID>> ->
                val direct: (v29: (Term<Jtype<LogicInt>>, Term<Jtype<LogicInt>>, Term<LogicBool>) -> Goal, v30: Term<Jtype<LogicInt>>, v31: Term<Jtype<LogicInt>>, v32: Term<LogicBool>) -> (State) -> RecursiveStream<State> =
                        { a, b, c, d ->
                            v.minus_less_minus(a, b, c, d)
                        }
                and(
                        only_classes_interfaces_and_arrays(q),
                        supers.fold(success) { acc, (_, bound) ->
                            acc and
                                    JGSBackward.MakeClosure2(closureBuilder)
                                            .closure(direct, bound, q)
                        },
                        subs.fold(success) { acc, (_, bound) ->
                            acc and
                                    JGSBackward.MakeClosure2(closureBuilder)
                                            .closure(direct, q, bound)
                        },
                )
            }

            var answerStartTimeMark = TimeSource.Monotonic.markNow()
//
            val elementConsumer: State.() -> Unit = {
                val nextMark = TimeSource.Monotonic.markNow()
                val delta = (nextMark - answerStartTimeMark).inWholeMilliseconds
                answerStartTimeMark = nextMark
                println("... in $delta ms")
            }
            val answers = run(count, g, elementConsumer = elementConsumer).map { p -> p.term }.toList()

//            if (verbose) answers.forEachIndexed { i, x -> println("$i: ${x.toString().replace("$", "\\$")}") }

            val expectedTerm = expectedResult(classTable).toCountMap()
            val pp = JtypePretty { classTable.nameOfId(it) }
            val answers2 = answers.map { pp.ppJtype(it) }
            answers2.run {
                forEachIndexed { i, x -> println("//$i\n\"${x.toString().replace("$", "\\$")}\",") }
            }
            assertEquals(count, answers.count())
            assertEquals(expectedTerm, answers2.toCountMap())
        }
    }

    @Test
    @DisplayName("Graph check")
    fun test1() {
        val ct = data.first
        val moreDependencyFirstIterator = TopologicalOrderIterator(data.second)
        moreDependencyFirstIterator.forEachRemaining { id: Int ->
            check(ct.table.containsKey(id))
            val dest = ct.table[id]
            println("$id -> $dest")
        }
    }

    @Test
    @DisplayName("Subclasses of Object")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class java.lang.Object",
//1
                    "Array<Class java.lang.Object>",
//2
                    "Class sun.util.resources.provider.NonBaseLocaleDataMetaInfo",
//3
                    "Class sun.util.resources.cldr.provider.CLDRLocaleDataMetaInfo",
//4
                    "Class sun.util.resources.ParallelListResourceBundle\$KeySet\$1",
          )
        }
        testSingleConstraint(
                expectedResult,
                count = 5,
                ClosureType.Subtyping, { _, ct -> ct.object_t },
                verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of Pseudo Object")
    fun test21() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
            )
        }
        testSingleConstraint(
            expectedResult,
            count = 5,
            ClosureType.Subtyping, { _, ct ->
                ct.makeTVar(0, ct.object_t)
            },
            verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of Iterable<Object>")
    fun test3() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Interface java.lang.Iterable<Class java.lang.Object>",
//1
                    "Interface javax.xml.crypto.NodeSetData<Class java.lang.Object>",
//2
                    "Interface java.util.Collection<Class java.lang.Object>",
//3
                    "Interface java.nio.file.DirectoryStream<Class java.lang.Object>",
//4
                    "Class java.util.stream.SpinedBuffer\$OfPrimitive<Class java.lang.Object, _.?, _.?>",

                    )
        }

        testSingleConstraint(
                expectedResult, count = 5,
                ClosureType.Subtyping, { _, ct ->
            val humanName = "java.lang.Iterable"
            val listID = ct.idOfName(humanName)!!
            ct.makeInterface(listID, logicListOf(Type(ct.object_t)))
        },
                verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of java.util.AbstractList<Object>")
    fun test4() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class java.util.AbstractList<Class java.lang.Object>",
//1
                    "Class sun.awt.util.IdentityArrayList<Class java.lang.Object>",
//2
                    "Class java.util.Vector<Class java.lang.Object>",
//3
                    "Class java.util.Collections\$SingletonList<Class java.lang.Object>",
//4
                    "Class java.util.Collections\$EmptyList<Class java.lang.Object>",
//5
                    "Class java.util.Collections\$CopiesList<Class java.lang.Object>",
//6
                    "Class java.util.Arrays\$ArrayList<Class java.lang.Object>",
//7
                    "Class java.util.ArrayList\$SubList<Class java.lang.Object>",
//8
                    "Class java.util.ArrayList<Class java.lang.Object>",
//9
                    "Class java.util.AbstractSequentialList<Class java.lang.Object>",
//10
                    "Class java.util.AbstractList\$SubList<Class java.lang.Object>",
//11
                    "Class java.lang.invoke.AbstractConstantGroup\$AsList",
//12
                    "Class com.sun.org.apache.xerces.internal.impl.xs.util.ObjectListImpl",
//13
                    "Class java.util.Stack<Class java.lang.Object>",
//14
                    "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl\$AbstractObjectList",
//15
                    "Class com.sun.org.apache.xerces.internal.impl.dv.xs.ListDV\$ListData",
//16
                    "Class com.sun.jmx.remote.internal.ArrayQueue<Class java.lang.Object>",
//17
                    "Class sun.swing.BakedArrayList<Class java.lang.Object>",
//18
                    "Class jdk.internal.org.objectweb.asm.tree.MethodNode\$1",
//19
                    "Class javax.management.relation.RoleUnresolvedList",
//20
                    "Class sun.awt.util.IdentityLinkedList<Class java.lang.Object>",
//21
                    "Class javax.management.relation.RoleList",
//22
                    "Class java.util.LinkedList<Class java.lang.Object>",
//23
                    "Class javax.management.AttributeList",
//24
                    "Class java.util.AbstractList\$RandomAccessSubList<Class java.lang.Object>",
//25
                    "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl\$3",
//26
                    "Class com.sun.org.apache.xerces.internal.impl.dv.xs.XSSimpleTypeDecl\$2",           )
        }
        // In principle, we can find AbstractSequentialList, ArrayList, Vector
        // but this classes seem not to be in the class table

        val lookup = { ct: BigCT, clas: String ->
            println("\nLooking for $clas in the idOfName")
            ct.data.idOfName.forEach {
                if (it.key.contains(clas)) {
                    println("\t${it.key} ~~> ${it.value}")
                    println("\t\t${ct.data.table[it.value]}")
                }
            }
        }
        testSingleConstraint(
                expectedResult, count = 27,
                ClosureType.Subtyping, { _, ct ->
            val ct2 = ct as BigCT

            val humanName = "java.util.AbstractList"
            val listID = ct.idOfName(humanName)!!
            ct.makeClass(listID, logicListOf(Type(ct.object_t)))
        },
                verbose = false
        )
    }

    @Test
    @DisplayName("Subclasses of Collection<V1>")
    fun test5() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Interface java.util.Collection<_.1.0>",
//1
                    "Class java.util.concurrent.ConcurrentHashMap\$ValuesView<_.1.0, _.?>",
                    )
        }

        testSingleConstraint(
                expectedResult, count = 2,
                ClosureType.Subtyping, { _, ct ->
            val humanName = "java.util.Collection"
            val iterableID = ct.idOfName(humanName)!!

            ct.makeInterface(iterableID, logicListOf(Type(ct.makeTVar(0, ct.object_t))))
        },
                verbose = false
        )
    }

    @Test
    @DisplayName("Super classes of javax.management.AttributeList")
    fun test6() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class javax.management.AttributeList",
//1
                    "Class java.util.ArrayList<Class java.lang.Object>",
//2
                    "Interface java.io.Serializable",
//3
                    "Interface java.lang.Cloneable",
//4
                    "Interface java.util.RandomAccess",
//5
                    "Class java.util.AbstractList<Class java.lang.Object>",
//6
                    "Interface java.util.List<Class java.lang.Object>",
//7
                    "Interface java.util.List<Class java.lang.Object>",
//8
                    "Class java.util.AbstractCollection<Class java.lang.Object>",
//9
                    "Interface java.util.Collection<Class java.lang.Object>",
//10
                    "Interface java.lang.Iterable<Class java.lang.Object>",
//11
                    "Interface java.util.Collection<Class java.lang.Object>",
//12
                    "Class java.lang.Object",
//13
                    "Interface java.util.Collection<Class java.lang.Object>",
//14
                    "Interface java.lang.Iterable<Class java.lang.Object>",
//15
                    "Interface java.lang.Iterable<Class java.lang.Object>",
            )
        }

        testSingleConstraint(
                expectedResult, count = 16,
                ClosureType.SuperTyping, { _, ct ->
            val humanName = "javax.management.AttributeList"
            val ID = ct.idOfName(humanName)!!
            ct.makeClass(ID, logicListOf())
        },
                verbose = false
        )
    }

    @Test
    @DisplayName("Conj of constraints: <= Iterable<V1> && <= Collection<V1> ")
    fun test7() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Interface java.util.Collection<_.1.0>",
//1
                    "Class java.util.concurrent.ConcurrentHashMap\$ValuesView<_.1.0, _.?>",
//2
                    "Interface java.util.Set<_.1.0>",
//3
                    "Class java.util.concurrent.ConcurrentHashMap\$CollectionView<_.1.0, _.?, _.?>",
//4
                    "Interface java.util.Queue<_.1.0>",
//5
                    "Class java.util.Collections\$UnmodifiableCollection<_.1.0>",
//6
                    "Interface java.util.List<_.1.0>",
//7
                    "Class java.util.Collections\$SynchronizedCollection<_.1.0>",
//8
                    "Class java.util.Collections\$CheckedCollection<_.1.0>",
//9
                    "Class java.util.AbstractCollection<_.1.0>",
//10
                    "Class javax.security.auth.Subject\$SecureSet<_.1.0>",
//11
                    "Interface java.util.SortedSet<_.1.0>",
//12
                    "Class java.util.concurrent.ConcurrentHashMap\$KeySetView<_.1.0, _.?>",
//13
                    "Class java.util.LinkedHashSet<_.1.0>",
//14
                    "Class java.util.LinkedHashSet<_.1.0>",
//15
                    "Class java.util.ImmutableCollections\$AbstractImmutableSet<_.1.0>",
//16
                    "Class java.util.LinkedHashSet<_.1.0>",
//17
                    "Class java.util.LinkedHashSet<_.1.0>",
//18
                    "Class java.util.ImmutableCollections\$AbstractImmutableSet<_.1.0>",
//19
                    "Class java.util.HashSet<_.1.0>",
                    )
        }

        testManyConstraints(
                expectedResult, count = 20,
                verbose = false
        ) { _, ct ->
            val iterableID = ct.idOfName("java.lang.Iterable")!!
            val collectionID = ct.idOfName("java.util.Collection")!!
            val v1 = Type(ct.makeTVar(0, ct.object_t))
            listOf(
                    ClosureType.Subtyping to ct.makeInterface(iterableID, logicListOf(v1)),
                    ClosureType.Subtyping to ct.makeInterface(collectionID, logicListOf(v1)),
            )
        }
    }

    @Test
    @DisplayName("Conj of upper and lower bound")
    fun test8() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class javax.management.AttributeList",
//1
                    "Class java.util.ArrayList<Class java.lang.Object>",
//2
                    "Interface java.util.RandomAccess",
            )
        }

        testManyConstraints(
                expectedResult, count = 3,
                verbose = false
        ) { _, ct ->
            val attrListID = ct.idOfName("javax.management.AttributeList")!!
            val randAccID = ct.idOfName("java.util.RandomAccess")!!
            listOf(
                    ClosureType.SuperTyping to ct.makeClass(attrListID, logicListOf()),
                    ClosureType.Subtyping to ct.makeInterface(randAccID, logicListOf()),
            )
        }
    }

    @Test
    @DisplayName("SuperTypes of PrinterStateReasons")
    fun test9() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class javax.print.attribute.standard.PrinterStateReasons",
//1
                    "Interface javax.print.attribute.PrintServiceAttribute",
//2
                    "Class java.util.HashMap<Class javax.print.attribute.standard.PrinterStateReason, Class javax.print.attribute.standard.Severity>",
            )
        }

        testManyConstraints(
                expectedResult, count = 3,
                verbose = false
        ) { _, ct ->
            val printerID = ct.idOfName("javax.print.attribute.standard.PrinterStateReasons")!!
            listOf(
                    ClosureType.SuperTyping to ct.makeClass(printerID, logicListOf()),
            )
        }
    }

    @Test
    @DisplayName("SubTypes of java.util.HashMap<V0, Severity>")
    fun test10() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class java.util.HashMap<_.1.0, Class javax.print.attribute.standard.Severity>",
//1
                    "Class java.util.LinkedHashMap<_.1.0, Class javax.print.attribute.standard.Severity>",
//2
                    "Class sun.security.ssl.X509KeyManagerImpl\$SizedMap<_.1.0, Class javax.print.attribute.standard.Severity>",
            )
        }

        testManyConstraints(
                expectedResult, count = 3,
                verbose = false
        ) { _, ct ->
            val hashMapID = ct.idOfName("java.util.HashMap")!!
            val severityID = ct.idOfName("javax.print.attribute.standard.Severity")!!
            val v0 = ct.makeTVar(0, ct.object_t)
            listOf(
                    ClosureType.Subtyping to
                            ct.makeClass(hashMapID,
                                    logicListOf(Type(v0),
                                            Type(ct.makeClass(severityID, logicListOf())))),
            )
        }
    }


    @Test
    @DisplayName("SubTypes of java.util.HashMap<V0, ? extends Severity>")
    fun test11() {
        val expectedResult: (CLASSTABLE) -> Collection<String> = { _ ->
            listOf(
//0
                    "Class java.util.HashMap<_.1.0, * extends Class javax.print.attribute.standard.Severity>",
//1
                    "Class java.util.LinkedHashMap<_.1.0, * extends Class javax.print.attribute.standard.Severity>",
//2
                    "Class sun.security.ssl.X509KeyManagerImpl\$SizedMap<_.1.0, * extends Class javax.print.attribute.standard.Severity>",
            )
        }

        testManyConstraints(
                expectedResult, count = 3,
                verbose = false
        ) { _, ct ->
            val hashMapID = ct.idOfName("java.util.HashMap")!!
            val severityID = ct.idOfName("javax.print.attribute.standard.Severity")!!
            val v0 = ct.makeTVar(0, ct.object_t)
            val arg2 = ArgWildcardProto(Some(
                    Extends
                    logicTo
                    ct.makeClass(severityID, logicListOf())))
            listOf(
                    ClosureType.Subtyping to
                            ct.makeClass(hashMapID,
                                    logicListOf(Type(v0), arg2)),
            )
        }
    }

    interface ConvenientCT : CLASSTABLE {
        fun idOfName(name: String): Int?
        fun nameOfId(id: Int): String?
        fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID>
        fun makeClass(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>>
        fun makeInterface(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>>
    }

    class BigCT(g: DirectedAcyclicGraph<Int, DefaultEdge>, ct: ClassesTable) : ConvenientCT {
        private var lastId: Int = 0
        private fun newId(): Int {
            lastId++
            return lastId
        }

        private val graph: DirectedAcyclicGraph<Int, DefaultEdge> = g
        val data: ClassesTable = ct
        private val topId: Int = 0
        private val objectId: Int
        private val cloneableId: Int
        private val serializableId: Int

        override fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID> {
            val id = newId()
            return utils.JGS.Var(id.toLogic(), index.toPeanoLogicNumber(), upb, None())
        }

        override fun makeClass(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>> {
            assert(data.table.containsKey(id))
            assert(data.table[id] is C)
            return Class_(id.toLogic(), args)
        }

        override fun makeInterface(id: Int, args: LogicList<Jarg<Jtype<ID>>>): Term<Jtype<ID>> {
            assert(data.table.containsKey(id))
            assert(data.table[id] is I)
            return Interface(id.toLogic(), args)
        }

        override fun idOfName(name: String): Int? {
            return when (val d = data.idOfName[name]) {
                null -> null
                else -> d
            }
        }

        override fun nameOfId(id: Int): String? {
            return data.nameOfId[id]
        }

        private val topT: Term<Jtype<ID>>
        override val object_t: Term<Jtype<ID>>
        override val cloneable_t: Term<Jtype<ID>>
        override val serializable_t: Term<Jtype<ID>>

        // superID -> (subID * subKind * superJtype) list
        private val subClassMap: MutableMap<Int, MutableList<Triple<ID, Jtype_kind, Jtype<ID>>>> = mutableMapOf()

        init {
            check(ct.table.isNotEmpty())
            check(ct.idOfName.isNotEmpty())
            topT = Class_(topId.toLogic(), logicListOf())
            objectId = 1
            check(objectId == 1)
            object_t = Class_(objectId.toLogic(), logicListOf())
            check(ct.table.containsKey(objectId))
            cloneableId = 2
            check(cloneableId == 2)
            cloneable_t = Interface(cloneableId.toLogic(), logicListOf())
            check(ct.table.containsKey(cloneableId))
            serializableId = 3
            check(serializableId == 3)
            serializable_t = Interface(serializableId.toLogic(), logicListOf())
            check(ct.table.containsKey(serializableId))

            for ((typId, decl) in data.table) {
                val pars = parents(decl)
                for (par in pars) {
                    val id0 = when (par) {
                        is Class_ -> par.id
                        is Interface -> par.id
                        else -> TODO("Fuck you, Kotlin")
                    }
                    val id = (id0 as LogicInt).n

                    if (!(subClassMap.containsKey(id)))
                        subClassMap[id] = mutableListOf()
                    subClassMap[id]!!.add(Triple(typId.toLogic(), decl.getKind(), par))
                }
            }
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
            return debugVar(v1, { id -> id.reified() }) {
                when (val v = it.term) {
                    is Var<*> -> TODO("not implemented. Got a var")
                    is LogicInt -> if (data.table.containsKey(v.n)) rez `===` data.table[v.n]!!
                    else {
                        println("Asking for ${data.table[v.n]}")
                        println("Asking for ${data.table[v.n]}")
                        //TODO("Not implemented. Asked integer ${v.n} which is not in the table")
                        val kind = data.kindOfId[v.n]!!
                        when (kind) {
                            is Class_kind -> rez `===` C(logicListOf(), topT, logicListOf())
                            is Interface_kind ->
                                rez `===` I(logicListOf(), logicListOf())
                            //                            failure
                        }

                    }

                    else -> TODO("?")
                }

            }
        }

        private fun parents(it: Decl<ID>): List<Jtype<ID>> =
                when (it) {
                    is I -> when (it.supers) {
                        is LogicList<Jtype<ID>> -> it.supers.toList().map { it as Jtype<ID> }

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

        context(RelationalContext)
        private fun getSuperclassByIdFreeFree(
                subId: Term<LogicInt>,
                subKind: Term<Jtype_kind>,
                superId: Term<LogicInt>,
                superKind: Term<Jtype_kind>,
                rez: Term<Jtype<LogicInt>>
        ): Goal {
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

        sealed class Classify
        data class GroundGround(val subId: Int, val superId: Int) : Classify()
        data class GroundFree(val subId: Int, val superId: Term<ID>) : Classify()
        data class FreeGround(val subId: Term<ID>, val superId: Int) : Classify()
        data class FreeFree(val subId: Term<ID>, val superId: Term<ID>) : Classify()

        private fun classify(subId: Term<ID>, superId: Term<ID>): Classify {
            return when (subId) {
                is Var -> {
                    when (superId) {
                        is Var -> FreeFree(subId, superId)
                        is UnboundedValue -> TODO("")
                        is LogicInt -> FreeGround(subId, superId.n)
                        is CustomTerm -> TODO()
                        else -> TODO("FUCK")
                    }
                }

                is LogicInt ->
                    when (superId) {
                        is Var -> GroundFree(subId.n, superId)
                        is UnboundedValue -> TODO("")
                        is LogicInt -> GroundGround(subId.n, superId.n)
                        is CustomTerm -> TODO()
                        else -> TODO("FUCK")
                    }

                else -> TODO("FUCK")
            }
        }

        private fun <T, R> findFirstMap(xs: Collection<T>, f: (T) -> R?): R? {
            for (x in xs) {
                val foo = f(x);
                if (foo != null)
                    return foo
            }
            return null
        }

        context(RelationalContext)
        override fun get_superclass_by_id(
                subId: Term<LogicInt>,
                subKind: Term<Jtype_kind>,
                superId: Term<LogicInt>,
                superKind: Term<Jtype_kind>,
                rez: Term<LogicOption<Jtype<LogicInt>>>
        ): Goal {

            return debugVar(subId logicTo superId, reifier = { it.reified() }) { it ->
                val u = it.term as LogicPair<LogicInt, LogicInt>
                val subId = u.first
                val superId = u.second
                when (val sortOfGroundness = classify(subId, superId)) {
                    is FreeFree ->
                        freshTypedVars { answerJtyp: Term<Jtype<LogicInt>> ->
                            and(
                                    rez `===` Some(answerJtyp),
                                    getSuperclassByIdFreeFree(sortOfGroundness.subId, subKind, sortOfGroundness.superId, superKind, answerJtyp)
                            )
                        }

                    is GroundFree -> {
                        val curId = sortOfGroundness.subId
                        val decl = data.table[curId]!!
                        val parentsList = parents(decl)

                        parentsList.fold(failure) { acc, jtyp: Jtype<ID> ->
                            val toGoal = { kind: Jtype_kind, jtypID: Term<ID> ->
                                acc `|||` and(
                                        jtypID `===` superId,
                                        superKind `===` kind,
                                        subKind `===` decl.getKind(),
                                        curId.toLogic() `===` subId,
                                        rez `===` Some(jtyp)
                                )
                            }
                            when (jtyp) {
                                is Interface -> toGoal(Interface_kind, jtyp.id)
                                is Class_ -> toGoal(Class_kind, jtyp.id)
                                else -> TODO("ancestor of the interface should be an interface")
                            }
                        }
                    }

                    is FreeGround -> {
                        val info = subClassMap[sortOfGroundness.superId]
                        if (info == null)
                            failure
                        else
                            info.fold(failure) { acc, (newSubId, newKind, superJType) ->
                                acc `|||` and(
                                        subId `===` newSubId,
                                        subKind `===` newKind,
                                        rez `===` Some(superJType)
                                )
                            }
                    }

                    is GroundGround -> {
                        val curId = sortOfGroundness.subId
                        if (data.table[curId] == null)
                            TODO("Table is bad, not value for $curId")
                        val decl = data.table[curId]!!
                        val parentsList = parents(decl)

                        val infoAboutSuper = findFirstMap(parentsList) {
                            when (it) {
                                is Interface -> {
                                    if ((it.id as LogicInt).n == sortOfGroundness.superId)
                                        Interface_kind to it
                                    else null

                                }

                                is Class_ -> {
                                    if ((it.id as LogicInt).n == sortOfGroundness.superId)
                                        Class_kind to it
                                    else null
                                }

                                else -> TODO("The table is full of shit")
                            }
                        }
                        if (infoAboutSuper == null)
                            failure
                        else {
                            and(
                                    superKind `===` infoAboutSuper.first,
                                    subKind `===` decl.getKind(),
                                    rez `===` Some(infoAboutSuper.second)
                            )
                        }
                    }
                }
            }
        }
    }
}
