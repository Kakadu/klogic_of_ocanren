import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.core.Var
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicBool.Companion.toLogicBool
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.*
import utils.JGS.*
import utils.JGS.Wildcard
import utils.LogicInt.Companion.toLogic
import utils.freshTypedVars

typealias ID = LogicInt

interface MutableClassTable : CLASSTABLE {
    fun addClass(c: C<ID>): Int
    fun addClass(
        params: Term<LogicList<Jtype<ID>>>,
        superClass: Term<Jtype<ID>>,
        supers: Term<LogicList<Jtype<ID>>>,
    ): Int

    fun addInterface(c: I<ID>): Int
    fun addInterface(params: Term<LogicList<Jtype<ID>>>, supers: Term<LogicList<Jtype<ID>>>): Int

    fun makeTVar(id: Int, upb: Term<Jtype<ID>>): Jtype<ID>
}

class DefaultCT : MutableClassTable {
    private var lastId: Int = 0
    fun newId(): Int {
        lastId++;
        return lastId;
    }

    private val data: MutableMap<Int, Decl<ID>> = mutableMapOf()
    private val objectId: Int
    private val cloneableId: Int
    private val serializableId: Int
    private val top: Term<Jtype<ID>>?

    override val object_t: Term<Jtype<LogicInt>>
    override val cloneable_t: Term<Jtype<LogicInt>>
    override val serializable_t: Term<Jtype<LogicInt>>

    override fun addClass(c: C<ID>): Int {
        data[newId()] = c
        return lastId
    }

    override fun addClass(
        params: Term<LogicList<Jtype<ID>>>,
        superClass: Term<Jtype<ID>>,
        supers: Term<LogicList<Jtype<ID>>>,
    ): Int {
        data[newId()] = C(params, superClass, supers)
        return lastId
    }

    override fun addInterface(c: I<ID>): Int {
        data[newId()] = c
        return lastId
    }

    override fun addInterface(
        params: Term<LogicList<Jtype<ID>>>,
        supers: Term<LogicList<Jtype<ID>>>
    ): Int {
        data[newId()] = I(params, supers)
        return lastId

    }

    override fun makeTVar(index: Int, upb: Term<Jtype<ID>>): Jtype<ID> {
        val id = newId()
        return utils.JGS.Var(id.toLogic(), index.toPeanoLogicNumber(), upb, None())
    }


    constructor() {
        top = Class_<ID>(0.toLogic(), logicListOf());
        addClass(logicListOf(), top, logicListOf())
        lastId = 0;
        objectId = addClass(C(logicListOf(), top, logicListOf()))
        assert(objectId == 1)
        object_t = Class_(objectId.toLogic(), logicListOf())
        cloneableId = addInterface(logicListOf(), logicListOf())
        assert(cloneableId == 2)
        cloneable_t = Interface(cloneableId.toLogic(), logicListOf())
        serializableId = addInterface(logicListOf(), logicListOf())
        assert(serializableId == 3)
        serializable_t = Interface(serializableId.toLogic(), logicListOf())
    }

    context(RelationalContext) override fun new_var(): Term<LogicInt> {
        return newId().toLogic()
    }

    context(RelationalContext)
    override fun decl_by_id(v1: Term<LogicInt>, rez: Term<Decl<LogicInt>>): Goal {
//        println("decl_by_id: $v1, $rez")
        return debugVar(v1, { id -> id.reified() }) { it ->
            val v = it.term
            when (v) {
                is Var<*> -> TODO("not implemented")
                is LogicInt -> rez `===` (data[v.n] as Term<Decl<LogicInt>>)
                else -> TODO("?")
            }

        }
    }

    context(RelationalContext)
    fun getSuperclassByIdFreeFree(
        subId: Term<LogicInt>, superId: Term<LogicInt>,
        rez: Term<Jtype<LogicInt>>
    ): Goal {
        val parents: (Decl<ID>) -> List<Jtype<ID>> = { it ->
            when (it) {
                is I -> when (it.supers) {
                    is LogicList<Jtype<ID>> -> it.supers.toList().map { it -> it as Jtype<ID> }

                    is org.klogic.core.Var -> TODO("")
                    is Wildcard<*> -> TODO("Should not be reachable")
                    else -> TODO("Should not be reachable 100%")
                }
//                is I -> when (it.supers) {
//                    is CustomTerm<LogicList<Jtype<ID>>> -> it.supers.asReified().toList().map { it -> it as Jtype<ID> }
//                    is org.klogic.core.UnboundedValue<*> -> TODO("")
//
//                }
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
        return data.entries.fold(failure) { acc, entry ->
            val curId = entry.key
            if (curId == objectId) acc
            else {
                val d: Term<Decl<ID>> = entry.value
                val parentsList = parents(d as Decl<ID>)


                parentsList.fold(acc) { acc, jtyp ->
                    when (jtyp) {
                        is Interface -> acc `|||` and(
                            jtyp.id `===` superId,
                            curId.toLogic() `===` subId, rez `===` jtyp
                        )

                        is Class_ -> acc `|||` and(
                            jtyp.id `===` superId,
                            curId.toLogic() `===` subId, rez `===` jtyp
                        )

                        else -> TODO("ancestor of the interface should be an interface")
                    }
                }
            }
        }
    }

    context(RelationalContext) override fun get_superclass_by_id(
        subId: Term<LogicInt>,
        superId: Term<LogicInt>,
        rez: Term<LogicOption<Jtype<LogicInt>>>
    ): Goal {
        println("get_superclass_by_id $subId $superId ~~> $rez\n")
        return freshTypedVars { answerJtyp: Term<Jtype<LogicInt>> ->
            and(rez `===` Some(answerJtyp), getSuperclassByIdFreeFree(subId, superId, answerJtyp))
        }
    }
}



data class NotComplete(val v: VERIFIER) {
    context(RelationalContext)
    fun smallFish(
        ta: Term<Jtype<LogicInt>>, tb: Term<Jtype<LogicInt>>,
        rez: Term<LogicBool>
    ): Goal = this.check(ta, tb, rez)

    context(RelationalContext)
    fun check(ta: Term<Jtype<LogicInt>>, tb: Term<Jtype<LogicInt>>, rez: Term<LogicBool>): Goal {
        return v.minus_less_minus(
            { a, b, c -> smallFish(a, b, c) }, ta, tb, rez
        )
    }
}

class JGSTest {
    @AfterEach
    fun clear() {
        //        UnificationsController.onFinish()
    }

    private val unificationsTracer = UnificationListener { firstTerm, secondTerm, stateBefore, stateAfter ->
        //if (System.getenv("SILENT_UNIFICATIONS") == null)
        val rez = if (stateAfter == null) " ~~> _|_"
        else ""
        println(
            "${firstTerm.walk(stateBefore.substitution)} `===` ${
                secondTerm.walk(stateBefore.substitution)
            }$rez"
        )
    }

    fun testForward(
        a: (MutableClassTable) -> Term<Jtype<ID>>,
        b: (MutableClassTable) -> Term<Jtype<ID>>,
        init: (MutableClassTable) -> Unit = { }, rez: Boolean,
        verbose: Boolean = false
    ) {
        val classtable = DefaultCT()
        init(classtable)
        val v = Verifier(classtable)

        withEmptyContext {
            if (verbose) addUnificationListener(unificationsTracer)
            val g: (Term<LogicBool>) -> Goal = {
                NotComplete(v).check(a(classtable), b(classtable), it)
            }

            val answers = run(2, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(1, answers.count())
            val expectedTerm = rez.toLogicBool()
            assertEquals(expectedTerm, answers[0])
        }
    }

    @Test
    @DisplayName("Object[] <: Object")
    fun test1() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        testForward(a, b, rez = true)
        // false because NotComplete can't calculate this.
    }

    @Test
    @DisplayName("Object[][] <: Object")
    fun test15() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(Array_(classtable.object_t)) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[] <: Clonable")
    fun test2() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        testForward(a, b, rez = true)
    }

    @Test
    @DisplayName("Object[] <: Serializable")
    fun test3() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        testForward(a, b, rez = true)
    }

    @Test
    @DisplayName("Object[] :> Object is FALSE")
    fun test4() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.object_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[] :> Clonable is FALSE")
    fun test5() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.cloneable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[] :> Serializable is FALSE")
    fun test6() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> classtable.serializable_t }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        testForward(a, b, rez = false)
    }

    @Test
    @DisplayName("Object[][] <: Serializable[]")
    fun test7() {
        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable ->
            Array_(Array_(classtable.object_t))
        }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.serializable_t) }
        testForward(a, b, rez = true, verbose = false)
    }

    @Test
    @DisplayName("B <: A")
    fun test8() {
        var a: Term<Jtype<ID>>? = null
        var b: Term<Jtype<ID>>? = null
        // TODO(Kakadu): this null-related stuff is bad. rewrite.
        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val aId = ct.addClass(logicListOf(), ct.object_t, logicListOf())
            a = Class_(aId.toLogic(), logicListOf())
            val bId = ct.addClass(logicListOf(), a!!, logicListOf())
            b = Class_(bId.toLogic(), logicListOf())
        }
        testForward({ b!! }, { a!! }, init, rez = true, verbose = false)
    }

    @Test
    @DisplayName("C <: IA")
    fun test9() {
        var ia: Term<Jtype<ID>>? = null
        var c: Term<Jtype<ID>>? = null
        // TODO(Kakadu): this null-related stuff is bad. rewrite.
        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val iaId = ct.addInterface(logicListOf(), logicListOf())
            ia = Interface(iaId.toLogic(), logicListOf())
            val cId = ct.addClass(logicListOf(), ct.object_t, logicListOf(ia!!))
            c = Class_(cId.toLogic(), logicListOf())
        }
        testForward({ c!! }, { ia!! }, init, rez = true, verbose = false)
    }

    @Test
    @DisplayName("F<A, B> <: E<D<B>")
    fun test12() {
        var a: Term<Jtype<ID>>?
        var b: Term<Jtype<ID>>?
        var left: Term<Jtype<ID>>? = null
        var right: Term<Jtype<ID>>? = null
        // TODO(Kakadu): this null-related stuff is bad. rewrite.
        val init: (MutableClassTable) -> Unit = { ct: MutableClassTable ->
            val aId = ct.addClass(logicListOf(), ct.object_t, logicListOf())
            a = Class_(aId.toLogic(), logicListOf())
            val bId = ct.addClass(logicListOf(), a!!, logicListOf())
            b = Class_(bId.toLogic(), logicListOf())

            val dId = ct.addClass(params = logicListOf(ct.object_t), ct.object_t, logicListOf())

            val eId = ct.addClass(logicListOf(ct.object_t, ct.object_t), ct.object_t, logicListOf())

            val fId = ct.addClass(
                logicListOf(ct.object_t, ct.object_t),
                Class_(
                    eId.toLogic(),
                    logicListOf(
                        Type(
                            Class_(
                                dId.toLogic(),
                                logicListOf(Type(ct.makeTVar(1, ct.object_t)))
                            )
                        ),
                        Type(ct.makeTVar(0, ct.object_t))
                    )
                ),
                logicListOf()
            )
            left = Class_(
                fId.toLogic(),
                logicListOf(
                    Type(a!!), Type(b!!)
                )
            )
            right = Class_(
                eId.toLogic(),
                logicListOf(
                    Type(
                        Class_(
                            dId.toLogic(),
                            logicListOf(Type(Class_(bId.toLogic(), logicListOf())))
                        )
                    ),
                    Type(a!!)
                )
            )

        }
        testForward({ left!! }, { right!! }, init, rez = true, verbose = false)
    }
}
