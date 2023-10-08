import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.RelationalContext
//import org.klogic.core.*
import org.klogic.core.Term
import org.klogic.core.UnificationListener
import org.klogic.core.reified
import org.klogic.core.Goal
import org.klogic.core.Var
import org.klogic.core.debugVar
import org.klogic.core.failure
import org.klogic.core.`|||`
import org.klogic.core.and
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicBool.Companion.toLogicBool
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.toPeanoLogicNumber
import utils.*
import utils.JGS.*
import utils.JGS.Wildcard
import utils.LogicInt.Companion.toLogic

class JGSBackward {
    @AfterEach
    fun clear() {
        //        UnificationsController.onFinish()
    }

    private val unificationsTracer = UnificationListener { firstTerm, secondTerm, stateBefore, stateAfter ->
        //if (System.getenv("SILENT_UNIFICATIONS") == null)
        val rez = if (stateAfter == null) " ~~> _|_"
        else ""
        println("${firstTerm.walk(stateBefore.substitution)} `===` ${
            secondTerm.walk(stateBefore.substitution)
        }$rez")
    }

    internal fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    fun test(super_: (MutableClassTable) -> Term<Jtype<ID>>,
             init: (MutableClassTable) -> Unit = { }, rez: Collection<Jtype<ID>>,
             count: Int = 10,
             verbose: Boolean = false) {
        val classtable = DefaultCT()
        init(classtable)
        val v = Verifier(classtable)

        withEmptyContext {
            if (verbose) addUnificationListener(unificationsTracer)
            val g: (Term<Jtype<ID>>) -> Goal = {
                NotComplete(v).check(it, super_(classtable), true.toLogicBool())
            }

            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(count, answers.count())
            val expectedTerm = rez.toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    @Test
    @DisplayName("? <: Object")
    fun test1() {
        //        val a: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable -> Array_(classtable.object_t) }
        val b: (CLASSTABLE) -> Term<Jtype<ID>> = { classtable ->
            println("AAA")
            classtable.object_t
        }
        test(b, count = 2, rez = listOf(), verbose = true)
    }
    /*
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

                val fId = ct.addClass(logicListOf(ct.object_t, ct.object_t),
                        Class_(eId.toLogic(),
                                logicListOf(Type(Class_(dId.toLogic(),
                                        logicListOf(Type(ct.makeTVar(1, ct.object_t))))),
                                        Type(ct.makeTVar(0, ct.object_t))
                                )),
                        logicListOf())
                left = Class_(fId.toLogic(),
                        logicListOf(
                                Type(a!!), Type(b!!)
                        ))
                right = Class_(eId.toLogic(),
                        logicListOf(
                                Type(Class_(dId.toLogic(),
                                        logicListOf(Type(Class_(bId.toLogic(), logicListOf()))))),
                                Type(a!!)
                        ))

            }
            testForward({ left!! }, { right!! }, init, rez = true, verbose = false)
        }
    */
}
