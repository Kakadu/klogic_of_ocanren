import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.api.Test
import org.klogic.core.*
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.ZeroNaturalNumber
import utils.JGS.*
import utils.JGS.Closure.CLOSURE
import utils.JGS.Closure.Closure
import utils.JGS.Var
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.LogicOption


typealias DirectT = (
    v29: (Term<Jtype<LogicInt>>, Term<Jtype<LogicInt>>, Term<LogicBool>) -> Goal, v30: Term<Jtype<LogicInt>>, v31: Term<Jtype<LogicInt>>, v32: Term<LogicBool>
) -> Goal

class JGSBackward {
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

    internal fun <T> Iterable<T>.toCountMap(): Map<out T, Int> = groupingBy { it }.eachCount()

    @Test
    @DisplayName("Wanna specify a domain and cut type variables.")
    fun test0wildcards() {
        withEmptyContext {
            val dom: (Term<Jtype<ID>>) -> Goal = { it ->
                conde(it `===` Class_(1.toLogic(), logicListOf()),
                    it `===` Interface(2.toLogic(), logicListOf()),
                    freshTypedVars { c: Term<Jtype<ID>>, d: Term<LogicOption<Jtype<ID>>> ->
                        it `===` Var(4.toLogic(), ZeroNaturalNumber, c, d)
                    })
            }
            val goal: (Term<Jtype<ID>>) -> Goal = { it ->
                and(
                    // I expect that next lines removes all Type Variables, but it doesn't
                    it `!==` Var(wildcard(), wildcard(), wildcard(), wildcard()), dom(it)
                )
            }
            val answers = run(10, goal).map { it.term }.toList()
            val expectedTerm = listOf(
                Class_(1.toLogic(), logicListOf()), Interface(2.toLogic(), logicListOf())
            ).toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    enum class ClosureType {
        Subtyping, SuperTyping
    }

//    class MakeClosure(
//        private val closureBuilder: CLOSURE,
//        val ct: CLASSTABLE,
//        private val closureType: ClosureType,
//        private val verifier: VERIFIER,
//        private val ctx: RelationalContext
//    ) {
//        fun direct(ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>): Goal = { st ->
//            println("direct:  ${st.reify(ta)}")
//            println("         ${st.reify(tb)}")
//            (with(ctx) {
//                closureBuilder.minus_less_minus( // ERROR. No required context receiver found:
//                    // this function is passed as parameter in OCaml, but here we are trying to inline it
//                    // see run_json2.ml line 230
//                    { a, b, c, d -> verifier.minus_less_minus(a, b, c, d) },
//                    { a, b -> closure(a, b) },
//                    { success },
//                    ta,
//                    tb
//                )
//            }(st))
//        }
//
//        fun isCorrect(t: Term<Jtype<ID>>): Goal {
//            with(ctx) {
//                return closureBuilder.is_correct_type({ a, b -> closure(a, b) }, t)
//            }
//        }
//
//
//        fun closure(ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>): Goal {
//            with(ctx) {
//                return when (closureType) {
//                    ClosureType.Subtyping ->
//                        closureBuilder.less_minus_less({ a, b -> direct(a, b) }, success, ta, tb)
//
//                    ClosureType.SuperTyping ->
//                        TODO("Not implemented")
//                }
//            }
//        }
//    }


    class MakeClosure2(val closure: CLOSURE) {
        context(RelationalContext)
        fun debugVarHandler(ta: Term<Jtype<ID>>, closureDown: Goal, closureUp: Goal): Goal =
            debugVar(ta, reifier = { it -> it.reified() }) {
                when (it) {
                    is CustomTerm<*> -> closureUp
                    else -> closureDown
                }
            }

//        fun directSubtyping(direct: DirectT,ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>) : Goal =
//                closure.direct_subtyping()

        context(RelationalContext)
        fun closure(direct: DirectT, ta: Term<Jtype<ID>>, tb: Term<Jtype<ID>>): Goal =
            closure.closure({ a, b, c -> debugVarHandler(a, b, c) }, direct, success, ta, tb)
    }

    // new revised by Peter
    // specifies upper bound
    fun testSingleConstraint2(
        expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>>,
        count: Int = 10,
        boundKind: ClosureType = ClosureType.Subtyping,
        bound: (CLASSTABLE) -> Term<Jtype<ID>>,
        verbose: Boolean = false
    ) {
        val classTable = DefaultCT()
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q), (when (boundKind) {
                        ClosureType.Subtyping -> MakeClosure2(closureBuilder).closure({ a, b, c, d ->
                            v.minus_less_minus(
                                a,
                                b,
                                c,
                                d
                            )
                        }, q, bound(classTable))

                        ClosureType.SuperTyping -> TODO()
                    })
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(count, answers.count())
            val expectedTerm = expectedResult(classTable).toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    fun testBinary(
        expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>>,
        count: Int = 10,
        init: (MutableClassTable) -> Unit = { },
        verbose: Boolean = false,
        makeGoal: (RelationalContext, Term<Jtype<ID>>) -> ((Term<Jtype<ID>>, Term<Jtype<ID>>) -> Goal) -> Goal
    ) {
        val classTable = DefaultCT()
        init(classTable)
        val v = Verifier(classTable)
        val closureBuilder = Closure(classTable)
        withEmptyContext {
            val queryItself: (Term<Jtype<ID>>, Term<Jtype<ID>>) -> Goal = { a: Term<Jtype<ID>>, b: Term<Jtype<ID>> ->
                MakeClosure2(closureBuilder).closure({ a, b, c, d -> v.minus_less_minus(a, b, c, d) }, a, b)
            }
            val g = { q: Term<Jtype<ID>> ->
                and(
                    only_classes_interfaces_and_arrays(q), makeGoal(this, q)(queryItself)
                )
            }
            val answers = run(count, g).map { it.term }.toList()
            if (verbose) answers.forEachIndexed { i, x -> println("$i: $x") }

            assertEquals(count, answers.count())
            val expectedTerm = expectedResult(classTable).toCountMap()
            assertEquals(expectedTerm, answers.toCountMap())
        }
    }

    @Test
    @DisplayName("? <: Object")
    fun test1() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                ct.object_t, Array_(ct.object_t), Array_(Array_(ct.object_t)), Array_(Null) as Jtype<ID>
            )
        }
        testSingleConstraint2(expectedResult, count = 4, ClosureType.Subtyping, { it.object_t }, verbose = false)
    }

    @Test
    @DisplayName("? <: Cloneable")
    fun test2() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                ct.object_t
            )
        }
        testSingleConstraint2(expectedResult, count = 1, ClosureType.Subtyping, { it.cloneable_t }, verbose = false)
    }

    @Test
    @DisplayName("? <: Cloneable[][]")
    fun test3() {
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                Array_(Null) as Jtype<ID>
            )
        }

        testSingleConstraint2(
            expectedResult,
            // larget count will generate answers with intersections and Vars
            count = 1, ClosureType.Subtyping, { Array_(Array_(it.cloneable_t)) }, verbose = false
        )
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
        val expectedResult: (CLASSTABLE) -> Collection<Term<Jtype<ID>>> = { ct ->
            listOf(
                b!!
            )
        }
        testBinary(
            expectedResult,
            count = 1,
            init = init,
            verbose = false
        ) { ctx: RelationalContext, q: Term<Jtype<ID>> ->
            { f ->
                with(ctx) { f(b!!, a!!) and (q `===` b!!) }
            }
        }
    }
}
