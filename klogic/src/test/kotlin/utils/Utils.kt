package utils

import org.klogic.core.*
import org.klogic.core.Var.Companion.createTypedVar
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.plus
import org.klogic.utils.terms.toLogicList

object UnificationsController {
    private var unificationsCounter: Int = 0

    fun onUnification() {
        ++unificationsCounter
    }

    fun onFinish() {
        System.out.printf("unifications: %d\n", unificationsCounter)
        clear()
    }

    private fun clear() {
        unificationsCounter = 0
    }
}

context(RelationalContext)
infix fun <T : Term<T>> Term<T>.debugUnify(other: Term<T>): Goal = { state: State ->
    if (System.getenv("SILENT_UNIFICATIONS") == null)
        System.out.printf("%s %s ", this, other)
    UnificationsController.onUnification()

    val rez = (this unify other)(state)
    if (rez.msplit() != null)
        System.out.printf("\n")
    else System.out.printf(" _|_\n")
    rez

}

typealias ListTerm<T> = Term<LogicList<T>>

private var variableIndex: Int = 10
// This variable index clashes regularly wiht indexes introduced by `run`.
// So I changed 0 -> 10
// Kakadu

fun <T : Term<T>> freshTypedVar(): Var<T> = (variableIndex++).createTypedVar()

context(RelationalContext)
fun <T1 : Term<T1>> freshTypedVars(f: (Term<T1>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()

    delay { f(first) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>> freshTypedVars(
        f: (Term<T1>, Term<T2>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()

    delay { f(first, second) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()

    delay { f(first, second, third) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>, T4 : Term<T4>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>, Term<T4>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()
    val fourth = freshTypedVar<T4>()

    delay { f(first, second, third, fourth) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>, T4 : Term<T4>, T5 : Term<T5>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>, Term<T4>, Term<T5>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()
    val fourth = freshTypedVar<T4>()
    val fifth = freshTypedVar<T5>()

    delay { f(first, second, third, fourth, fifth) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>, T4 : Term<T4>, T5 : Term<T5>, T6 : Term<T6>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>, Term<T4>, Term<T5>, Term<T6>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()
    val fourth = freshTypedVar<T4>()
    val fifth = freshTypedVar<T5>()
    val sixth = freshTypedVar<T6>()

    delay { f(first, second, third, fourth, fifth, sixth) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>, T4 : Term<T4>, T5 : Term<T5>, T6 : Term<T6>, T7 : Term<T7>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>, Term<T4>, Term<T5>, Term<T6>, Term<T7>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()
    val fourth = freshTypedVar<T4>()
    val fifth = freshTypedVar<T5>()
    val sixth = freshTypedVar<T6>()
    val seventh = freshTypedVar<T7>()

    delay { f(first, second, third, fourth, fifth, sixth, seventh) }(st)
}

context(RelationalContext)
fun <T1 : Term<T1>, T2 : Term<T2>, T3 : Term<T3>, T4 : Term<T4>, T5 : Term<T5>, T6 : Term<T6>, T7 : Term<T7>, T8 : Term<T8>> freshTypedVars(
        f: (Term<T1>, Term<T2>, Term<T3>, Term<T4>, Term<T5>, Term<T6>, Term<T7>, Term<T8>) -> Goal): Goal = { st: State ->
    val first = freshTypedVar<T1>()
    val second = freshTypedVar<T2>()
    val third = freshTypedVar<T3>()
    val fourth = freshTypedVar<T4>()
    val fifth = freshTypedVar<T5>()
    val sixth = freshTypedVar<T6>()
    val seventh = freshTypedVar<T7>()
    val eighth = freshTypedVar<T8>()

    delay { f(first, second, third, fourth, fifth, sixth, seventh, eighth) }(st)
}

context(RelationalContext)
fun <T : Term<T>> appendo(a: ListTerm<T>, b: ListTerm<T>, ab: ListTerm<T>): Goal = { state ->
    System.out.printf("appendo: %s %s %s\n", a, b, ab)

    conde(
            and(
                    (a debugUnify nilLogicList()),
                    (b debugUnify ab)
            ),
            freshTypedVars<T, LogicList<T>, LogicList<T>> { head, tail, rest ->
                and(
                        (a debugUnify head + tail),
                        (ab debugUnify head + rest),
                        appendo(tail, b, rest)
                )
            }
    )(state)
}

context(RelationalContext)
fun <T : Term<T>> reverso(a: ListTerm<T>, b: ListTerm<T>): Goal = { state ->
    System.out.printf("reverso: %s %s\n", a, b)

    conde(
            and(
                    (a debugUnify nilLogicList()),
                    (a debugUnify b)
            ),
            freshTypedVars<T, LogicList<T>, LogicList<T>> { h, t, rest ->
                and(
                        (a debugUnify h + t),
                        reverso(t, rest),
                        appendo(
                                rest,
                                h.toLogicList(),
                                b
                        )
                )
            }
    )(state)
}

context(RelationalContext)
fun <A: Term<A>> debugUnify(msg: String, a: Term<A>, b: Term<A>) : Goal = { st ->
    println(msg);
    (a `===` b)(st)
}
