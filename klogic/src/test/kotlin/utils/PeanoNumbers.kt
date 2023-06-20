package utils

import org.klogic.core.Goal
import org.klogic.core.Term
import org.klogic.core.and
import org.klogic.core.conde
import org.klogic.utils.terms.LogicBool
import org.klogic.utils.terms.LogicFalsᴼ.falsᴼ
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.LogicTruᴼ.truᴼ
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.PeanoLogicNumber
import org.klogic.utils.terms.PeanoLogicNumber.Companion.succ
import org.klogic.utils.terms.ZeroNaturalNumber.Z
import org.klogic.utils.terms.plus

internal val zero: PeanoLogicNumber = Z
internal val one: PeanoLogicNumber = succ(zero)
internal val two: PeanoLogicNumber = succ(one)

fun Int.toPeanoLogicNumber(): PeanoLogicNumber = if (this <= 0) Z else succ((this - 1).toPeanoLogicNumber())

private typealias PeanoTerm = Term<PeanoLogicNumber>

fun addᴼ(x: PeanoTerm, y: PeanoTerm, result: PeanoTerm): Goal = conde(
    (x debugUnify Z) and (result debugUnify y),
    freshTypedVars<PeanoLogicNumber, PeanoLogicNumber> { a, b ->
        (x debugUnify succ(a)) and (result debugUnify succ(b)) and addᴼ(a, y, b)
    }
)

fun mulᴼ(x: PeanoTerm, y: PeanoTerm, result: PeanoTerm): Goal = conde(
    (x debugUnify Z) and (result debugUnify Z),
    freshTypedVars<PeanoLogicNumber, PeanoLogicNumber> { a, b ->
        (x debugUnify succ(a)) and addᴼ(y, b, result) and mulᴼ(a, y, b)
    }
)

fun lessThanOrEqualᴼ(x: PeanoTerm, y: PeanoTerm, result: Term<LogicBool>): Goal = conde(
    (x debugUnify Z) and (result debugUnify truᴼ),
    (x ineq Z) and (y debugUnify Z) and (result debugUnify falsᴼ),
    freshTypedVars<PeanoLogicNumber, PeanoLogicNumber> { x1, y1 ->
        (x debugUnify succ(x1)) and (y debugUnify succ(y1)) and lessThanOrEqualᴼ(x1, y1, result)
    }
)

fun greaterThanOrEqualᴼ(x: PeanoTerm, y: PeanoTerm, result: Term<LogicBool>): Goal = lessThanOrEqualᴼ(y, x, result)

fun greaterThanᴼ(x: PeanoTerm, y: PeanoTerm, result: Term<LogicBool>): Goal = conde(
    (x ineq Z) and (y debugUnify Z) and (result debugUnify truᴼ),
    (x debugUnify Z) and (result debugUnify falsᴼ),
    freshTypedVars<PeanoLogicNumber, PeanoLogicNumber> { x1, y1 ->
        (x debugUnify succ(x1)) and (y debugUnify succ(y1)) and greaterThanᴼ(x1, y1, result)
    }
)

fun lessThanᴼ(x: PeanoTerm, y: PeanoTerm, result: Term<LogicBool>): Goal = greaterThanᴼ(y, x, result)

fun minMaxᴼ(a: PeanoTerm, b: PeanoTerm, min: PeanoTerm, max: PeanoTerm): Goal = conde(
    (min debugUnify a) and (max debugUnify b) and lessThanOrEqualᴼ(a, b, truᴼ),
    (min debugUnify b) and (max debugUnify a) and greaterThanᴼ(a, b, truᴼ),
)

fun smallestᴼ(
    nonEmptyList: Term<LogicList<PeanoLogicNumber>>,
    smallestElement: PeanoTerm,
    otherElements: Term<LogicList<PeanoLogicNumber>>
): Goal = conde(
    (nonEmptyList debugUnify logicListOf(smallestElement)) and (otherElements debugUnify nilLogicList()),
    freshTypedVars<PeanoLogicNumber, LogicList<PeanoLogicNumber>, PeanoLogicNumber, LogicList<PeanoLogicNumber>, PeanoLogicNumber> { head, tail, smallest1, tail1, max ->
        (otherElements debugUnify max + tail1) and
                (nonEmptyList debugUnify head + tail) and
                minMaxᴼ(head, smallest1, smallestElement, max) and
                smallestᴼ(tail, smallest1, tail1)
    }
)

fun sortᴼ(unsortedList: Term<LogicList<PeanoLogicNumber>>, sortedList: Term<LogicList<PeanoLogicNumber>>): Goal = conde(
    (unsortedList debugUnify nilLogicList()) and (sortedList debugUnify nilLogicList()),
    freshTypedVars<PeanoLogicNumber, LogicList<PeanoLogicNumber>, LogicList<PeanoLogicNumber>> { smallest, unsortedOthers, sortedTail ->
        (sortedList debugUnify smallest + sortedTail) and sortᴼ(unsortedOthers, sortedTail) and smallestᴼ(unsortedList, smallest, unsortedOthers)
    }
)