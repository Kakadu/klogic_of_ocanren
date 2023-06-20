@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName")

package utils

import org.klogic.core.*
import org.klogic.utils.terms.*
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.Symbol.Companion.toSymbol
import utils.OlegLogicNumber.Companion.digitOne
import utils.OlegLogicNumber.Companion.digitZero
import utils.OlegLogicNumber.Companion.numberZero
import utils.OlegLogicNumber.Companion.toOlegLogicNumber

typealias Digit = Symbol

private typealias OlegTerm = Term<OlegLogicNumber>
private typealias DigitTerm = Term<Digit>

/**
 * Logic number represented by list of [Digit]s, from the last digit to the first.
 */
data class OlegLogicNumber(val digits: Term<LogicList<Digit>>) : UnaryTerm<OlegLogicNumber, Term<LogicList<Digit>>>() {
    override val value: Term<LogicList<Digit>>
        get() = digits
    override val constructor: (Term<LogicList<Digit>>) -> OlegLogicNumber
        get() = ::OlegLogicNumber

    operator fun get(index: Int): DigitTerm = (digits as LogicList<Digit>)[index]

    fun toUInt(): UInt = digits.asReified().toList().foldIndexed(0u) { i, accumulator, current ->
        accumulator or (current.asReified().toString().toUInt() shl i)
    }

    override fun toString(): String = digits.toString()

    companion object {
        internal val digitZero: Digit = "0".toSymbol()
        internal val digitOne: Digit = "1".toSymbol()

        val numberZero: OlegLogicNumber = nilLogicList<Digit>().toOlegLogicNumber()

        fun UInt.toOlegLogicNumber(): OlegLogicNumber = OlegLogicNumber(toLogicList())

        fun Term<LogicList<Digit>>.toOlegLogicNumber(): OlegLogicNumber = OlegLogicNumber(this)

        private fun UInt.toLogicList(): LogicList<Digit> =
            when {
                this == 0u -> nilLogicList()
                this % 2u == 0u -> digitZero + (this / 2u).toLogicList()
                else -> digitOne + (this / 2u).toLogicList()
            }
    }
}

internal val numberOne: OlegLogicNumber = digitOne.toLogicList().toOlegLogicNumber()
internal val numberTwo: OlegLogicNumber = (digitZero + digitOne.toLogicList()).toOlegLogicNumber()
internal val numberThree: OlegLogicNumber = (digitOne + digitOne.toLogicList()).toOlegLogicNumber()

fun <T : Term<T>> appendᴼ(x: ListTerm<T>, y: ListTerm<T>, xy: ListTerm<T>): Goal =
    conde (
        (x `===` nilLogicList()) and (y `===` xy),
        freshTypedVars<T, LogicList<T>, LogicList<T>> { head, tail, rest ->
            (head + tail `===` x) and (head + rest `===` xy) and appendᴼ(tail, y, rest)
        }
    )

/**
 * Checks whether the [number] is positive.
 */
fun posᴼ(number: OlegTerm): Goal = freshTypedVars<Digit, LogicList<Digit>> { head, tail ->
    number debugUnify (head + tail).toOlegLogicNumber()
}

/**
 * Checks whether [number] is greater than 1.
 */
fun greaterThan1ᴼ(number: OlegTerm): Goal =
    freshTypedVars<Digit, Digit, LogicList<Digit>> { head, tailHead, tail ->
        number debugUnify (head + (tailHead + tail)).toOlegLogicNumber()
    }

/**
 * Satisfies [b] + [x] + [y] = [r] + 2 * [c]
 */
fun fullAdderᴼ(b: DigitTerm, x: DigitTerm, y: DigitTerm, r: DigitTerm, c: DigitTerm): Goal = conde(
    (digitZero debugUnify b) and (digitZero debugUnify x) and (digitZero debugUnify y) and (digitZero debugUnify r) and (digitZero debugUnify c),
    (digitOne debugUnify b) and (digitZero debugUnify x) and (digitZero debugUnify y) and (digitOne debugUnify r) and (digitZero debugUnify c),
    (digitZero debugUnify b) and (digitOne debugUnify x) and (digitZero debugUnify y) and (digitOne debugUnify r) and (digitZero debugUnify c),
    (digitOne debugUnify b) and (digitOne debugUnify x) and (digitZero debugUnify y) and (digitZero debugUnify r) and (digitOne debugUnify c),
    (digitZero debugUnify b) and (digitZero debugUnify x) and (digitOne debugUnify y) and (digitOne debugUnify r) and (digitZero debugUnify c),
    (digitOne debugUnify b) and (digitZero debugUnify x) and (digitOne debugUnify y) and (digitZero debugUnify r) and (digitOne debugUnify c),
    (digitZero debugUnify b) and (digitOne debugUnify x) and (digitOne debugUnify y) and (digitZero debugUnify r) and (digitOne debugUnify c),
    (digitOne debugUnify b) and (digitOne debugUnify x) and (digitOne debugUnify y) and (digitOne debugUnify r) and (digitOne debugUnify c)
)

/**
 * Adds a carry-in bit [d] to arbitrarily large numbers [n] and [m] to produce a number [r].
 */
fun adderᴼ(d: DigitTerm, n: OlegTerm, m: OlegTerm, r: OlegTerm): Goal = conde(
    (digitZero debugUnify d) and (m debugUnify numberZero) and (n debugUnify r),
    (digitZero debugUnify d) and (n debugUnify numberZero) and (m debugUnify r) and posᴼ(m),
    (digitOne debugUnify d) and (m debugUnify numberZero) and delay { adderᴼ(digitZero, n, numberOne, r) },
    (digitOne debugUnify d) and (n debugUnify numberZero) and posᴼ(m) and delay { adderᴼ(digitZero, m, numberOne, r) },
    and(
        (n debugUnify numberOne), (m debugUnify numberOne), freshTypedVars<Digit, Digit> { a, c ->
            (logicListOf(a, c).toOlegLogicNumber() debugUnify r) and fullAdderᴼ(d, digitOne, digitOne, a, c)
        }
    ),
    (n debugUnify numberOne) and genAdderᴼ(d, n, m, r),
    (m debugUnify numberOne) and greaterThan1ᴼ(n) and greaterThan1ᴼ(r) and delay { adderᴼ(d, numberOne, n, r) },
    greaterThan1ᴼ(n) and genAdderᴼ(d, n, m, r)
)

/**
 * Satisfies [d] + [n] + [m] = [r], provided that [m] and [r] are greater than 1 and [n] is positive.
 */
fun genAdderᴼ(d: DigitTerm, n: OlegTerm, m: OlegTerm, r: OlegTerm): Goal =
    freshTypedVars<Digit, Digit, Digit, Digit, LogicList<Digit>, LogicList<Digit>, LogicList<Digit>> { a, b, c, e, x, y, z ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()
        val numberZ = z.toOlegLogicNumber()

        ((a + x).toOlegLogicNumber() debugUnify n) and
                ((b + y).toOlegLogicNumber() debugUnify m) and
                posᴼ(numberY) and
                ((c + z).toOlegLogicNumber() debugUnify r) and
                posᴼ(numberZ) and
                (fullAdderᴼ(d, a, b, c, e)) and
                (adderᴼ(e, numberX, numberY, numberZ))
    }

fun plusᴼ(n: OlegTerm, m: OlegTerm, result: OlegTerm): Goal = adderᴼ(digitZero, n, m, result)

fun minusᴼ(n: OlegTerm, m: OlegTerm, result: OlegTerm): Goal = plusᴼ(m, result, n)

fun boundMulᴼ(q: OlegTerm, p: OlegTerm, n: OlegTerm, m: OlegTerm): Goal = conde(
    (q debugUnify numberZero) and posᴼ(p),
    freshTypedVars<Digit, Digit, Digit, Digit, LogicList<Digit>, LogicList<Digit>, LogicList<Digit>> { a0, a1, a2, a3, x, y, z ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()
        val numberZ = z.toOlegLogicNumber()

        and(
            q debugUnify (a0 + x).toOlegLogicNumber(),
            p debugUnify (a1 + y).toOlegLogicNumber(),
            conde(
                and(
                    n debugUnify numberZero,
                    m debugUnify (a2 + z).toOlegLogicNumber(),
                    boundMulᴼ(numberX, numberY, numberZ, numberZero)
                ),
                and(
                    n debugUnify (a3 + z).toOlegLogicNumber(),
                    boundMulᴼ(numberX, numberY, numberZ, m)
                )
            )
        )
    }
)



// *o
fun mulᴼ(n: OlegTerm, m: OlegTerm, p: OlegTerm): Goal = conde(
    (n debugUnify numberZero) and (p debugUnify numberZero),
    posᴼ(n) and (m debugUnify numberZero) and (p debugUnify numberZero),
    (n debugUnify numberOne) and posᴼ(m) and (m debugUnify p),
    greaterThan1ᴼ(n) and (m debugUnify numberOne) and (n debugUnify p),
    freshTypedVars<LogicList<Digit>, LogicList<Digit>> { x, z ->
        val numberX = x.toOlegLogicNumber()
        val numberZ = z.toOlegLogicNumber()

        and(
            (n debugUnify (digitZero + x).toOlegLogicNumber()) and posᴼ(numberX),
            (p debugUnify (digitZero + z).toOlegLogicNumber()) and posᴼ(numberZ),
            greaterThan1ᴼ(m),
            mulᴼ(numberX, m, numberZ)
        )
    },
    freshTypedVars<LogicList<Digit>, LogicList<Digit>> { x, y ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()

        and(
            (n debugUnify (digitOne + x).toOlegLogicNumber()) and posᴼ(numberX),
            (m debugUnify (digitZero + y).toOlegLogicNumber()) and posᴼ(numberY),
            mulᴼ(m, n, p)
        )
    },
    freshTypedVars<LogicList<Digit>, LogicList<Digit>> { x, y ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()

        and(
            (n debugUnify (digitOne + x).toOlegLogicNumber()) and posᴼ(numberX),
            (m debugUnify (digitOne + y).toOlegLogicNumber()) and posᴼ(numberY),
            oddMulᴼ(numberX, n, m, p)
        )
    }
)

fun oddMulᴼ(x: OlegTerm, n: OlegTerm, m: OlegTerm, p: OlegTerm): Goal = freshTypedVars<LogicList<Digit>> { q ->
    val number = q.toOlegLogicNumber()

    and(
        boundMulᴼ(number, p, n, m),
        mulᴼ(x, m, number),
        plusᴼ((digitZero + q).toOlegLogicNumber(), m, p)
    )
}

// `=lo`
fun hasTheSameLengthᴼ(n: OlegTerm, m: OlegTerm): Goal = conde(
    (n debugUnify numberZero) and (m debugUnify numberZero),
    (n debugUnify numberOne) and (m debugUnify numberOne),
    freshTypedVars<Digit, LogicList<Digit>, Digit, LogicList<Digit>> { a, x, b, y ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()

        ((a + x).toOlegLogicNumber() debugUnify n) and posᴼ(numberX) and
                ((b + y).toOlegLogicNumber() debugUnify m) and posᴼ(numberY) and
                hasTheSameLengthᴼ(numberX, numberY)
    }
)

// `<lo`
fun hasTheSmallerLengthᴼ(n: OlegTerm, m: OlegTerm): Goal = conde(
    (n debugUnify numberZero) and posᴼ(m),
    (n debugUnify numberOne) and greaterThan1ᴼ(m),
    freshTypedVars<Digit, LogicList<Digit>, Digit, LogicList<Digit>> { a, x, b, y ->
        val numberX = x.toOlegLogicNumber()
        val numberY = y.toOlegLogicNumber()

        ((a + x).toOlegLogicNumber() debugUnify n) and posᴼ(numberX) and
                ((b + y).toOlegLogicNumber() debugUnify m) and posᴼ(numberY) and
                hasTheSmallerLengthᴼ(numberX, numberY)
    }
)

// `<=lo`
fun hasTheSmallerOrSameLengthᴼ(n: OlegTerm, m: OlegTerm): Goal = conde(
    hasTheSameLengthᴼ(n, m),
    hasTheSmallerLengthᴼ(n, m)
)

// `<o`
fun lessThanᴼ(n: OlegTerm, m: OlegTerm): Goal = conde(
    hasTheSmallerLengthᴼ(n, m),
    hasTheSameLengthᴼ(n, m) and freshTypedVars<OlegLogicNumber> { x -> posᴼ(x) and plusᴼ(n, x, m) }
)

// `<=o`
fun lessThanOrEqualᴼ(n: OlegTerm, m: OlegTerm): Goal = conde(
    n debugUnify m,
    lessThanᴼ(n, m)
)

fun repeatedMulᴼ(n: OlegTerm, q: OlegTerm, nq: OlegTerm): Goal = conde(
    posᴼ(n) and (q debugUnify numberZero) and (nq debugUnify numberOne),
    (q debugUnify numberOne) and (n debugUnify nq),
    and(
        greaterThan1ᴼ(q),
        freshTypedVars<OlegLogicNumber, OlegLogicNumber> { q1, nq1 ->
            and(
                plusᴼ(q1, numberOne, q),
                repeatedMulᴼ(n, q1, nq1),
                mulᴼ(nq1, n, nq)
            )
        }
    )
)

/**
 * Satisfies n = m * q + r, with 0 <= r < m.
 */
fun divᴼ(n: OlegTerm, m: OlegTerm, q: OlegTerm, r: OlegTerm): Goal = conde(
    (r debugUnify n) and (q debugUnify numberZero) and lessThanᴼ(n, m),
    and(
        (q debugUnify numberOne),
        hasTheSameLengthᴼ(n, m),
        plusᴼ(r, m, n),
        lessThanᴼ(r, m)
    ),
    and(
        hasTheSmallerLengthᴼ(m, n),
        lessThanᴼ(r, m),
        posᴼ(q),
        freshTypedVars<LogicList<Digit>, OlegLogicNumber, LogicList<Digit>, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, LogicList<Digit>> { nh, nl, qh, ql, qlm, qlmr, rr, rh ->
            val numberNh = nh.toOlegLogicNumber()
            val numberQh = qh.toOlegLogicNumber()
            val numberRh = rh.toOlegLogicNumber()

            and(
                splitᴼ(n, r, nl, nh),
                splitᴼ(q, r, ql, qh),
                conde(
                    and(
                        numberNh debugUnify numberZero,
                        numberQh debugUnify numberZero,
                        minusᴼ(nl, r, qlm),
                        mulᴼ(ql, m, qlm)
                    ),
                    and(
                        posᴼ(numberNh),
                        mulᴼ(ql, m, qlm),
                        plusᴼ(qlm, r, qlmr),
                        minusᴼ(qlmr, nl, rr),
                        splitᴼ(rr, r, numberZero, rh),
                        divᴼ(numberNh, m, numberQh, numberRh)
                    )
                )
            )
        }
    )
)

/**
 *  Splits a binary numeral at a given length:
 * (split o n r l h) holds if n = 2^{s+1} · l + h where s = ∥r∥ and h < 2^{s+1}.
 */
fun splitᴼ(n: OlegTerm, r: OlegTerm, l: OlegTerm, h: Term<LogicList<Digit>>): Goal = conde(
    (n debugUnify numberZero) and (h debugUnify nilLogicList()) and (l debugUnify numberZero),
    freshTypedVars<Digit, LogicList<Digit>> { b, n1 ->
        val concatenation = b + n1

        and(
            n debugUnify (digitZero + concatenation).toOlegLogicNumber(),
            r debugUnify numberZero,
            h debugUnify concatenation,
            l debugUnify numberZero
        )
    },
    freshTypedVars<LogicList<Digit>> { n1 ->
        and(
            n debugUnify (digitOne + n1).toOlegLogicNumber(),
            (r debugUnify numberZero),
            (n1 debugUnify h),
            (l debugUnify numberOne)
        )
    },
    freshTypedVars<Digit, LogicList<Digit>, Digit, LogicList<Digit>> { b, n1, a, r1 ->
        val concatenation = b + n1

        and(
            n debugUnify (digitZero + concatenation).toOlegLogicNumber(),
            r debugUnify (a + r1).toOlegLogicNumber(),
            l debugUnify numberZero,
            splitᴼ(concatenation.toOlegLogicNumber(), r1.toOlegLogicNumber(), numberZero, h)
        )
    },
    freshTypedVars<LogicList<Digit>, Digit, LogicList<Digit>> { n1, a, r1 ->
        and(
            n debugUnify (digitOne + n1).toOlegLogicNumber(),
            r debugUnify (a + r1).toOlegLogicNumber(),
            l debugUnify numberOne,
            splitᴼ(n1.toOlegLogicNumber(), r1.toOlegLogicNumber(), numberZero, h)
        )
    },
    freshTypedVars<Digit, LogicList<Digit>, Digit, LogicList<Digit>, LogicList<Digit>> { b, n1, a, r1, l1 ->
        val numberL1 = l1.toOlegLogicNumber()

        and(
            n debugUnify (b + n1).toOlegLogicNumber(),
            r debugUnify (a + r1).toOlegLogicNumber(),
            l debugUnify (b + l1).toOlegLogicNumber(),
            posᴼ(numberL1),
            splitᴼ(n1.toOlegLogicNumber(), r1.toOlegLogicNumber(), numberL1, h)
        )
    },
)

/**
 * Satisfies n = b ^ q + r, where 0 <= r <= n and q is the largest.
 */
@Suppress("NAME_SHADOWING")
fun logᴼ(n: OlegTerm, b: OlegTerm, q: OlegTerm, r: OlegTerm): Goal = conde(
    (n debugUnify numberOne) and posᴼ(b) and (q debugUnify numberZero) and (r debugUnify numberZero),
    (q debugUnify numberZero) and lessThanᴼ(n, b) and plusᴼ(r, numberOne, n),
    (q debugUnify numberOne) and greaterThan1ᴼ(b) and hasTheSameLengthᴼ(n, b) and plusᴼ(r, b, n),
    (b debugUnify numberOne) and posᴼ(q) and plusᴼ(r, numberOne, n),
    (b debugUnify numberZero) and posᴼ(q) and (r debugUnify n),
    (b debugUnify numberTwo) and freshTypedVars<Digit, Digit, LogicList<Digit>> { a, ad, dd ->
        val numberDd = dd.toOlegLogicNumber()

        and(
            posᴼ(numberDd),
            n debugUnify (a + (ad + dd)).toOlegLogicNumber(),
            exp2ᴼ(n, nilLogicList(), q),
            freshTypedVars<LogicList<Digit>> { s ->
                splitᴼ(n, numberDd, r, s)
            }
        )
    },
    and(
        freshTypedVars<Digit, Digit, Digit, LogicList<Digit>> { a, ad, add, ddd ->
            conde(
                b debugUnify numberThree,
                b debugUnify (a + (ad + (add + ddd))).toOlegLogicNumber()
            )
        },
        hasTheSmallerLengthᴼ(b, n),
        freshTypedVars<OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber> { bw1, bw, nw, nw1, ql1, ql, s ->
            and(
                exp2ᴼ(b, nilLogicList(), bw1),
                plusᴼ(bw1, numberOne, bw),
                hasTheSmallerLengthᴼ(q, n),
                freshTypedVars<OlegLogicNumber, OlegLogicNumber> { q1, bwq1 ->
                    and(
                        plusᴼ(q, numberOne, q1),
                        mulᴼ(bw, q1, bwq1),
                        lessThanᴼ(nw1, bwq1)
                    )
                },
                exp2ᴼ(n, nilLogicList(), nw1),
                plusᴼ(nw1, numberOne, nw),
                divᴼ(nw, bw, ql1, s),
                plusᴼ(ql, numberOne, ql1),
                hasTheSmallerOrSameLengthᴼ(ql, q),
                freshTypedVars<OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber, OlegLogicNumber> { bql, qh, s, qdh, qd ->
                    and(
                        repeatedMulᴼ(b, ql, bql),
                        divᴼ(nw, bw1, qh, s),
                        plusᴼ(ql, qdh, qh),
                        plusᴼ(ql, qd, q),
                        lessThanOrEqualᴼ(qd, qdh),
                        freshTypedVars<OlegLogicNumber, OlegLogicNumber, OlegLogicNumber> { bqd, bq1, bq ->
                            and(
                                repeatedMulᴼ(b, qd, bqd),
                                mulᴼ(bql, bqd, bq),
                                mulᴼ(b, bq, bq1),
                                plusᴼ(bq, r, n),
                                lessThanᴼ(n, bq1)
                            )
                        }
                    )
                }
            )
        }
    )
)

fun exp2ᴼ(n: OlegTerm, b: Term<LogicList<Digit>>, q: OlegTerm): Goal {
    val numberB = b.toOlegLogicNumber()

    return conde(
        (n debugUnify numberOne) and (q debugUnify numberZero),
        and(
            greaterThan1ᴼ(n) and (q debugUnify numberOne),
            freshTypedVars<OlegLogicNumber> { s ->
                splitᴼ(n, numberB, s, logicListOf(digitOne))
            }
        ),
        freshTypedVars<LogicList<Digit>, LogicList<Digit>> { q1, b2 ->
            val numberQ1 = q1.toOlegLogicNumber()

            and(
                q debugUnify (digitZero + q1).toOlegLogicNumber(),
                posᴼ(numberQ1),
                hasTheSmallerLengthᴼ(numberB, n),
                appendᴼ(b, digitOne + b, b2),
                exp2ᴼ(n, b2, numberQ1)
            )
        },
        freshTypedVars<LogicList<Digit>, LogicList<Digit>, LogicList<Digit>, OlegLogicNumber> { q1, nh, b2, s ->
            val numberQ1 = q1.toOlegLogicNumber()
            val numberNh = nh.toOlegLogicNumber()

            and(
                q debugUnify (digitOne + q1).toOlegLogicNumber(),
                posᴼ(numberQ1),
                posᴼ(numberNh),
                splitᴼ(n, numberB, s, nh),
                appendᴼ(b, digitOne + b, b2),
                exp2ᴼ(numberNh, b2, numberQ1)
            )
        }
    )
}

fun expᴼ(b: OlegTerm, q: OlegTerm, n: OlegTerm): Goal = logᴼ(n, b, q, numberZero)
