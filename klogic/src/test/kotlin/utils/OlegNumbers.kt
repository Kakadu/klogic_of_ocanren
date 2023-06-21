// Autogenerated file
@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName")

package utils

import org.klogic.core.*
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.plus
import utils.LogicInt.Companion.toLogic

val digitZero: Digit = 0.toLogic()
val digitOne: Digit = 1.toLogic()

typealias Digit = LogicInt
typealias OlegLogicNumber = LogicList<Digit>

val zero: OlegLogicNumber = logicListOf()
val one: OlegLogicNumber = logicListOf( 1.toLogic() )
val three: OlegLogicNumber = logicListOf( 1.toLogic(), 1.toLogic() )

fun UInt.toOlegLogicNumber(): OlegLogicNumber = toLogicList()
fun UInt.toLogicList(): LogicList<Digit> =
    when {
        this == 0u -> nilLogicList()
        this % 2u == 0u -> digitZero + (this / 2u).toLogicList()
        else -> digitOne + (this / 2u).toLogicList()
    }

fun <T> pause(f: () -> RecursiveStream<T>): RecursiveStream<T> = ThunkStream(f)


// There are 3 relations
fun poso(n: Term<LogicList<LogicInt>>): Goal =
  { st: State ->
  pause { val h : Term<LogicInt> = freshTypedVar();
          val t : Term<LogicList<LogicInt>> = freshTypedVar();
          (n `===` (h + t))(st)
  } }
fun zeroo(n: Term<LogicList<LogicInt>>): Goal =
  (n `===` nilLogicList())
fun appendo(l: Term<LogicList<LogicInt>>, s: Term<LogicList<LogicInt>>,
out: Term<LogicList<LogicInt>>): Goal =
  { st: State ->
  pause { (((((l `===` nilLogicList())(st))
              bind
              ((s `===` out))))
            mplus
            
            (pause { { st: State ->
                     pause { val a : Term<LogicInt> = freshTypedVar();
                             val d : Term<LogicList<LogicInt>> = freshTypedVar();
                             val res : Term<LogicList<LogicInt>> = freshTypedVar();
                             ((((((a + d) `===` l)(st))
                                 bind
                                 (((a + res) `===` out))))
                               bind
                               (appendo(d, s, res)))
                     } }(st)
                       }))
            }
  }
// Put epilogue here 
