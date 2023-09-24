// Autogenerated file
@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName")

package utils.JGS

import org.klogic.core.*
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.plus
import utils.LogicInt
import utils.LogicOption
//import utils.None

typealias Decl = LogicInt
typealias JType = LogicInt

fun <T: Term<T>> None(): LogicOption<T> = utils.None as LogicOption<T>

fun  pause(f: () -> Goal): Goal = { st -> ThunkStream { f()(st) } }

// There are 5 relations
fun conso1(xs: Term<LogicList<LogicInt>>): Goal =
/* NOTE: fresh without delay */
freshTypedVars { h : Term<LogicInt> ->
freshTypedVars { tl: Term<LogicList<LogicInt>> -> (xs `===` (h + tl)) } 
}
fun nilo1(xs: Term<LogicList<LogicInt>>): Goal =
xs `===` nilLogicList()
// CT 
interface CT {
  // decl_by_id
  fun decl_by_id(v1: (Term<LogicInt>) -> Goal, v2: Term<Decl>): Goal
  // get_superclass
  fun get_superclass(v3: (Term<LogicInt>) -> Goal,
  v4: (Term<LogicInt>) -> Goal, v5: Term<LogicOption<JType>>): Goal
  // new_var
  fun new_var(v6: (Term<LogicInt>) -> Goal, v7: Term<LogicInt>): Goal
  }
// STUFF 
interface STUFF {
  }
// functor
private val Stuff : (CT) -> STUFF = { Impl: CT ->
object: STUFF {
  fun not_a_superclass(a: Term<LogicInt>, b: Term<LogicInt>): Goal =
  Impl.get_superclass({  x-> x `===` a }, {  x-> x `===` b }, None())
// Put epilogue here 
}}