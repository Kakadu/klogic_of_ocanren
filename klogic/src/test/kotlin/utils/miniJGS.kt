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

@Suppress("UNCHECKED_CAST")
fun <T: Term<T>> None(): LogicOption<T> = utils.None as LogicOption<T>

fun  pause(f: () -> Goal): Goal = { st -> ThunkStream { f()(st) } }

// There are 3 relations
fun <ID : Term<ID>> dummy(typ: Term<Jtype<ID>>): Goal =
conde(freshTypedVars { a: Term<Jtype<ID>> -> (typ `===` Array_(a)) },
      freshTypedVars { a: Term<ID>, b: Term<LogicList<Targ<Jtype<ID>>>> ->
      (typ `===` Class_(a, b)) },
      freshTypedVars { a: Term<ID>, b: Term<PeanoLogic>, c: Term<Jtype<ID>>,
        d: Term<LogicOption<Jtype<ID>>> ->
      (typ `===` Var(a, b, c, d)) })
fun <ID : Term<ID>> substitute_typ(subst: (Term<LogicList<Targ<Jtype<ID>>>>) -> Term<Goal>,
q0: (Term<Jtype<ID>>) -> Term<Goal>, q30: Term<Jtype<ID>>): Goal =
freshTypedVars { q3: Term<Jtype<ID>> ->
and(q0(q3),
    conde(freshTypedVars { typ: Term<Jtype<ID>>, q4: Term<Jtype<ID>> ->
          and(q3 `===` Array_(typ),
              q30 `===` Array_(q4),
              substitute_typ(subst, {  eta-> typ `===` eta }, q4))
          },
          freshTypedVars { id: Term<ID>,
            args: Term<LogicList<Targ<Jtype<ID>>>>,
            q8: Term<LogicList<Targ<Jtype<ID>>>> ->
          and(q3 `===` Class_(id, args),
              q30 `===` Class_(id, q8),
              List_HO_map({  a,  b-> substitute_arg(subst, a, b) },
              {  eta-> eta `===` args }, q8))
          },
          freshTypedVars { id: Term<ID>,
            args: Term<LogicList<Targ<Jtype<ID>>>>,
            q13: Term<LogicList<Targ<Jtype<ID>>>> ->
          and(q3 `===` Interface(id, args),
              q30 `===` Interface(id, q13),
              List_HO_map({  a,  b-> substitute_arg(subst, a, b) },
              {  eta-> eta `===` args }, q13))
          },
          freshTypedVars { typs: Term<LogicList<Jtype<ID>>>,
            q17: Term<LogicList<Jtype<ID>>> ->
          and(q3 `===` Intersect(typs),
              q30 `===` Intersect(q17),
              List_HO_map({  a,  b-> substitute_typ(subst, a, b) },
              {  eta-> eta `===` typs }, q17))
          },
          pause { and(q3 `===` Null(/* Unit */),
                      q30 `===` Null(/* Unit */))
          }))
}
fun <ID : Term<ID>> substitute_arg(subst: (Term<LogicList<Targ<Jtype<ID>>>>) -> Term<Goal>,
q34: (Term<Targ<Jtype<ID>>>) -> Term<Goal>,
q63: Term<Targ<Jtype<ID>>>): Goal =
freshTypedVars { q37: Term<Targ> ->
and(q34(q37),
    conde(freshTypedVars { q38: Term<ID>, index: Term<PeanoLogic>,
            q39: Term<Jtype<ID>>, q40: Term<LogicOption<Jtype<ID>>> ->
          and(q37 `===` Type(Var(q38, index, q39, q40)),
              List_HO_nth(subst, {  eta-> eta `===` index }, q63))
          },
          freshTypedVars { typ: Term<Jtype<ID>>, q48: Term<Jtype<ID>> ->
          and(q37 `===` Type(typ),
              q63 `===` Type(q48),
              substitute_typ(subst, {  eta-> typ `===` eta }, q48))
          },
          pause { and(q37 `===` Wildcard(None()),
                      q63 `===` Wildcard(None()))
          },
          freshTypedVars { p: Term<Polarity>, typ: Term<Jtype<ID>>,
            q58: Term<Polarity>, q59: Term<Jtype<ID>> ->
          and(q37 `===` Wildcard(Some(LogicPair(p, typ))),
              q63 `===` Wildcard(Some(LogicPair(q58, q59))),
              p `===` q58,
              OCanren.=/=(q37, Wildcard(None())),
              substitute_typ(subst, {  eta-> typ `===` eta }, q59))
          }))
}
// Put epilogue here 
