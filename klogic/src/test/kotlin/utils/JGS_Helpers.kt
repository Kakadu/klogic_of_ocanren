// Autogenerated file
@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName"
  , "PropertyName", "ClassName", "LocalVariableName", "SpellCheckingInspection"
  , "PARAMETER_NAME_CHANGED_ON_OVERRIDE", "NAME_SHADOWING"
  )

package utils.JGS

import org.klogic.core.*
import org.klogic.utils.terms.*
import utils.LogicInt
import utils.Some
import utils.None
import utils.LogicOption

//context(RelationalContext)
//fun  pause(f: () -> Goal): Goal = { st -> ThunkStream { f()(st) } }

//context(RelationalContext)
//fun <A: Term<A>> wc(f : (Term<A>) -> Goal ) : Goal = success

// There are 1 relations
context(RelationalContext)
fun  only_classes_interfaces_and_arrays(q: Term<Jtype<LogicInt>>): Goal =
  pause { and(q `!==` Null(),
              (q `!==` Intersect(wildcard())),
              (q `!==` Var(wildcard() wildcard() wildcard() wildcard())))// Put epilogue here 

  }

