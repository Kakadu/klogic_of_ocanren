open OCanren

[@@@ocaml.warning "-32-33"]

type jtype_injected = int OCanren.ilogic
type decl_injected = int OCanren.ilogic

[@@@klogic.preamble
{|// Autogenerated file
@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName"
  , "PropertyName", "ClassName", "LocalVariableName"
  )

package utils.JGS

import org.klogic.core.*
import org.klogic.utils.terms.LogicList
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Nil.nilLogicList
import org.klogic.utils.terms.plus
import org.klogic.utils.terms.PeanoLogicNumber
import org.klogic.utils.terms.NextNaturalNumber
import org.klogic.utils.terms.ZeroNaturalNumber
import org.klogic.utils.terms.LogicPair
import utils.LogicInt
import utils.Some
import utils.None
import utils.LogicOption
//import utils.None

typealias Decl = LogicInt
typealias JType = LogicInt

@Suppress("UNCHECKED_CAST")
fun <T: Term<T>> None(): LogicOption<T> = utils.None as LogicOption<T>

fun  pause(f: () -> Goal): Goal = { st -> ThunkStream { f()(st) } }
@Suppress("UNUSED_PARAMETER")
fun <A: Term<A>> wc(f : (Term<A>) -> Goal ) : Goal = success
|}]

[@@@klogic.epilogue {|// Put epilogue here |}]

(*  *)
[@@@klogic.ident.mangle
[ "OCanren.Std.pair", "LogicPair"
; "OCanren.Std.some", "Some"
; "Targ.wildcard", "Wildcard"
; "Targ.type_", "Type"
; "Jtype.class_", "Class_"
; "Jtype.array", "Array_"
; "Jtype.var", "Var"
; "Jtype.interface", "Interface"
; "Jtype.intersect", "Intersect"
; "Jtype.null", "Null"
; "List.HO.nth", "list_ho_nth"
; "List.HO.map", "list_ho_map"
; "OCanren.Std.Nat.zero", "ZeroNaturalNumber"
; "OCanren.Std.Nat.succ", "NextNaturalNumber"
; "", ""
]]
(*  *)

[@@@klogic.type.mangle
[ "int OCanren.ilogic OCanren.Std.List.injected", "Term<LogicList<LogicInt>>"
; "string OCanren.ilogic OCanren.Std.List.injected", "Term<LogicList<LogicString>>"
; "int OCanren__.Logic.ilogic", "Term<LogicInt>"
; "int OCanren.ilogic", "LogicInt"
; "string OCanren__.Logic.ilogic", "LogicString"
  (* ; ( "(int OCanren__.Logic.ilogic, int OCanren__.Logic.ilogic \
     OCanren.Std.List.injected)OCanren.Std.List.t OCanren__.Logic.ilogic"
  , "Term<LogicList<LogicInt>>" )
; ( "(int OCanren.ilogic, int OCanren.ilogic \
     OCanren.Std.List.injected)OCanren.Std.List.t OCanren__.Logic.ilogic"
  , "Term<LogicList<LogicInt>>" ) *)
; "jtype_injected", "JType"
; "decl_injected", "Decl"
; "Polarity.t ilogic", "Polarity"
; "jtype_injected OCanren.Std.Option.injected", "Term<LogicOption<JType>>"
; "OCanren.goal", "Goal"
; "Targ.injected", "Jarg"
; "Jtype.injected", "Jtype"
; "Polarity.injected", "Polarity"
; "Polarity.t", "Polarity"
; "OCanren.Std.Pair.injected", "LogicPair"
; "OCanren.Std.Nat.injected", "PeanoLogicNumber"
; "OCanren.Std.Option.injected", "LogicOption"
  (* ; ( "('id OCanren.ilogic, 'id OCanren.ilogic Jtype.injected Targ.injected \
     OCanren.Std.List.injected, OCanren.Std.Nat.injected, 'id OCanren.ilogic \
     Jtype.injected, 'id OCanren.ilogic Jtype.injected OCanren.Std.Option.injected, 'id \
     OCanren.ilogic Jtype.injected OCanren.Std.List.injected)Jtype.t \
     OCanren__.Logic.ilogic"
  , "FUCK" ) *)
]]

(* let conso1 : int ilogic Std.List.injected -> goal =
 fun xs -> fresh (h tl) (xs === Std.List.cons h tl)
;; *)

(* let nilo1 : int ilogic Std.List.injected -> goal = fun xs -> xs === Std.List.nil () *)
(* let nilo2 : int ilogic Std.List.injected -> goal = fun xs -> xs =/= Std.List.cons __ __ *)

(* module type CT = sig
  val decl_by_id : (int ilogic -> OCanren.goal) -> decl_injected -> OCanren.goal

  val get_superclass
    :  (int ilogic -> OCanren.goal)
    -> (int ilogic -> OCanren.goal)
    -> jtype_injected Std.Option.injected
    -> OCanren.goal

  (* val object_t : jtype_injected -> OCanren.goal
     val cloneable_t : jtype_injected -> OCanren.goal
     val serializable_t : jtype_injected -> OCanren.goal *)
  val new_var : (int OCanren.ilogic -> OCanren.goal) -> int ilogic -> OCanren.goal
end

module type STUFF = sig end

module Stuff (Impl : CT) : STUFF = struct
  let not_a_superclass : int ilogic -> int ilogic -> goal =
   fun a b -> Impl.get_superclass (fun x -> x === a) (fun x -> x === b) (Std.none ())
 ;;
end *)

(* let rec list_ho_forall :
          'a.
          (('a ilogic -> goal) -> bool ilogic -> goal)
          -> ('a ilogic Std.List.injected -> goal)
          -> bool ilogic
          -> goal
  =
 fun fcond fxs rez ->
  fresh
    xs
    (fxs xs)
    (conde
       [ xs === Std.nil () &&& (rez === !!true)
       ; fresh
           (h tl hrez)
           (xs === Std.List.cons h tl)
           (fcond (fun eta -> eta === h) hrez)
           (conde
              [ hrez === !!true &&& list_ho_forall fcond (fun eta -> eta === tl) rez
              ; hrez === !!false &&& (rez === !!false)
              ])
       ])
;; *)

let rec list_ho_map
  :  (('a ilogic -> goal) -> 'b ilogic -> goal) -> ('a ilogic Std.List.injected -> goal)
  -> 'b ilogic Std.List.injected -> goal
  =
 fun f lst ys ->
  fresh
    xs
    (lst xs)
    (conde
       [ xs === Std.nil () &&& (ys === Std.nil ())
       ; fresh
           (h tl tmph tmptl)
           (xs === Std.List.cons h tl)
           (ys === Std.(tmph % tmptl))
           (f (fun eta -> eta === h) tmph)
           (list_ho_map f (fun eta -> eta === tl) tmptl)
       ])
;;

let rec list_ho_nth
  :  ('b ilogic Std.List.injected -> goal) -> (Std.Nat.injected -> goal) -> 'b ilogic
  -> goal
  =
 fun hoxs hon rez ->
  fresh
    (xs n)
    (hoxs xs)
    (hon n)
    (conde
       [ fresh tl (n === Std.Nat.zero) (xs === Std.List.cons rez tl)
       ; fresh
           (prev h tl)
           (n === Std.Nat.succ prev)
           (xs === Std.List.cons h tl)
           (list_ho_nth (fun eta -> eta === tl) (fun eta -> eta === prev) rez)
         (* ; xs === Std.nil () &&& failure *)
       ])
;;

(* let rec list_ho_fold_left2 f acc l1 l2 q223 =
  fresh
    (q209 q205 q206)
    (q209 === Std.pair q205 q206)
    (l1 q205)
    (l2 q206)
    (conde
       [ q209 === Std.pair !!OCanren.Std.List.Nil !!OCanren.Std.List.Nil &&& acc q223
       ; fresh
           (hd1 tl1 hd2 tl2)
           (q209
            === Std.pair
                  !!(OCanren.Std.List.Cons (hd1, tl1))
                  !!(OCanren.Std.List.Cons (hd2, tl2)))
           (list_ho_fold_left2
              f
              (f acc (fun q210 -> hd1 === q210) (fun q212 -> hd2 === q212))
              (fun q211 -> tl1 === q211)
              (fun q213 -> tl2 === q213)
              q223)
       ; failure
       ])
;; *)

module Polarity = struct
  [%%distrib
  type nonrec ground =
    | Extends
    | Super
  [@@deriving gt ~options:{ show; fmt; gmap }]]
end
[@@skip_from_klogic]

module Targ = struct
  [%%distrib
  type nonrec 'jtype ground =
    | Type of 'jtype
    | Wildcard of (Polarity.ground * 'jtype) Std.Option.ground
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let type_ t : _ ilogic injected = !!(Type t)
  let wildcard t : _ injected = !!(Wildcard t)
end
[@@skip_from_klogic]

module Jtype = struct
  [%%distrib
  type 'id ground =
    | Array of 'id ground
    | Class of 'id * 'id ground Targ.ground Std.List.ground
    | Interface of 'id * 'id ground Targ.ground Std.List.ground
    | Var of
        { id : 'id
        ; index : Std.Nat.ground
        ; upb : 'id ground
        ; lwb : 'id ground Std.Option.ground
        }
    | Null
    | Intersect of 'id ground Std.List.ground
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let array a : _ injected = !!(Array a)
  let class_ a b : _ injected = !!(Class (a, b))
  let interface a b : _ injected = !!(Interface (a, b))
  let var id index upb lwb : _ injected = !!(Var { id; index; upb; lwb })
  let intersect a : _ injected = !!(Intersect a)
  let null () : _ injected = !!Null
end
[@@skip_from_klogic]

open Jtype
open Targ
(*
let dummy : 'id ilogic Jtype.injected -> goal =
 fun typ ->
  (* typ === typ *)
  conde
    [ fresh a (typ === array a)
    ; fresh (a b) (typ === class_ a b)
    ; fresh (a b c d) (typ === var a b c d)
    ]
;; *)

let rec substitute_typ :
          'id.
          ('id ilogic Jtype.injected Targ.injected Std.List.injected -> goal)
          -> ('id ilogic Jtype.injected -> goal)
          -> 'id ilogic Jtype.injected
          -> OCanren.goal
  =
 fun subst q0 q30 ->
  fresh
    q3
    (q0 q3)
    (conde
       [ fresh
           (typ q4)
           (q3 === array typ)
           (q30 === array q4)
           (substitute_typ subst (fun eta -> typ === eta) q4)
       ; fresh
           (id args q8)
           (q3 === class_ id args)
           (q30 === class_ id q8)
           (List.HO.map
              (fun a b -> substitute_arg subst a b)
              (fun eta -> eta === args)
              q8)
       ; fresh
           (id args q13)
           (q3 === interface id args)
           (q30 === interface id q13)
           (List.HO.map
              (fun a b -> substitute_arg subst a b)
              (fun eta -> eta === args)
              q13)
       ; fresh
           (typs q17)
           (q3 === intersect typs)
           (q30 === intersect q17)
           (List.HO.map
              (fun a b -> substitute_typ subst a b)
              (fun eta -> eta === typs)
              q17)
       ; fresh () (q3 === null ()) (q30 === null ())
       ])

and substitute_arg :
      'id.
      ('id ilogic Jtype.injected Targ.injected Std.List.injected -> goal)
      -> ('id ilogic Jtype.injected Targ.injected -> goal)
      -> 'id ilogic Jtype.injected Targ.injected
      -> goal
  =
 fun subst q34 q63 ->
  fresh
    q37
    (q34 q37)
    (conde
       [ fresh
           (q38 index q39 q40)
           (q37 === type_ (var q38 index q39 q40))
           (List.HO.nth subst (fun eta -> eta === index) q63)
       ; fresh
           (typ q48)
           (q37 === type_ typ)
           (q63 === type_ q48)
           (* (q37 =/= type_ (var __ __ __ __)) *)
           (substitute_typ subst (fun eta -> typ === eta) q48)
       ; fresh
           ()
           (q37 === wildcard (Std.none ()))
           (q63 === wildcard (Std.none ()))
           (q37 =/= type_ __)
           (q37 =/= type_ (var __ __ __ __))
       ; fresh
           (p typ q58 q59)
           (q37 === wildcard (Std.some (Std.pair p typ)))
           (q63 === wildcard (Std.some (Std.pair q58 q59)))
           (p === q58)
           (q37 =/= wildcard (Std.none ()))
           (q37 =/= type_ __)
           (* (q37 =/= type_ (var __ __ __ __)) *)
           (substitute_typ subst (fun eta -> typ === eta) q59)
       ])
;;

module type HIGH_ORDER = sig
  val decl_by_id : (int ilogic -> OCanren.goal) -> decl_injected -> OCanren.goal

  val get_superclass
    :  (int ilogic -> OCanren.goal)
    -> (int ilogic -> OCanren.goal)
    -> int ilogic Jtype.injected Std.Option.injected
    -> OCanren.goal

  val object_t : jtype_injected -> OCanren.goal
  val cloneable_t : jtype_injected -> OCanren.goal
  val serializable_t : jtype_injected -> OCanren.goal
  val new_var : int ilogic -> OCanren.goal
end

module type CLASS_TABLE = sig
  module HO : HIGH_ORDER

  (* val ( <-< )
    :  (jtype_injected -> OCanren.goal)
    -> (jtype_injected -> OCanren.goal)
    -> bool ilogic
    -> OCanren.goal *)
end

module type VERIFIER = sig
  val appo : ('a ilogic -> goal) -> 'a ilogic -> goal
end

module Verifier (CT : CLASS_TABLE) : VERIFIER = struct
  let appo : ('a ilogic -> goal) -> 'a ilogic -> goal = fun f x -> f x
  (*
  open Polarity

  let rec ( <=< ) ( <-< ) ta tb q97 =
    fresh
      (q71 q67 q68)
      (q71 === Std.pair q67 q68)
      (ta q67)
      (tb q68)
      (conde
         [ fresh
             (t s)
             (q71
              === Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Polarity.Extends t)))
                    !!(Wildcard !!(Some (Std.pair !!Extends s))))
             (( <-< ) (( === ) t) (( === ) s) q97)
         ; fresh
             t
             (q71
              === Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends t)))
                    !!(Wildcard !!None))
             (q97 === !!true)
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
         ; fresh
             (t s)
             (q71
              === Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super t)))
                    !!(Wildcard !!(Some (Std.pair !!Super s))))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!None))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
             (( <-< ) (( === ) s) (( === ) t) q97)
         ; fresh
             t
             (q71
              === Std.pair !!(Wildcard !!(Some (Std.pair !!Super t))) !!(Wildcard !!None)
             )
             (q97 === !!true)
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super __)))
                    !!(Wildcard !!(Some (Std.pair !!Super __))))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!None))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
         ; fresh
             (t o)
             (fresh
                (q82 q83)
                (q71
                 === Std.pair
                       !!(Wildcard !!(Some (Std.pair !!Super t)))
                       !!(Wildcard !!(Some (Std.pair !!Extends o))))
                (o === q82)
                (q71
                 =/= Std.pair
                       !!(Wildcard !!(Some (Std.pair !!Super __)))
                       !!(Wildcard !!None))
                (q71
                 =/= Std.pair
                       !!(Wildcard !!(Some (Std.pair !!Super __)))
                       !!(Wildcard !!(Some (Std.pair !!Super __))))
                (q71
                 =/= Std.pair
                       !!(Wildcard !!(Some (Std.pair !!Extends __)))
                       !!(Wildcard !!None))
                (q71
                 =/= Std.pair
                       !!(Wildcard !!(Some (Std.pair !!Extends __)))
                       !!(Wildcard !!(Some (Std.pair !!Extends __))))
                (CT.HO.object_t q83)
                (conde
                   [ fresh () (q82 === q83) (q97 === !!true)
                   ; fresh () (q97 === !!false) (q82 =/= q83)
                   ]))
         ; fresh
             (t1 t2)
             (conde
                [ q71 === Std.pair !!(Type t1) !!(Type t2)
                ; q71
                  === Std.pair !!(Type t1) !!(Wildcard !!(Some (Std.pair !!Extends t2)))
                ; q71 === Std.pair !!(Type t1) !!(Wildcard !!(Some (Std.pair !!Super t2)))
                ])
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
             (q71
              =/= Std.pair !!(Wildcard !!(Some (Std.pair !!Super __))) !!(Wildcard !!None)
             )
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super __)))
                    !!(Wildcard !!(Some (Std.pair !!Super __))))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!None))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
             (conde
                [ fresh () (t1 === t2) (q97 === !!true)
                ; fresh () (q97 === !!false) (t1 =/= t2)
                ])
         ; fresh
             ()
             (q97 === !!false)
             (q71 =/= Std.pair !!(Type __) !!(Type __))
             (q71 =/= Std.pair !!(Type __) !!(Wildcard !!(Some (Std.pair !!Extends __))))
             (q71 =/= Std.pair !!(Type __) !!(Wildcard !!(Some (Std.pair !!Super __))))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
             (q71
              =/= Std.pair !!(Wildcard !!(Some (Std.pair !!Super __))) !!(Wildcard !!None)
             )
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Super __)))
                    !!(Wildcard !!(Some (Std.pair !!Super __))))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!None))
             (q71
              =/= Std.pair
                    !!(Wildcard !!(Some (Std.pair !!Extends __)))
                    !!(Wildcard !!(Some (Std.pair !!Extends __))))
         ])

  and class_int_sub
    :  ((int ilogic -> goal) -> (int ilogic -> goal) -> bool ilogic -> goal) -> int ilogic
    -> _ (* (int ilogic Targ.injected Std.List.injected -> goal) *)
    -> (int ilogic -> goal)
    -> (* -> ((Polarity.t ilogic, int ilogic) Std.Pair.injected -> goal)  *)
       _
    -> bool ilogic -> goal
    =
   fun ( <-< ) (id_a as q232) targs_a id_b targs_b q235 ->
    fresh
      (q233 q208)
      (id_b q233)
      (conde
         [ fresh () (q232 === q233) (q208 === !!true)
         ; fresh () (q208 === !!false) (q232 =/= q233)
         ])
      (conde
         [ fresh
             ()
             (q208 === !!true)
             (list_ho_fold_left2
                (fun f ta tb q228 ->
                  fresh
                    q226
                    (f q226)
                    (conde
                       [ fresh () (q226 === !!false) (q228 === !!false)
                       ; fresh () (q226 === !!true) (( <=< ) ( <-< ) ta tb q228)
                       ]))
                (( === ) !!true)
                targs_a
                targs_b
                q235)
         ; fresh
             q211
             (q208 === !!false)
             (CT.HO.get_superclass (( === ) q232) (( === ) q233) q211)
             (conde
                [ fresh
                    (q212 targs_b' q213 q217 q218)
                    (conde
                       [ q211 === !!(Some !!(Class (q212, targs_b')))
                       ; q211 === !!(Some !!(Interface (q213, targs_b')))
                       ])
                    (targs_b q217)
                    (list_ho_map (substitute_arg targs_a) (( === ) targs_b') q218)
                    (conde
                       [ fresh () (q217 === q218) (q235 === !!true)
                       ; fresh () (q235 === !!false) (q217 =/= q218)
                       ])
                ; fresh () (q211 === !!None) (q235 === !!false)
                ])
         ])

  and capture_conversion ( <-< ) id targs q205 =
    fresh
      q206
      (targs q206)
      (let params q98 =
         fresh
           (q99 q100 q101 q102)
           (CT.HO.decl_by_id id q99)
           (conde
              [ q99 === !!(C (ctor_cdecl q98 q100 q101))
              ; q99 === !!(I (ctor_idecl q98 q102))
              ])
       in
       let raw =
         List.HO.mapi
           (fun i q107 q133 ->
             fresh
               (q134 q110)
               (i q134)
               (q107 q110)
               (conde
                  [ fresh t (q110 === !!(Type t)) (q133 === !!(CC_type t))
                  ; fresh
                      (q114 q117)
                      (q110 === !!(Wildcard !!None))
                      (q133
                       === !!(CC_var (q114, q134, !!(CC_subst q117), !!(Some !!Null))))
                      (CT.HO.new_var (( === ) !!()) q114)
                      (List.HO.nth params (( === ) q134) q117)
                  ; fresh
                      (t q119 q122)
                      (q110 === !!(Wildcard !!(Some (Std.pair !!Super t))))
                      (q133 === !!(CC_var (q119, q134, !!(CC_subst q122), !!(Some t))))
                      (CT.HO.new_var (( === ) !!()) q119)
                      (List.HO.nth params (( === ) q134) q122)
                  ; fresh
                      (t q126 q130)
                      (q110 === !!(Wildcard !!(Some (Std.pair !!Extends t))))
                      (q133
                       === !!(CC_var (q126, q134, !!(CC_inter (t, q130)), !!(Some !!Null)))
                      )
                      (CT.HO.new_var (( === ) !!()) q126)
                      (List.HO.nth params (( === ) q134) q130)
                  ]))
           (( === ) q206)
       in
       let subst =
         List.HO.map
           (fun q136 q137 ->
             fresh
               q138
               (q136 q138)
               (conde
                  [ fresh t (q138 === !!(CC_type t)) (q137 === !!(Type t))
                  ; fresh
                      (id i q142 q143)
                      (q138 === !!(CC_var (id, i, q142, q143)))
                      (q137 === !!(Type (var id i !!Null !!None)))
                  ]))
           raw
       in
       let targs =
         List.HO.map
           (fun q151 q152 ->
             fresh
               q153
               (q151 q153)
               (conde
                  [ fresh
                      (t q154)
                      (q153 === !!(CC_type t))
                      (q152 === !!(Type q154))
                      (substitute_typ subst (( === ) t) q154)
                  ; fresh
                      (id i p lwb q159)
                      (q153 === !!(CC_var (id, i, !!(CC_subst p), lwb)))
                      (q152 === !!(Type (var id i q159 lwb)))
                      (substitute_typ subst (( === ) p) q159)
                  ; fresh
                      (id i t p lwb q168 q170)
                      (q153 === !!(CC_var (id, i, !!(CC_inter (t, p)), lwb)))
                      (q152 === !!(Type (var id i q168 lwb)))
                      (substitute_typ subst (( === ) p) q170)
                      (conde
                         [ fresh
                             ts
                             (q170 === !!(Intersect ts))
                             (q168 === !!(Intersect (Std.( % ) t ts)))
                         ; fresh
                             ()
                             (q168 === !!(Intersect (Std.list Fun.id [ t; q170 ])))
                             (q170 =/= !!(Intersect __))
                         ])
                  ]))
           raw
       in
       fresh
         q186
         (list_ho_for_all
            (fun q191 q192 ->
              fresh
                q193
                (q191 q193)
                (conde
                   [ fresh
                       (q194 q195 upb lwb)
                       (q193 === !!(Type (var q194 q195 upb !!(Some lwb))))
                       (( <-< ) (( === ) lwb) (( === ) upb) q192)
                   ; fresh
                       ()
                       (q192 === !!true)
                       (q193 =/= !!(Type (var __ __ __ !!(Some __))))
                   ]))
            targs
            q186)
         (conde
            [ fresh q189 (q186 === !!true) (q205 === !!(Some q189)) (targs q189)
            ; fresh () (q186 === !!false) (q205 === !!None)
            ]))

  and ( -<- ) ( <-< ) ta tb res =
    fresh
      (ta_val tb_val)
      (ta ta_val)
      (tb tb_val)
      (let ( -<- ) = ( -<- ) ( <-< ) in
       fresh
         ()
         (conde
            [ fresh
                (id_a targs_a q243)
                (ta_val === !!(Class (id_a, targs_a)))
                (capture_conversion ( <-< ) (( === ) id_a) (( === ) targs_a) q243)
                (conde
                   [ fresh () (q243 === !!None) (res === !!false)
                   ; fresh
                       (targs_a q246)
                       (q243 === !!(Some targs_a))
                       (q246 === tb_val)
                       (conde
                          [ fresh
                              (id_b targs_b)
                              (conde
                                 [ q246 === !!(Interface (id_b, targs_b))
                                 ; q246 === !!(Class (id_b, targs_b))
                                 ])
                              (class_int_sub
                                 ( <-< )
                                 id_a
                                 (( === ) targs_a)
                                 (( === ) id_b)
                                 (( === ) targs_b)
                                 res)
                          ; fresh
                              (q249 q250 q251 typ)
                              (fresh
                                 ()
                                 (q246 === var q249 q250 q251 !!(Some typ))
                                 (q246 =/= !!(Interface (__, __)))
                                 (q246 =/= !!(Class (__, __)))
                                 (conde
                                    [ fresh () (typ === ta_val) (res === !!true)
                                    ; fresh () (res === !!false) (typ =/= ta_val)
                                    ]))
                          ; fresh
                              ()
                              (res === !!false)
                              (q246 =/= var __ __ __ !!(Some __))
                              (q246 =/= !!(Interface (__, __)))
                              (q246 =/= !!(Class (__, __)))
                          ])
                   ])
            ; fresh
                (id_a targs_a q271)
                (ta_val === !!(Interface (id_a, targs_a)))
                (capture_conversion ( <-< ) (( === ) id_a) (( === ) targs_a) q271)
                (conde
                   [ fresh () (q271 === !!None) (res === !!false)
                   ; fresh
                       targs_a
                       (q271 === !!(Some targs_a))
                       (conde
                          [ fresh
                              (id_b targs_b)
                              (conde
                                 [ tb_val === !!(Class (id_b, targs_b))
                                 ; tb_val === !!(Interface (id_b, targs_b))
                                 ])
                              (class_int_sub
                                 ( <-< )
                                 id_a
                                 (( === ) targs_a)
                                 (( === ) id_b)
                                 (( === ) targs_b)
                                 res)
                          ; fresh
                              (q289 q290 q291 typ)
                              (tb_val === var q289 q290 q291 !!(Some typ))
                              (tb_val =/= !!(Class (__, __)))
                              (tb_val =/= !!(Interface (__, __)))
                              (conde
                                 [ fresh () (typ === ta_val) (res === !!true)
                                 ; fresh () (res === !!false) (typ =/= ta_val)
                                 ])
                          ; fresh
                              ()
                              (res === !!false)
                              (tb_val =/= var __ __ __ !!(Some __))
                              (tb_val =/= !!(Class (__, __)))
                              (tb_val =/= !!(Interface (__, __)))
                          ])
                   ])
            ; fresh
                (ta q310 q352 q353)
                (ta_val === !!(Array ta))
                (ta === q352)
                (CT.HO.object_t q353)
                (conde
                   [ fresh () (q352 === q353) (q310 === !!true)
                   ; fresh () (q310 === !!false) (q352 =/= q353)
                   ])
                (conde
                   [ fresh
                       (q318 q348 q329 q330)
                       (q310 === !!true)
                       (q329 === tb_val)
                       (CT.HO.object_t q330)
                       (conde
                          [ fresh () (q329 === q330) (q348 === !!true)
                          ; fresh () (q348 === !!false) (q329 =/= q330)
                          ])
                       (conde
                          [ fresh () (q348 === !!true) (q318 === !!true)
                          ; fresh
                              (q344 q335)
                              (q348 === !!false)
                              (CT.HO.cloneable_t q335)
                              (conde
                                 [ fresh () (tb_val === q335) (q344 === !!true)
                                 ; fresh () (q344 === !!false) (tb_val =/= q335)
                                 ])
                              (conde
                                 [ fresh () (q344 === !!true) (q318 === !!true)
                                 ; fresh
                                     q340
                                     (q344 === !!false)
                                     (CT.HO.serializable_t q340)
                                     (conde
                                        [ fresh () (tb_val === q340) (q318 === !!true)
                                        ; fresh () (q318 === !!false) (tb_val =/= q340)
                                        ])
                                 ])
                          ])
                       (conde
                          [ fresh () (q318 === !!true) (res === !!true)
                          ; fresh
                              ()
                              (q318 === !!false)
                              (conde
                                 [ fresh
                                     tb
                                     (tb_val === !!(Array tb))
                                     (( -<- ) (( === ) ta) (( === ) tb) res)
                                 ; fresh
                                     q323
                                     (tb_val === q323)
                                     (res === !!false)
                                     (tb_val =/= !!(Array __))
                                 ])
                          ])
                   ; fresh
                       ()
                       (q310 === !!false)
                       (conde
                          [ fresh
                              tb
                              (tb_val === !!(Array tb))
                              (( -<- ) (( === ) ta) (( === ) tb) res)
                          ; fresh
                              q315
                              (tb_val === q315)
                              (res === !!false)
                              (tb_val =/= !!(Array __))
                          ])
                   ])
            ; fresh
                ts
                (ta_val === !!(Intersect ts))
                (List.HO.mem (( === ) tb_val) (( === ) ts) res)
            ; fresh
                (q357 q358 q359 typ)
                (ta_val === var q357 q358 typ q359)
                (conde
                   [ fresh () (typ === tb_val) (res === !!true)
                   ; fresh () (res === !!false) (typ =/= tb_val)
                   ])
            ; fresh
                q373
                (ta_val === !!Null)
                (q373 === !!Null)
                (conde
                   [ fresh () (tb_val === q373) (res === !!false)
                   ; fresh () (res === !!true) (tb_val =/= q373)
                   ])
            ]))
  ;;
  *)
end

(* let rec ( <=< )
  :  (int ilogic -> int ilogic -> int ilogic) -> (int ilogic -> int ilogic -> int ilogic)
  -> int ilogic -> int ilogic -> goal
  =
 fun ( #%< ) ( #$% ) x y ->
  conde
    [ x #%< y === x #$% y
    ; ( <=< ) (fun ( &?& ) ( ~*^ ) -> ( &?& ) #%< ( ~*^ )) ( #$% ) x y
    ]
;;

module type Test = sig
  val ( %%% ) : int ilogic -> int ilogic
end

module type STUFF = sig end

module Stuff (CT : Test) : STUFF = struct
  let eval : int ilogic -> goal = fun x -> x === CT.( %%% ) x
end *)
