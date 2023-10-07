open OCanren

[@@@ocaml.warning "-32-33"]

[@@@klogic.preamble
{|// Autogenerated file
@file:Suppress("FunctionName", "NonAsciiCharacters", "TestFunctionName"
  , "PropertyName", "ClassName", "LocalVariableName", "SpellCheckingInspection"
  , "PARAMETER_NAME_CHANGED_ON_OVERRIDE", "NAME_SHADOWING"
  )

package utils.JGS

import org.klogic.core.*
import org.klogic.utils.terms.*
import org.klogic.utils.terms.LogicBool.Companion.toLogicBool
import org.klogic.utils.terms.LogicList.Companion.logicListOf
import org.klogic.utils.terms.Nil.nilLogicList
import utils.LogicInt
import utils.LogicInt.Companion.toLogic
import utils.Some
import utils.None
import utils.LogicOption
//import utils.None

@Suppress("UNCHECKED_CAST")
fun <T: Term<T>> None(): LogicOption<T> = utils.None as LogicOption<T>

context(RelationalContext)
fun  pause(f: () -> Goal): Goal = { st -> ThunkStream { f()(st) } }

context(RelationalContext)
fun <A: Term<A>> wc(f : (Term<A>) -> Goal ) : Goal = success
|}]

[@@@klogic.epilogue {|// Put epilogue here |}]

(*  *)
[@@@klogic.ident.mangle
[ "CC_type.cc_var", "CC_var"
; "CC_type.cc_type", "CC_type"
; "CC_subst.cc_subst", "CC_subst"
; "Jtype.class_", "Class_"
; "Jtype.array", "Array_"
; "Jtype.var", "Var"
; "Jtype.interface", "Interface"
; "Jtype.intersect", "Intersect"
; "Jtype.null", "Null"
; "Decl.c", "C"
; "Decl.i", "I"
; "OCanren.Std.Nat.zero", "ZeroNaturalNumber"
; "OCanren.Std.Nat.o", "ZeroNaturalNumber"
; "OCanren.Std.Nat.succ", "NextNaturalNumber"
; "OCanren.Std.Nat.s", "NextNaturalNumber"
; "OCanren.Std.pair", "LogicPair"
; "OCanren.Std.some", "Some"
; "Polarity.super", "Super"
; "Polarity.extends", "Extends"
; "Targ.wildcard", "Wildcard"
; "Targ.type_", "Type"
; "", ""
]]
(*  *)

[@@@klogic.type.mangle
[ (* "int OCanren.ilogic OCanren.Std.List.injected", "Term<LogicList<LogicInt>>" *)
  (* ; "string OCanren.ilogic OCanren.Std.List.injected", "Term<LogicList<LogicString>>" *)
  (* ; "int OCanren__.Logic.ilogic", "Term<LogicInt>" *)
  (* ; "int OCanren.ilogic", "LogicInt" *)
  (* ; "bool OCanren.ilogic", "LogicBool" *)
  (* ; "string OCanren__.Logic.ilogic", "LogicString" *)
  (* ; ( "(int OCanren__.Logic.ilogic, int OCanren__.Logic.ilogic \
     OCanren.Std.List.injected)OCanren.Std.List.t OCanren__.Logic.ilogic"
  , "Term<LogicList<LogicInt>>" ) *)
  (* ; ( "(int OCanren.ilogic, int OCanren.ilogic \
     OCanren.Std.List.injected)OCanren.Std.List.t OCanren__.Logic.ilogic"
  , "Term<LogicList<LogicInt>>" ) *)
  (* ; "jtype_injected", "JType" *)
  (* ; "decl_injected", "Decl" *)
  (* ; "Polarity.t ilogic", "Polarity" *)
  (* ; "jtype_injected OCanren.Std.Option.injected", "Term<LogicOption<JType>>" *)
  (* ; "OCanren.goal", "Goal" *)
  (* ; "Polarity.t", "Polarity" *)
  "Targ.injected", "Jarg"
; "Jtype.injected", "Jtype"
; "Polarity.injected", "Polarity"
; "Decl.injected", "Decl"
; "CC_type.injected", "ClosureConversionType"
; "CC_subst.injected", "CC_subst"
; "OCanren.Std.Pair.injected", "LogicPair"
; "OCanren.Std.Nat.injected", "PeanoLogicNumber"
; "OCanren.Std.Option.injected", "LogicOption"
]]

let rec mapo :
   ('a ilogic -> 'b ilogic -> goal)
  -> 'a ilogic Std.List.injected
  -> 'b ilogic Std.List.injected
  -> goal
  =
 fun f l res ->
  let open Std in
  conde
    [ fresh () (l === nil ()) (res === nil ())
    ; fresh
        (l_hd l_tl res_hd res_tl)
        (l === l_hd % l_tl)
        (res === res_hd % res_tl)
        (f l_hd res_hd)
        (mapo f l_tl res_tl)
    ]
;;

let rec mapio_helper :
   (Std.Nat.injected -> 'a ilogic -> 'b ilogic -> goal)
  -> Std.Nat.injected
  -> 'a ilogic Std.List.injected
  -> 'b ilogic Std.List.injected
  -> goal
  =
 fun f i l res ->
  let open Std in
  conde
    [ fresh () (l === nil ()) (res === nil ())
    ; fresh
        (l_hd l_tl res_hd res_tl)
        (l === l_hd % l_tl)
        (res === res_hd % res_tl)
        (f i l_hd res_hd)
        (mapio_helper f (Nat.s i) l_tl res_tl)
    ]
;;

let mapio :
   (Std.Nat.injected -> 'a ilogic -> 'b ilogic -> goal)
  -> 'a ilogic Std.List.injected
  -> 'b ilogic Std.List.injected
  -> goal
  =
 fun f l res -> mapio_helper f Std.Nat.o l res
;;

let rec memo : 'a ilogic -> 'a ilogic Std.List.injected -> bool ilogic -> goal =
 fun e l res ->
  let open Std in
  conde
    [ fresh () (l === nil ()) (res === !!false)
    ; fresh
        (hd tl)
        (l === hd % tl)
        (conde
           [ fresh () (hd === e) (res === !!true); fresh () (hd =/= e) (memo e tl res) ])
    ]
;;

let rec ntho : 'a ilogic Std.List.injected -> Std.Nat.injected -> 'a ilogic -> goal =
 fun l n rez ->
  let open Std in
  fresh
    (hd tl)
    (l === hd % tl)
    (conde
       [ fresh () (n === Nat.o) (hd === rez)
       ; fresh prev (n === Nat.s prev) (ntho tl prev rez)
       ])
;;

let rec for_allo :
  ('a ilogic -> bool ilogic -> goal) -> 'a ilogic Std.List.injected -> bool ilogic -> goal
  =
 fun p l res ->
  let open Std in
  conde
    [ fresh () (l === nil ()) (res === !!true)
    ; fresh
        (hd tl p_res)
        (l === hd % tl)
        (p hd p_res)
        (conde
           [ fresh () (p_res === !!true) (for_allo p tl res)
           ; fresh () (p_res === !!false) (res === !!false)
           ])
    ]
;;

let rec fold_left2o :
   ('a ilogic -> 'b ilogic -> 'c ilogic -> 'a ilogic -> goal)
  -> 'a ilogic
  -> 'b ilogic Std.List.injected
  -> 'c ilogic Std.List.injected
  -> 'a ilogic
  -> goal
  =
 fun f acc l1 l2 res ->
  let open Std in
  conde
    [ fresh () (l1 === nil ()) (l2 === nil ()) (res === acc)
    ; fresh
        (hd1 tl1 hd2 tl2 new_acc)
        (l1 === hd1 % tl1)
        (l2 === hd2 % tl2)
        (f acc hd1 hd2 new_acc)
        (fold_left2o f new_acc tl1 tl2 res)
    ]
;;

module Polarity = struct
  [%%distrib
  type nonrec ground =
    | Extends
    | Super
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let extends () = !!Extends
  let super_ () = !!Super
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

module Decl = struct
  [%%distrib
  type nonrec 'id ground =
    | C of
        { params : 'id Jtype.ground Std.List.ground
        ; super : 'id Jtype.ground
        ; supers : 'id Jtype.ground Std.List.ground
        }
    | I of
        { params : 'id Jtype.ground Std.List.ground
        ; supers : 'id Jtype.ground Std.List.ground
        }
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let cdecl params super supers = !!(C { params; super; supers })
  let idecl params supers = !!(I { params; supers })
end
[@@skip_from_klogic]

module CC_subst = struct
  [%%distrib
  type nonrec 'id ground =
    | CC_inter of 'id Jtype.ground * 'id Jtype.ground
    | CC_subst of 'id Jtype.ground
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let cc_inter x y = !!(CC_inter (x, y))
  let cc_subst x = !!(CC_subst x)
end
[@@skip_from_klogic]

module CC_type = struct
  [%%distrib
  type nonrec 'id ground =
    | CC_type of 'id Jtype.ground
    | CC_var of
        'id * Std.Nat.ground * 'id CC_subst.ground * 'id Jtype.ground Std.Option.ground
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let cc_type t = !!(CC_type t)
  let cc_var x y z t = !!(CC_var (x, y, z, t))
end
[@@skip_from_klogic]

open Jtype
open Targ
open Polarity
open CC_type
open CC_subst

let rec substitute_typ :
          'id.
          'id ilogic Jtype.injected Targ.injected Std.List.injected
          -> 'id ilogic Jtype.injected
          -> 'id ilogic Jtype.injected
          -> goal
  =
 fun subst typ res ->
  conde
    [ fresh
        (param new_param)
        (typ === array param)
        (res === array new_param)
        (substitute_typ subst param new_param)
    ; fresh
        (id args new_args)
        (typ === class_ id args)
        (res === class_ id new_args)
        (mapo (fun targ res -> substitute_arg subst targ res) args new_args)
    ; fresh
        (id args new_args)
        (typ === interface id args)
        (res === interface id new_args)
        (mapo (fun targ res -> substitute_arg subst targ res) args new_args)
    ; fresh
        (typs new_typs)
        (typ === intersect typs)
        (res === intersect new_typs)
        (mapo (fun typ res -> substitute_typ subst typ res) typs new_typs)
    ; fresh () (typ === null ()) (res === null ())
    ]

and substitute_arg :
      'id.
      'id ilogic Jtype.injected Targ.injected Std.List.injected
      -> 'id ilogic Jtype.injected Targ.injected
      -> 'id ilogic Jtype.injected Targ.injected
      -> goal
  =
 fun subst targ res ->
  conde
    [ fresh index (targ === type_ (var __ index __ __)) (ntho subst index res)
    ; fresh
        (typ new_typ)
        (targ === type_ typ)
        (res === type_ new_typ)
        (substitute_typ subst typ new_typ)
    ; fresh () (targ === wildcard (Std.none ())) (res === wildcard (Std.none ()))
    ; fresh
        (p typ new_typ)
        (targ === wildcard (Std.some (Std.pair p typ)))
        (res === wildcard (Std.some (Std.pair p new_typ)))
        (substitute_typ subst typ new_typ)
    ]
;;

module type CLASSTABLE = sig
  val decl_by_id : int ilogic -> int ilogic Decl.injected -> goal

  val get_superclass_by_id :
     int ilogic
    -> int ilogic
    -> int ilogic Jtype.injected Std.Option.injected
    -> goal

  (* TODO: After translation these signature items are functions,
     but they are values in `( -<- )` image *)
  val object_t : int ilogic Jtype.injected [@@klogic_val]
  val cloneable_t : int ilogic Jtype.injected [@@klogic_val]
  val serializable_t : int ilogic Jtype.injected [@@klogic_val]

  (* TODO for KAKADU: unsupported `unit` in class type *)
  val new_var : unit -> int ilogic
end

module type VERIFIER = sig
  val params : int ilogic -> int ilogic Jtype.injected Std.List.injected -> goal

  val raw_helper :
     int ilogic
    -> Std.Nat.injected
    -> int ilogic Jtype.injected Targ.injected
    -> int ilogic CC_type.injected
    -> goal

  val subst_helper :
     int ilogic CC_type.injected
    -> int ilogic Jtype.injected Targ.injected
    -> goal

  val targs_helper :
     int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic CC_type.injected
    -> int ilogic Jtype.injected Targ.injected
    -> goal

  val targs_pred :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected Targ.injected
    -> bool ilogic
    -> goal

  val capture_conversion :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic Jtype.injected Targ.injected Std.List.injected Std.Option.injected
    -> goal

  val ( <=< ) :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected Targ.injected
    -> int ilogic Jtype.injected Targ.injected
    -> bool ilogic
    -> goal

  val class_int_sub :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> bool ilogic
    -> goal

  val ( -<- ) :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected
    -> int ilogic Jtype.injected
    -> bool ilogic
    -> goal
end

(* TODO for KAKADU: reversed order of methods in KLogic image *)
module Verifier (CT : CLASSTABLE) : VERIFIER = struct
  let params : int ilogic -> int ilogic Jtype.injected Std.List.injected -> goal =
   fun id p ->
    fresh
      decl
      (CT.decl_by_id id decl)
      (conde [ decl === Decl.c p __ __; decl === Decl.i p __ ])
 ;;

  let raw_helper :
     int ilogic
    -> Std.Nat.injected
    -> int ilogic Jtype.injected Targ.injected
    -> int ilogic CC_type.injected
    -> goal
    =
   fun id i targ cc_targ ->
    conde
      [ fresh t (targ === type_ t) (cc_targ === cc_type t)
      ; fresh
          (param params_val)
          (targ === wildcard (Std.none ()))
          (cc_targ === cc_var (CT.new_var ()) i (cc_subst param) (Std.some (null ())))
          (params id params_val)
          (ntho params_val i param)
      ; fresh
          (t subst params_val)
          (targ === wildcard (Std.some (Std.pair (super ()) t)))
          (cc_targ === cc_var (CT.new_var ()) i (cc_subst subst) (Std.some t))
          (params id params_val)
          (ntho params_val i subst)
      ; fresh
          (t t2 params_val)
          (targ === wildcard (Std.some (Std.pair (extends ()) t)))
          (cc_targ === cc_var (CT.new_var ()) i (cc_inter t t2) (Std.some (null ())))
          (params id params_val)
          (ntho params_val i t2)
      ]
 ;;

  let subst_helper :
    int ilogic CC_type.injected -> int ilogic Jtype.injected Targ.injected -> goal
    =
   fun raw_element targ ->
    conde
      [ fresh t (raw_element === cc_type t) (targ === type_ t)
      ; fresh
          (id i)
          (raw_element === cc_var id i __ __)
          (targ === type_ (var id i (null ()) (Std.none ())))
      ]
 ;;

  let targs_helper :
     int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic CC_type.injected
    -> int ilogic Jtype.injected Targ.injected
    -> goal
    =
   fun subst cc_typ res ->
    conde
      [ fresh
          (t new_t)
          (cc_typ === cc_type t)
          (res === type_ new_t)
          (substitute_typ subst t new_t)
      ; fresh
          (id i p new_p lwb)
          (cc_typ === cc_var id i (cc_subst p) lwb)
          (res === type_ (var id i new_p lwb))
          (substitute_typ subst p new_p)
      ; fresh
          (id i t p lwb upb new_p)
          (cc_typ === cc_var id i (cc_inter t p) lwb)
          (res === type_ (var id i upb lwb))
          (substitute_typ subst p new_p)
          (conde
             [ fresh ts (new_p === intersect ts) (upb === intersect Std.(t % ts))
             ; fresh
                 ()
                 (* TODO for KAKADU: what about logic list constructor `OCanren.Std.list`? *)
                 (* (upb === intersect (Std.list (fun x -> x) [ t; new_p ])) *)
                 (upb === intersect Std.(t % (new_p % Std.nil ())))
                 (new_p =/= intersect __)
             ])
      ]
 ;;

  let targs_pred :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected Targ.injected
    -> bool ilogic
    -> goal
    =
   fun ( <-< ) targ res ->
    conde
      [ fresh
          (upb lwb)
          (targ === type_ (var __ __ upb (Std.some lwb)))
          (( <-< ) lwb upb res)
      ; fresh () (res === !!true) (targ =/= type_ (var __ __ __ (Std.some __)))
      ]
 ;;

  (* TODO: two useless arguments (they were used in comlete version of `capture_conversion`) *)
  let capture_conversion :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic Jtype.injected Targ.injected Std.List.injected Std.Option.injected
    -> goal
    =
   fun _subtyping _id targs res -> res === Std.some targs
 ;;

  (* TODO: useless argument (it was used in comlete version of `( <=< )` *)
  let ( <=< ) :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected Targ.injected
    -> int ilogic Jtype.injected Targ.injected
    -> bool ilogic
    -> goal
    =
   fun _subtyping type_a type_b res ->
    conde
      [ fresh () (type_a === type_b) (res === !!true)
      ; fresh () (type_a =/= type_b) (res === !!false)
      ]
 ;;

  let class_int_sub :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> int ilogic
    -> int ilogic Jtype.injected Targ.injected Std.List.injected
    -> bool ilogic
    -> goal
    =
   fun ( <-< ) id_a targs_a id_b targs_b res ->
    conde
      [ fresh
          ()
          (id_a === id_b)
          (fold_left2o
             (fun acc ta tb res ->
               conde
                 [ fresh () (acc === !!false) (res === !!false)
                 ; fresh () (acc === !!true) (( <=< ) ( <-< ) ta tb res)
                 ])
             !!true
             targs_a
             targs_b
             res)
      ; fresh
          super_
          (id_a =/= id_b)
          (CT.get_superclass_by_id id_a id_b super_)
          (conde
             [ fresh
                 (targs_b2 new_targs_b2)
                 (conde
                    [ super_ === Std.some (class_ __ targs_b2)
                    ; super_ === Std.some (interface __ targs_b2)
                    ])
                 (mapo
                    (fun arg res -> substitute_arg targs_a arg res)
                    targs_b2
                    new_targs_b2)
                 (conde
                    [ fresh () (targs_b === new_targs_b2) (res === !!true)
                    ; fresh () (res === !!false) (targs_b =/= new_targs_b2)
                    ])
             ; fresh () (super_ === Std.none ()) (res === !!false)
             ])
      ]
 ;;

  let rec ( -<- ) :
     (int ilogic Jtype.injected -> int ilogic Jtype.injected -> bool ilogic -> goal)
    -> int ilogic Jtype.injected
    -> int ilogic Jtype.injected
    -> bool ilogic
    -> goal
    =
   fun ( <-< ) type_a type_b res ->
    conde
      [ fresh
          (id_a targs_a converted)
          (type_a === class_ id_a targs_a)
          (capture_conversion ( <-< ) id_a targs_a converted)
          (conde
             [ fresh () (converted === Std.none ()) (res === !!false)
             ; fresh
                 targs_a
                 (converted === Std.some targs_a)
                 (conde
                    [ fresh
                        (id_b targs_b)
                        (conde
                           [ type_b === interface id_b targs_b
                           ; type_b === class_ id_b targs_b
                           ])
                        (class_int_sub ( <-< ) id_a targs_a id_b targs_b res)
                    ; fresh
                        typ
                        (type_b === var __ __ __ (Std.some typ))
                        (conde
                           [ fresh () (typ === type_a) (res === !!true)
                           ; fresh () (res === !!false) (typ =/= type_a)
                           ])
                    ; fresh
                        ()
                        (res === !!false)
                        (type_b =/= var __ __ __ (Std.some __))
                        (type_b =/= interface __ __)
                        (type_b =/= class_ __ __)
                    ])
             ])
      ; fresh
          (id_a targs_a converted)
          (type_a === interface id_a targs_a)
          (capture_conversion ( <-< ) id_a targs_a converted)
          (conde
             [ fresh () (converted === Std.none ()) (res === !!false)
             ; fresh
                 targs_a
                 (converted === Std.some targs_a)
                 (conde
                    [ fresh
                        (id_b targs_b)
                        (conde
                           [ type_b === class_ id_b targs_b
                           ; type_b === interface id_b targs_b
                           ])
                        (class_int_sub ( <-< ) id_a targs_a id_b targs_b res)
                    ; fresh
                        typ
                        (type_b === var __ __ __ (Std.some typ))
                        (conde
                           [ fresh () (typ === type_a) (res === !!true)
                           ; fresh () (res === !!false) (typ =/= type_a)
                           ])
                    ; fresh
                        ()
                        (res === !!false)
                        (type_b =/= var __ __ __ (Std.some __))
                        (type_b =/= class_ __ __)
                        (type_b =/= interface __ __)
                    ])
             ])
      ; fresh
          ta
          (type_a === array ta)
          (conde
             [ fresh
                 ()
                 (ta === CT.object_t)
                 (conde
                    [ fresh
                        ()
                        (res === !!true)
                        (conde
                           [ type_b === CT.object_t
                           ; type_b === CT.cloneable_t
                           ; type_b === CT.serializable_t
                           ])
                    ; fresh
                        ()
                        (type_b =/= CT.object_t)
                        (type_b =/= CT.serializable_t)
                        (type_b =/= CT.cloneable_t)
                        (conde
                           [ fresh tb (type_b === array tb) (( -<- ) ( <-< ) ta tb res)
                           ; fresh () (res === !!false) (type_b =/= array __)
                           ])
                    ])
             ; fresh
                 ()
                 (ta =/= CT.object_t)
                 (conde
                    [ fresh tb (type_b === array tb) (( -<- ) ( <-< ) ta tb res)
                    ; fresh () (res === !!false) (type_b =/= array __)
                    ])
             ])
      ; fresh ts (type_a === intersect ts) (memo type_b ts res)
      ; fresh
          upb_typ
          (type_a === var __ __ upb_typ __)
          (conde
             [ fresh () (upb_typ === type_b) (res === !!true)
             ; fresh () (res === !!false) (upb_typ =/= type_b)
             ])
      ; fresh
          ()
          (type_a === null ())
          (conde
             [ fresh () (type_b === null ()) (res === !!false)
             ; fresh () (res === !!true) (type_b =/= null ())
             ])
      ]
 ;;
end
