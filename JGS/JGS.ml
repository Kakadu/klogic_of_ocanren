let need_simpified = false

[@@@ocaml.warning "-8"]

open Option
open Peano
open List
open Option

type polarity =
  | Extends
  | Super

type 'jtype targ =
  | Type of 'jtype
  | Wildcard of (polarity * 'jtype) option

type jtype =
  | Array of jtype
  | Class of int * jtype targ list
  | Interface of int * jtype targ list
  | Var of
      { id : int
      ; index : nat
      ; upb : jtype
      ; lwb : jtype option
      }
  | Null
  | Intersect of jtype list

type cdecl =
  { params : jtype list
  ; super : jtype
  ; supers : jtype list
  }

type idecl =
  { params : jtype list
  ; supers : jtype list
  }

type decl =
  | C of cdecl
  | I of idecl

type capture_conversion_subst =
  | CC_inter of jtype * jtype
  | CC_subst of jtype

type capture_conversion_type =
  | CC_type of jtype
  | CC_var of int * nat * capture_conversion_subst * jtype option

let rec substitute_typ subst = function
  | Array typ -> Array (substitute_typ subst typ)
  | Class (id, args) -> Class (id, List.map (substitute_arg subst) args)
  | Interface (id, args) -> Interface (id, List.map (substitute_arg subst) args)
  | Intersect typs -> Intersect (List.map (substitute_typ subst) typs)
  | Var _ -> failwith "*** should not happen ***"
  | Null -> Null

and substitute_arg subst = function
  | Type (Var { index }) -> List.nth subst index
  | Type typ -> Type (substitute_typ subst typ)
  | Wildcard None -> Wildcard None
  | Wildcard (Some (p, typ1)) -> Wildcard (Some (p, substitute_typ subst typ1))
;;

module Verifier (CT : sig
  val decl_by_id : int -> decl
  val get_superclass : int -> int -> jtype option
  val object_t : jtype
  val cloneable_t : jtype
  val serializable_t : jtype
  val new_var : unit -> int
end) =
struct
  let rec ( -<- ) (( <-< ) : jtype -> jtype -> bool) (ta : jtype) (tb : jtype) =
    let ( <=< ) ta tb =
      match ta, tb with
      | Wildcard (Some (Extends, t)), Wildcard (Some (Extends, s)) -> t <-< s
      | Wildcard (Some (Extends, t)), Wildcard None -> true
      | Wildcard (Some (Super, t)), Wildcard (Some (Super, s)) -> s <-< t
      | Wildcard (Some (Super, t)), Wildcard None -> true
      | Wildcard (Some (Super, t)), Wildcard (Some (Extends, o)) -> o = CT.object_t
      | Type t1, Type t2
      | Type t1, Wildcard (Some (Extends, t2))
      | Type t1, Wildcard (Some (Super, t2)) -> t1 = t2
      | _ -> false
    in
    let capture_conversion id targs =
      let params =
        match CT.decl_by_id id with
        | C { params } | I { params } -> params
      in
      let raw =
        List.mapi
          (fun i -> function
            | Type t -> CC_type t
            | Wildcard None ->
              CC_var (CT.new_var (), i, CC_subst (List.nth params i), Some Null)
            | Wildcard (Some (Super, t)) ->
              CC_var (CT.new_var (), i, CC_subst (List.nth params i), Some t)
            | Wildcard (Some (Extends, t)) ->
              CC_var (CT.new_var (), i, CC_inter (t, List.nth params i), Some Null))
          targs
      in
      let subst =
        List.map
          (function
           | CC_type t -> Type t
           | CC_var (id, i, _, _) -> Type (Var { lwb = None; upb = Null; index = i; id }))
          raw
      in
      let targs =
        List.map
          (function
           | CC_type t -> Type (substitute_typ subst t)
           | CC_var (id, i, CC_subst p, lwb) ->
             Type (Var { lwb; upb = substitute_typ subst p; index = i; id })
           | CC_var (id, i, CC_inter (t, p), lwb) ->
             Type
               (Var
                  { lwb
                  ; upb =
                      (match substitute_typ subst p with
                       | Intersect ts -> Intersect (t :: ts)
                       | typ -> Intersect [ t; typ ])
                  ; index = i
                  ; id
                  }))
          raw
      in
      if List.for_all
           (function
            | Type (Var { upb; lwb = Some lwb }) -> lwb <-< upb
            | _ -> true)
           targs
      then Some targs
      else None
    in
    let class_int_sub id_a targs_a id_b targs_b =
      if id_a = id_b
      then List.fold_left2 (fun f ta tb -> f && ta <=< tb) true targs_a targs_b
      else (
        match CT.get_superclass id_a id_b with
        | Some (Class (_, targs_b')) | Some (Interface (_, targs_b')) ->
          targs_b = List.map (fun t -> substitute_arg targs_a t) targs_b'
        | None -> false)
    in
    let ( -<- ) = ( -<- ) ( <-< ) in
    match ta with
    | Class (id_a, targs_a) ->
      (match capture_conversion id_a targs_a with
       | None -> false
       | Some targs_a ->
         (match tb with
          | Interface (id_b, targs_b) | Class (id_b, targs_b) ->
            class_int_sub id_a targs_a id_b targs_b
          | Var { lwb = Some typ } -> typ = ta
          | _ -> false))
    | Interface (id_a, targs_a) ->
      (match capture_conversion id_a targs_a with
       | None -> false
       | Some targs_a ->
         (match tb with
          | Class (id_b, targs_b) | Interface (id_b, targs_b) ->
            class_int_sub id_a targs_a id_b targs_b
          | Var { lwb = Some typ } -> typ = ta
          | _ -> false))
    | Array ta ->
      if ta = CT.object_t
      then
        if tb = CT.object_t || tb = CT.cloneable_t || tb = CT.serializable_t
        then true
        else (
          match tb with
          | Array tb -> ta -<- tb
          | _ -> false)
      else (
        match tb with
        | Array tb -> ta -<- tb
        | _ -> false)
    | Intersect ts -> List.mem tb ts
    | Var { upb = typ } -> typ = tb
    | Null -> tb <> Null
  ;;
end

[@@@ocaml.warning "+8"]

open GT
open OCanren

module HO = struct
  open Option.HO
  open Peano.HO
  open List.HO
  open Option.HO

  [%%distrib
  type polarity =
    | Extends
    | Super
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  [%%distrib
  type 'jtype targ =
    | Type of 'jtype
    | Wildcard of (polarity * 'jtype) option
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  [%%distrib
  type jtype =
    | Array of jtype
    | Class of int * jtype targ list
    | Interface of int * jtype targ list
    | Var of
        { id : int
        ; index : nat
        ; upb : jtype
        ; lwb : jtype option
        }
    | Null
    | Intersect of jtype list
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  [%%distrib
  type cdecl =
    { params : jtype list
    ; super : jtype
    ; supers : jtype list
    }
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let ctor_cdecl params super supers = inj { params; super; supers }

  [%%distrib
  type idecl =
    { params : jtype list
    ; supers : jtype list
    }
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let ctor_idecl params supers = inj { params; supers }
  let var id index upb lwb = !!(Var { id; index; upb; lwb })

  [%%distrib
  type decl =
    | C of cdecl
    | I of idecl
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  [%%distrib
  type capture_conversion_subst =
    | CC_inter of jtype * jtype
    | CC_subst of jtype
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  [%%distrib
  type capture_conversion_type =
    | CC_type of jtype
    | CC_var of int * nat * capture_conversion_subst * jtype option
  [@@deriving gt ~options:{ show; fmt; gmap }]]

  let rec substitute_typ subst q0 q30 =
    fresh
      q3
      (q0 q3)
      (conde
         [ fresh
             (typ q4)
             (q3 === !!(Array typ))
             (q30 === !!(Array q4))
             (substitute_typ subst (( === ) typ) q4)
         ; fresh
             (id args q8)
             (q3 === !!(Class (id, args)))
             (q30 === !!(Class (id, q8)))
             (List.HO.map (substitute_arg subst) (( === ) args) q8)
         ; fresh
             (id args q13)
             (q3 === !!(Interface (id, args)))
             (q30 === !!(Interface (id, q13)))
             (List.HO.map (substitute_arg subst) (( === ) args) q13)
         ; fresh
             (typs q17)
             (q3 === !!(Intersect typs))
             (q30 === !!(Intersect q17))
             (List.HO.map (substitute_typ subst) (( === ) typs) q17)
         ; fresh () (q3 === !!Null) (q30 === !!Null)
         ])

  and substitute_arg subst q34 q63 =
    fresh
      q37
      (q34 q37)
      (conde
         [ fresh
             (q38 index q39 q40)
             (q37 === !!(Type (var q38 index q39 q40)))
             (List.HO.nth subst (( === ) index) q63)
         ; fresh
             (typ q48)
             (q37 === !!(Type typ))
             (q63 === !!(Type q48))
             (q37 =/= !!(Type (var __ __ __ __)))
             (substitute_typ subst (( === ) typ) q48)
         ; fresh
             ()
             (q37 === !!(Wildcard !!None))
             (q63 === !!(Wildcard !!None))
             (q37 =/= !!(Type __))
             (q37 =/= !!(Type (var __ __ __ __)))
         ; fresh
             (p typ q58 q59)
             (q37 === !!(Wildcard !!(Some (Std.pair p typ))))
             (q63 === !!(Wildcard !!(Some (Std.pair q58 q59))))
             (p === q58)
             (q37 =/= !!(Wildcard !!None))
             (q37 =/= !!(Type __))
             (q37 =/= !!(Type (var __ __ __ __)))
             (substitute_typ subst (( === ) typ) q59)
         ])
  ;;

  module Verifier (CT : sig
    module HO : sig
      val decl_by_id : (int ilogic -> OCanren.goal) -> decl_injected -> OCanren.goal

      val get_superclass
        :  (int ilogic -> OCanren.goal)
        -> (int ilogic -> OCanren.goal)
        -> jtype_injected option_injected
        -> OCanren.goal

      val object_t : jtype_injected -> OCanren.goal
      val cloneable_t : jtype_injected -> OCanren.goal
      val serializable_t : jtype_injected -> OCanren.goal
      val new_var : (unit OCanren.ilogic -> OCanren.goal) -> int ilogic -> OCanren.goal
    end
  end) =
  struct
    let rec ( -<- ) ( <-< ) ta tb res =
      fresh
        (ta_val tb_val)
        (ta ta_val)
        (tb tb_val)
        (let ( <=< ) ta tb q97 =
           if need_simpified
           then
             fresh
               (ta_val tb_val)
               (ta ta_val)
               (tb tb_val)
               (conde
                  [ fresh () (ta_val === tb_val) (q97 === !!true)
                  ; fresh () (ta_val =/= tb_val) (q97 === !!false)
                  ])
           else
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
                             !!(Wildcard !!(Some (Std.pair !!Extends t)))
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
                       === Std.pair
                             !!(Wildcard !!(Some (Std.pair !!Super t)))
                             !!(Wildcard !!None))
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
                           === Std.pair
                                 !!(Type t1)
                                 !!(Wildcard !!(Some (Std.pair !!Extends t2)))
                         ; q71
                           === Std.pair
                                 !!(Type t1)
                                 !!(Wildcard !!(Some (Std.pair !!Super t2)))
                         ])
                      (q71
                       =/= Std.pair
                             !!(Wildcard !!(Some (Std.pair !!Super __)))
                             !!(Wildcard !!(Some (Std.pair !!Extends __))))
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
                      (conde
                         [ fresh () (t1 === t2) (q97 === !!true)
                         ; fresh () (q97 === !!false) (t1 =/= t2)
                         ])
                  ; fresh
                      ()
                      (q97 === !!false)
                      (q71 =/= Std.pair !!(Type __) !!(Type __))
                      (q71
                       =/= Std.pair
                             !!(Type __)
                             !!(Wildcard !!(Some (Std.pair !!Extends __))))
                      (q71
                       =/= Std.pair
                             !!(Type __)
                             !!(Wildcard !!(Some (Std.pair !!Super __))))
                      (q71
                       =/= Std.pair
                             !!(Wildcard !!(Some (Std.pair !!Super __)))
                             !!(Wildcard !!(Some (Std.pair !!Extends __))))
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
                  ])
         in
         let capture_conversion id targs q205 =
           if need_simpified
           then fresh targs_val (targs targs_val) (q205 === !!(Some targs_val))
           else
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
                                === !!(CC_var
                                         (q114, q134, !!(CC_subst q117), !!(Some !!Null)))
                               )
                               (CT.HO.new_var (( === ) !!()) q114)
                               (List.HO.nth params (( === ) q134) q117)
                           ; fresh
                               (t q119 q122)
                               (q110 === !!(Wildcard !!(Some (Std.pair !!Super t))))
                               (q133
                                === !!(CC_var (q119, q134, !!(CC_subst q122), !!(Some t)))
                               )
                               (CT.HO.new_var (( === ) !!()) q119)
                               (List.HO.nth params (( === ) q134) q122)
                           ; fresh
                               (t q126 q130)
                               (q110 === !!(Wildcard !!(Some (Std.pair !!Extends t))))
                               (q133
                                === !!(CC_var
                                         ( q126
                                         , q134
                                         , !!(CC_inter (t, q130))
                                         , !!(Some !!Null) )))
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
                                      (q168
                                       === !!(Intersect (Std.list Fun.id [ t; q170 ])))
                                      (q170 =/= !!(Intersect __))
                                  ])
                           ]))
                    raw
                in
                fresh
                  q186
                  (List.HO.for_all
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
         in
         let class_int_sub id_a targs_a id_b targs_b q235 =
           fresh
             (q232 q233 q208)
             (id_a q232)
             (id_b q233)
             (conde
                [ fresh () (q232 === q233) (q208 === !!true)
                ; fresh () (q208 === !!false) (q232 =/= q233)
                ])
             (conde
                [ fresh
                    ()
                    (q208 === !!true)
                    (List.HO.fold_left2
                       (fun f ta tb q228 ->
                         fresh
                           q226
                           (f q226)
                           (conde
                              [ fresh () (q226 === !!false) (q228 === !!false)
                              ; fresh () (q226 === !!true) (( <=< ) ta tb q228)
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
                           (List.HO.map (substitute_arg targs_a) (( === ) targs_b') q218)
                           (conde
                              [ fresh () (q217 === q218) (q235 === !!true)
                              ; fresh () (q235 === !!false) (q217 =/= q218)
                              ])
                       ; fresh () (q211 === !!None) (q235 === !!false)
                       ])
                ])
         in
         let ( -<- ) = ( -<- ) ( <-< ) in
         fresh
           ()
           (conde
              [ fresh
                  (id_a targs_a q243)
                  (ta_val === !!(Class (id_a, targs_a)))
                  (capture_conversion (( === ) id_a) (( === ) targs_a) q243)
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
                                   (( === ) id_a)
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
                  (capture_conversion (( === ) id_a) (( === ) targs_a) q271)
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
                                   (( === ) id_a)
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
  end
end

module FO = struct
  open Option.HO
  open Peano.HO
  open List.HO
  open Option.HO
  open HO

  let substitute_typ q33 q32 q31 = substitute_typ (( === ) q33) (( === ) q32) q31
  let substitute_arg q66 q65 q64 = substitute_arg (( === ) q66) (( === ) q65) q64

  module Verifier (CT : sig
    module HO : sig
      val decl_by_id : (int ilogic -> OCanren.goal) -> decl_injected -> OCanren.goal

      val get_superclass
        :  (int ilogic -> OCanren.goal)
        -> (int ilogic -> OCanren.goal)
        -> jtype_injected option_injected
        -> OCanren.goal

      val object_t : jtype_injected -> OCanren.goal
      val cloneable_t : jtype_injected -> OCanren.goal
      val serializable_t : jtype_injected -> OCanren.goal
      val new_var : (unit OCanren.ilogic -> OCanren.goal) -> int ilogic -> OCanren.goal
    end
  end) =
  struct
    open Verifier (CT)

    let ( -<- ) q383 q382 q381 q380 =
      ( -<- )
        (fun q387 q385 q384 ->
          call_fresh (fun q388 ->
            call_fresh (fun q386 -> ?&[ q387 q388; q385 q386; q383 q388 q386 q384 ])))
        (( === ) q382)
        (( === ) q381)
        q380
    ;;
  end
end
