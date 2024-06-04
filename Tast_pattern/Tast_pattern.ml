(** Copyright 2021-2023, Kakadu. *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

module Ast_pattern0 = struct
  exception Expected of Location.t * string

  let fail loc expected = raise (Expected (loc, expected))

  type context =
    { (* [matched] counts how many constructors have been matched. This is used to find what
         pattern matches the most some piece of ast in [Ast_pattern.alt]. In the case where
         all branches fail to match, we report the error from the one that matches the
         most.
         This is only incremented by combinators that can fail. *)
      mutable matched : int
    }

  type ('matched_value, 'k, 'k_result) t =
    | T of (context -> Location.t -> 'matched_value -> 'k -> 'k_result)

  (* end of copy-paste from https://github.com/ocaml-ppx/ppxlib/blob/0.22.2/src/ast_pattern0.ml *)
  (* TODO: deal with licencing issues *)
end

open Location
module Format = Stdlib.Format
open Format
open Ast_pattern0
open Stdppx

let debug_enabled = false
let debug_enabled = true

let log fmt =
  let open Format in
  if debug_enabled then kasprintf (printf "%s\n%!") fmt else ifprintf std_formatter fmt
;;

type ('a, 'b, 'c) t = ('a, 'b, 'c) Ast_pattern0.t

let of_func f = T f
let to_func (T f) = f
let save_context ctx = ctx.matched
let restore_context ctx backup = ctx.matched <- backup
let incr_matched c = c.matched <- c.matched + 1

let parse (T f) loc ?on_error x k =
  try f { matched = 0 } loc x k with
  | Expected (loc, expected) ->
    (match on_error with
    | None -> Location.raise_errorf ~loc "%s expected" expected
    | Some f -> f expected)
;;

module Packed = struct
  type ('a, 'b) t = T : ('a, 'b, 'c) Ast_pattern0.t * 'b -> ('a, 'c) t

  let create t f = T (t, f)
  let parse (T (t, f)) loc x = parse t loc x f
end

let __ : 'a 'b. ('a, 'a -> 'b, 'b) t =
  T
    (fun ctx _loc x k ->
      incr_matched ctx;
      k x)
;;

let as__ : 'a 'b 'c. ('a, 'b, 'c) t -> ('a, 'a -> 'b, 'c) t =
 fun (T f1) ->
  T
    (fun ctx loc x k ->
      let k = f1 ctx loc x (k x) in
      k)
;;

let pair (T f1) (T f2) =
  T
    (fun ctx loc (x1, x2) k ->
      let k = f1 ctx loc x1 k in
      let k = f2 ctx loc x2 k in
      k)
;;

let ( ** ) = pair

let __' =
  T
    (fun ctx loc x k ->
      incr_matched ctx;
      k { loc; txt = x })
;;

let drop : 'a 'b. ('a, 'b, 'b) t =
  T
    (fun ctx _loc _ k ->
      incr_matched ctx;
      k)
;;

let cst ~to_string ?(equal = Poly.equal) v =
  T
    (fun ctx loc x k ->
      if equal x v
      then (
        incr_matched ctx;
        (* printf "cst succeeded for %s\n%!" (to_string v); *)
        k)
      else fail loc (to_string v))
;;

let int v = cst ~to_string:Int.to_string v
let char v = cst ~to_string:(Printf.sprintf "%C") v
let string v = cst ~to_string:(Printf.sprintf "%S") v
let float v = cst ~to_string:Float.to_string v
let int32 v = cst ~to_string:Int32.to_string v
let int64 v = cst ~to_string:Int64.to_string v
let nativeint v = cst ~to_string:Nativeint.to_string v
let bool v = cst ~to_string:Bool.to_string v

let false_ =
  T
    (fun ctx loc x k ->
      match x with
      | false ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "false")
;;

let true_ =
  T
    (fun ctx loc x k ->
      match x with
      | true ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "true")
;;

let nil =
  T
    (fun ctx loc x k ->
      (* log "trying [] \n%!"; *)
      match x with
      | [] ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "[]")
;;

let ( ^:: ) (T f0) (T f1) =
  T
    (fun ctx loc x k ->
      match x with
      | x0 :: x1 ->
        ctx.matched <- ctx.matched + 1;
        (* Format.printf "trying elem of cons cell\n%!"; *)
        let k = f0 ctx loc x0 k in
        (* Format.printf "trying tail of cons cell\n%!"; *)
        let k = f1 ctx loc x1 k in
        (* Format.printf "trying  cons cell succeeded\n%!"; *)
        k
      | _ ->
        (* Format.printf "failing elem of cons cell\n%!"; *)
        fail loc "::")
;;

let none =
  T
    (fun ctx loc x k ->
      match x with
      | None ->
        ctx.matched <- ctx.matched + 1;
        (* log "none succeded"; *)
        k
      | _ -> fail loc "None")
;;

let some (T f0) =
  T
    (fun ctx loc x k ->
      match x with
      | Some x0 ->
        ctx.matched <- ctx.matched + 1;
        let k = f0 ctx loc x0 k in
        k
      | _ -> fail loc "Some")
;;

let triple (T f1) (T f2) (T f3) =
  T
    (fun ctx loc (x1, x2, x3) k ->
      let k = f1 ctx loc x1 k in
      let k = f2 ctx loc x2 k in
      let k = f3 ctx loc x3 k in
      k)
;;

let alt (T f1) (T f2) =
  T
    (fun ctx loc x k ->
      let backup = save_context ctx in
      try f1 ctx loc x k with
      | e1 ->
        let m1 = save_context ctx in
        restore_context ctx backup;
        (try f2 ctx loc x k with
        | e2 ->
          let m2 = save_context ctx in
          if m1 >= m2
          then (
            restore_context ctx m1;
            raise e1)
          else raise e2))
;;

let ( ||| ) = alt

let choice ps =
  T
    (fun ctx loc e k ->
      let rec helper = function
        | [] -> fail loc "no choices left "
        | h :: tl ->
          (match to_func h ctx loc e k with
          | exception Expected (_, _) ->
            (* log "Got Expected %S" s; *)
            helper tl
          | x -> x)
      in
      helper ps)
;;

let map (T func) ~f = T (fun ctx loc x k -> func ctx loc x (f k))
let map' (T func) ~f = T (fun ctx loc x k -> func ctx loc x (f loc k))
let map_result (T func) ~f = T (fun ctx loc x k -> f (func ctx loc x k))
let ( >>| ) t f = map t ~f
let map0 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (k f))
let map1 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a -> k (f a)))
let map2 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a b -> k (f a b)))
let map3 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a b c -> k (f a b c)))

let map4 (T func) ~f =
  T (fun ctx loc x k -> func ctx loc x (fun a b c d -> k (f a b c d)))
;;

let map5 (T func) ~f =
  T (fun ctx loc x k -> func ctx loc x (fun a b c d e -> k (f a b c d e)))
;;

let map6 (T func) ~f:fooo =
  T (fun ctx loc x k -> func ctx loc x (fun a b c d e f -> k (fooo a b c d e f)))
;;

let map7 (T func) ~f:fooo =
  T (fun ctx loc x k -> func ctx loc x (fun a b c d e f g -> k (fooo a b c d e f g)))
;;

let map0' (T func) ~f = T (fun ctx loc x k -> func ctx loc x (k (f loc)))
let map1' (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a -> k (f loc a)))
let map2' (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a b -> k (f loc a b)))
let map_result (T func) ~f = T (fun ctx loc x k -> f (func ctx loc x k))
let alt_option some none = alt (map1 some ~f:(fun x -> Some x)) (map0 none ~f:None)

let many (T f) =
  T (fun ctx loc l k -> k (List.map l ~f:(fun x -> f ctx loc x (fun x -> x))))
;;

let loc (T f) = T (fun ctx _loc (x : _ Ppxlib.Loc.t) k -> f ctx x.loc x.txt k)
let pack0 t = map t ~f:(fun f -> f ())
let pack2 t = map t ~f:(fun f x y -> f (x, y))
let pack3 t = map t ~f:(fun f x y z -> f (x, y, z))
let pack4 t = map t ~f:(fun f a b c d -> f (a, b, c, d))
let pack5 t = map t ~f:(fun f a b c d e -> f (a, b, c, d, e))

(* end of copy-paste from https://github.com/ocaml-ppx/ppxlib/blob/0.22.2/src/ast_pattern.ml *)
(* TODO: deal with licencing issues *)

let lident (T fident) =
  T
    (fun ctx loc x k ->
      match x with
      | Longident.Lident id ->
        ctx.matched <- ctx.matched + 1;
        k |> fident ctx loc id
      | _ -> fail loc (sprintf "lident"))
;;

let path_pident (T fident) =
  T
    (fun ctx loc x k ->
      match x with
      | Path.Pident id ->
        ctx.matched <- ctx.matched + 1;
        k |> fident ctx loc id
      | _ -> fail loc (sprintf "path_pident"))
;;

let path xs =
  let cmp_names l r =
    let ans = String.equal l r in
    (* let _ = printf "\t\tCompare names %s and %s:  %b\n%!" l r ans in *)
    ans
  in
  let rec helper ps ctx loc x k =
    (* let _ = Format.printf "path = %a\n%!" Path.print x in *)
    match x, ps with
    | Path.Pident id, [ id0 ] ->
      (* log "ident = %a, id0 = %s" Path.print x id0; *)
      if cmp_names (Ident.name id) id0
      then (
        let () = ctx.matched <- ctx.matched + 1 in
        (* log "path %s succeeded" (String.concat ~sep:"." xs); *)
        k)
      else (* let () = log "AAA" in *)
        fail loc "path"
    | Path.Pdot (next, id), id0 :: ids when cmp_names id id0 -> helper ids ctx loc next k
    | Path.Papply _, _ -> fail loc "path got Papply"
    | _ ->
      let msg = sprintf "path %s" (String.concat ~sep:"." xs) in
      (* let _ = Format.printf "path failed: %s\n%!" msg in *)
      fail loc msg
  in
  T (helper (List.rev xs))
;;

let path_of_list xs =
  match xs with
  | [] -> failwith "Bad argument: path_of_list"
  | s :: tl ->
    List.fold_left
      tl
      ~init:(Path.Pident (Ident.create_local s))
      ~f:(fun acc x -> Path.Pdot (acc, x))
;;

let%test_module " " =
  (module struct
    let names = [ "Stdlib!"; "List"; "length" ]

    let%test_unit _ =
      let old = !Clflags.unique_ids in
      Clflags.unique_ids := false;
      [%test_eq: Base.string]
        "Stdlib!.List.length"
        (asprintf "%a" Path.print (path_of_list names));
      Clflags.unique_ids := old
    ;;

    let%test _ =
      let noloc =
        Warnings.
          { loc_start = Lexing.dummy_pos; loc_end = Lexing.dummy_pos; loc_ghost = true }
      in
      parse (path names) noloc ~on_error:(fun _ -> false) (path_of_list names) true
    ;;
  end)
;;

open Typedtree

let econst (T f0) =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_constant n ->
        ctx.matched <- ctx.matched + 1;
        f0 ctx loc n k
      | _ -> fail loc (sprintf "econst"))
;;

let eint (T f0) =
  T
    (fun ctx loc x k ->
      (* let _ = log "<eint> %a\n%!" MyPrinttyped.expr x in *)
      match x.exp_desc with
      | Texp_constant (Asttypes.Const_int n) ->
        ctx.matched <- ctx.matched + 1;
        let ans = f0 ctx loc n k in
        (* log "eint succeeded %a\n%!" MyPrinttyped.expr x; *)
        ans
      | _ -> fail loc "eint")
;;

let estring (T f0) =
  T
    (fun ctx loc x k ->
      (* let _ = log "<eint> %a\n%!" MyPrinttyped.expr x in *)
      match x.exp_desc with
      | Texp_constant (Asttypes.Const_string (s, _, _)) ->
        ctx.matched <- ctx.matched + 1;
        let ans = f0 ctx loc s k in
        (* log "eint succeeded %a\n%!" MyPrinttyped.expr x; *)
        ans
      | _ -> fail loc "estring")
;;

let ebool =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_construct ({ txt = Lident "true" }, _, []) ->
        ctx.matched <- ctx.matched + 1;
        k true
      | Texp_construct ({ txt = Lident "false" }, _, []) ->
        ctx.matched <- ctx.matched + 1;
        k false
      | _ -> fail loc (sprintf "ebool"))
;;

let tpat_var (T fname) =
  T
    (fun ctx loc x k ->
      (* log "tpat_var"; *)
      match x.pat_desc with
      | Tpat_var (_, { txt }) ->
        ctx.matched <- ctx.matched + 1;
        let ans = k |> fname ctx loc txt in
        (* log "tpat_var +"; *)
        ans
      | _ -> fail loc "tpat_var")
;;

let tpat_var_type (T fname) (T ftyp) =
  T
    (fun ctx loc x k ->
      match x.pat_desc with
      | Tpat_var (_, { txt }) ->
        ctx.matched <- ctx.matched + 1;
        k |> fname ctx loc txt |> ftyp ctx loc x.pat_type
      | _ -> fail loc "tpat_var_type")
;;

let tpat_unit =
  T
    (fun (type a) ctx loc (x : a pattern_desc pattern_data) k ->
      match x.pat_desc with
      | Tpat_construct (_, Types.{ cstr_name = "()" }, [], _) ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "tpat_unit")
;;

let tpat_exception (T fpat) =
  T
    (fun ctx loc x k ->
      match x.pat_desc with
      | Tpat_exception exc ->
        ctx.matched <- ctx.matched + 1;
        k |> fpat ctx loc exc
      | _ -> fail loc "tpat_exception")
;;

let tpat_any =
  T
    (fun ctx loc x k ->
      match x.pat_desc with
      | Tpat_any ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "tpat_any")
;;

let texp_ident (T fpath) =
  T
    (fun ctx loc x k ->
      (* let _ = log "texp_ident %a (%s %d)\n%!" MyPrinttyped.expr x __FILE__ __LINE__ in *)
      match x.exp_desc with
      | Texp_ident (path, _, _) ->
        ctx.matched <- ctx.matched + 1;
        let ans = fpath ctx loc path k in
        (* log "texp_ident + %a\n%!" MyPrinttyped.expr x; *)
        ans
      | _ ->
        (* let _ = log "FAILED: texp_ident %a\n%!" MyPrinttyped.expr x in *)
        fail loc "texp_ident")
;;

let pident (T fstr) =
  T
    (fun ctx loc x k ->
      match x with
      | Path.Pident id -> fstr ctx loc (Ident.name id) k
      | _ -> fail loc "pident")
;;

let texp_ident_typ (T fpath) (T ftyp) =
  T
    (fun ctx loc x k ->
      (* let __ _ = Format.printf "texp_ident_typ %a\n%!" MyPrinttyped.expr x in *)
      match x.exp_desc with
      | Texp_ident (path, _, typ) ->
        ctx.matched <- ctx.matched + 1;
        k |> fpath ctx loc path |> ftyp ctx loc typ.Types.val_type
      | _ -> fail loc "texp_ident_typ")
;;

let texp_let (T fvbs) (T fe) =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_let (_, vbs, e) ->
        ctx.matched <- ctx.matched + 1;
        k |> fvbs ctx loc vbs |> fe ctx loc e
      | _ -> fail loc "texp_let")
;;

let value_binding (T fpat) (T fexpr) =
  T
    (fun ctx loc { vb_pat; vb_expr; _ } k ->
      k |> fpat ctx loc vb_pat |> fexpr ctx loc vb_expr)
;;

let texp_assert (T fexp) =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_assert e ->
        ctx.matched <- ctx.matched + 1;
        fexp ctx loc e k
      | _ -> fail loc "texp_assert")
;;

let texp_ascription (T fexp) (T ftyp) =
  of_func (fun ctx loc x k ->
    try
      let rez = k |> fexp ctx loc x in
      (* Format.printf "ascription with type %a\n%!" Printtyp.type_expr x.exp_type; *)
      let rez = rez |> ftyp ctx loc x.exp_type in
      (* Format.printf "ascription succeeded\n%!"; *)
      rez
    with
    | exc ->
      (* Format.printf "ascription failed\n%!"; *)
      raise_notrace exc)
;;

let texp_apply (T f0) (T args0) =
  T
    (fun ctx loc x k ->
      (* let _ = log "texp_apply %a\n%!" MyPrinttyped.expr x in *)
      match x.exp_desc with
      | Texp_apply (f, args) ->
        ctx.matched <- ctx.matched + 1;
        let ans = k |> f0 ctx loc f |> args0 ctx loc args in
        (* let _ = log "texp_apply + %a\n%!" MyPrinttyped.expr x in *)
        ans
      | _ ->
        (* let _ = log "texp_apply failed" in *)
        fail loc "texp_apply")
;;

let texp_apply_nolabelled (T f0) (T args0) =
  let exception EarlyExit in
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_apply (f, args) ->
        ctx.matched <- ctx.matched + 1;
        let k = f0 ctx loc f k in
        (try
           let args =
             List.map args ~f:(function
               | _, None -> raise EarlyExit
               | _, Some x -> x)
           in
           args0 ctx loc args k
         with
        | EarlyExit -> fail loc "texp_apply: None among the arguments ")
      | _ -> fail loc "texp_apply")
;;

let texp_construct (T fpath) (T fcd) (T fargs) =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_construct (path, cd, args) ->
        ctx.matched <- ctx.matched + 1;
        let k = fpath ctx loc path.txt k in
        k |> fcd ctx loc cd |> fargs ctx loc args
      | _ -> fail loc (sprintf "texp_construct"))
;;

let texp_unit =
  T
    (fun ctx loc x k ->
      match x.exp_desc with
      | Texp_construct ({ txt = Lident "()" }, _cd, []) ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc (sprintf "texp_unit"))
;;

let texp_assert_false () = texp_assert (texp_construct (lident (string "false")) drop nil)

let nolabel =
  T
    (fun ctx loc x k ->
      match x with
      | Asttypes.Nolabel ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "nolabel")
;;

let labelled (T fstr) =
  T
    (fun ctx loc x k ->
      match x with
      | Asttypes.Labelled s ->
        ctx.matched <- ctx.matched + 1;
        k |> fstr ctx loc s
      | _ -> fail loc "labelled")
;;

let texp_apply1 f x = texp_apply f ((nolabel ** some x) ^:: nil)
let texp_apply2 f x y = texp_apply f ((nolabel ** some x) ^:: (nolabel ** some y) ^:: nil)

[%%if ocaml_version < (4, 11, 2)]

(* 4.10 *)
type case_val = Typedtree.case
type case_comp = Typedtree.case
type value_pat = pattern
type comp_pat = pattern

[%%else]

type case_val = value case
type case_comp = computation case
type value_pat = value pattern_desc pattern_data
type comp_pat = computation pattern_desc pattern_data

[%%endif]

let texp_lambda (T fpat) (T frhs) =
  of_func (fun ctx loc e k ->
    match e.exp_desc with
    | Texp_function { cases = [ { c_lhs; c_rhs; c_guard = None } ] } ->
      ctx.matched <- ctx.matched + 1;
      let ans = k |> fpat ctx loc c_lhs |> frhs ctx loc c_rhs in
      (* log "texp_function +"; *)
      ans
    | _ -> fail loc "texp_lambda")
;;

let texp_function (T fcases) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_function { cases } ->
        (* log "texp_function with %d cases" (List.length cases); *)
        ctx.matched <- ctx.matched + 1;
        let ans = k |> fcases ctx loc cases in
        (* log "texp_function +"; *)
        ans
      | _ ->
        log "texp_function failed";
        fail loc "texp_function")
;;

let case (T pat) (T guard) (T rhs) =
  T
    (fun ctx loc { c_lhs; c_rhs; c_guard } k ->
      k |> pat ctx loc c_lhs |> guard ctx loc c_guard |> rhs ctx loc c_rhs)
;;

let texp_match (T fexpr) (T fcases) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_match (e, cases, _) ->
        ctx.matched <- ctx.matched + 1;
        k |> fexpr ctx loc e |> fcases ctx loc cases
      | _ -> fail loc "texp_match")
;;

let texp_ite (T pred) (T fthen) (T felse) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_ifthenelse (p, thenb, elseb) ->
        ctx.matched <- ctx.matched + 1;
        k |> pred ctx loc p |> fthen ctx loc thenb |> felse ctx loc elseb
      | _ -> fail loc "texp_ite")
;;

let texp_try (T fexpr) (T fcases) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_try (e, cases) ->
        ctx.matched <- ctx.matched + 1;
        k |> fexpr ctx loc e |> fcases ctx loc cases
      | _ -> fail loc "texp_try")
;;

let texp_record (T fext) (T ffields) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_record { fields; extended_expression; _ } ->
        ctx.matched <- ctx.matched + 1;
        k |> fext ctx loc extended_expression |> ffields ctx loc fields
      | _ -> fail loc "texp_record")
;;

let texp_field (T fexpr) (T fdesc) =
  T
    (fun ctx loc e k ->
      match e.exp_desc with
      | Texp_field (e, _, desc) ->
        ctx.matched <- ctx.matched + 1;
        k |> fexpr ctx loc e |> fdesc ctx loc desc
      | _ -> fail loc "texp_field")
;;

let texp_list : (expression, 'a, 'b) t -> (_, 'b list -> 'd, 'd) t =
 fun felem ->
  let rec lookup loc e =
    (* TODO: tailrec *)
    match e.exp_desc with
    | Texp_construct ({ txt = Longident.Lident "[]" }, _, _) -> []
    | Texp_construct ({ txt = Longident.Lident "::" }, _, [ h; tl ]) -> h :: lookup loc tl
    | _ ->
      log "texp_list#lookup failed %s %d\n%!" __FILE__ __LINE__;
      fail loc "texp_list"
  in
  T
    (fun ctx loc e k ->
      (* printf "%s %d\n%!" __FILE__ __LINE__; *)
      let items = lookup loc e in
      (* printf "texp_list found %d items\n %!" (List.length items); *)
      let items =
        ListLabels.map ~f:(fun e -> to_func felem ctx loc e Stdlib.Fun.id) items
      in
      k items)
;;

let label_desc (T fname) =
  T
    (fun ctx loc e k ->
      match e with
      | { Types.lbl_name; _ } ->
        ctx.matched <- ctx.matched + 1;
        k |> fname ctx loc lbl_name)
;;

let rld_kept =
  T
    (fun ctx loc e k ->
      match e with
      | Kept _ ->
        ctx.matched <- ctx.matched + 1;
        k
      | _ -> fail loc "rld_kept")
;;

let rld_overriden (T flident) (T fexpr) =
  T
    (fun ctx loc e k ->
      match e with
      | Overridden ({ txt = lident }, e) ->
        ctx.matched <- ctx.matched + 1;
        k |> flident ctx loc lident |> fexpr ctx loc e
      | _ -> fail loc "rld_overriden")
;;

(*   let hack0 (T path0) =
     T
     (fun ctx loc x k ->
     match x.Types.val_type.Types.desc with
     | Tconstr (path, [], _) ->
     ctx.matched <- ctx.matched + 1;
     path0 ctx loc path k
     | _ -> fail loc "hack0")
     ;;

     let hack1 ?(on_vd = drop) (T path0) =
     T
     (fun ctx loc x k ->
     match x.exp_desc with
     | Texp_ident (path, _, vd) ->
     ctx.matched <- ctx.matched + 1;
     let (T fvd) = on_vd in
     k |> path0 ctx loc path |> fvd ctx loc vd
     | _ -> fail loc "texp_ident")
     ;;

     let __ path = hack1 __ path *)
let rec core_typ (T ftexpr) = T (fun ctx loc x k -> ftexpr ctx loc x.ctyp_type k)

let rec typ_var (T fname) =
  let rec helper ctx loc x k =
    (* Format.printf "typ = %a\n%!" Printtyp.type_expr x; *)
    match Types.get_desc x with
    | Tvar (Some tag) ->
      ctx.matched <- ctx.matched + 1;
      k |> fname ctx loc tag
    | Tlink arg -> helper ctx loc arg k
    | _ -> fail loc "typ_var"
  in
  T helper
;;

let rec typ_constr (T fpath) (T fargs) =
  let rec helper ctx loc x k =
    (* Format.printf "typ = %a\n%!" Printtyp.type_expr x; *)
    match Types.get_desc x with
    | Tconstr (path, args, _) ->
      ctx.matched <- ctx.matched + 1;
      k |> fpath ctx loc path |> fargs ctx loc args
    | Tlink arg -> helper ctx loc arg k
    | _ -> fail loc "typ_constr"
  in
  T helper
;;

let typ_arrow (T l) (T r) =
  let rec helper ctx loc x k =
    match Types.get_desc x with
    | Tlink e -> helper ctx loc e k
    | Tarrow (_, tl, tr, _) ->
      ctx.matched <- ctx.matched + 1;
      k |> l ctx loc tl |> r ctx loc tr
    | _ -> fail loc "typ_arrow"
  in
  T helper
;;

let typ_arrows (T fargs) (T frhs) =
  let rec helper acc ctx loc x k =
    match Types.get_desc x with
    | Tlink e -> helper acc ctx loc e k
    | Tarrow (_, tl, tr, _) ->
      ctx.matched <- ctx.matched + 1;
      helper (tl :: acc) ctx loc tr k
    | _ when List.length acc = 0 -> fail loc "typ_arrows"
    | _ -> k |> fargs ctx loc (List.rev acc) |> frhs ctx loc x
  in
  T
    (fun ctx loc x k ->
      (* log "%s got type @[%a@]" __FUNCTION__ Printtyp.type_expr x; *)
      helper [] ctx loc x k)
;;

let ( @-> ) = typ_arrow

let tfun_param_named (T fname) (T fmodtyp) =
  T
    (fun ctx loc p k ->
      match p with
      | Typedtree.Named (Some ident, _, param_type) ->
        ctx.matched <- ctx.matched + 1;
        let k = k |> fname ctx loc ident in
        k |> fmodtyp ctx loc param_type
      | _ -> fail loc "tfun_param_named")
;;

let tmodule_type_ident (T fident) =
  T
    (fun ctx loc mt k ->
      match mt.mty_desc with
      | Tmty_ident (_, { txt = id; _ }) -> k |> fident ctx loc id
      | _ -> fail loc "tmodule_type_ident")
;;

let tmod_functor (T fparam) (T fme) =
  T
    (fun ctx loc str k ->
      match str.mod_desc with
      | Tmod_functor (param, me) ->
        ctx.matched <- ctx.matched + 1;
        k |> fparam ctx loc param |> fme ctx loc me
      | _ -> fail loc "tmod_functor")
;;

let tmod_structure (T fstru) =
  T
    (fun ctx loc str k ->
      match str.mod_desc with
      | Tmod_structure stru ->
        ctx.matched <- ctx.matched + 1;
        k |> fstru ctx loc stru
      | _ -> fail loc "tmod_structure")
;;

let tmod_ascription (T fme) (T ftyp) =
  T
    (fun ctx loc str k ->
      match str.mod_desc with
      (* | Tmod_constraint _ -> assert false *)
      (* | Tmod_functor _ -> failwith "herr" *)
      | Tmod_constraint (me, _, Tmodtype_explicit mt, _) ->
        (* log "parsing ascription"; *)
        ctx.matched <- ctx.matched + 1;
        k |> fme ctx loc me |> ftyp ctx loc mt
      | _ -> fail loc "tmod_ascription")
;;

(* Structure *)

let tstr_value (T fvbs) =
  T
    (fun ctx loc str k ->
      match str.str_desc with
      | Tstr_value (_, vbs) ->
        ctx.matched <- ctx.matched + 1;
        k |> fvbs ctx loc vbs
      | _ -> fail loc "tstr_value")
;;

let tstr_module (T fid) (T fexpr) =
  T
    (fun ctx loc str k ->
      match str.str_desc with
      | Tstr_module { mb_id = Some name; mb_expr } ->
        (* log "tstr_module %S" (Ident.name name); *)
        ctx.matched <- ctx.matched + 1;
        k |> fid ctx loc name |> fexpr ctx loc mb_expr
      | _ -> fail loc "tstr_module")
;;

let tstr_attribute (T fattr) =
  T
    (fun ctx loc str k ->
      match str.str_desc with
      | Tstr_attribute attr ->
        ctx.matched <- ctx.matched + 1;
        k |> fattr ctx loc attr
      | _ -> fail loc "tstr_attribute")
;;

let tsig_attribute (T fattr) =
  T
    (fun ctx loc str k ->
      match str.sig_desc with
      | Tsig_attribute attr ->
        ctx.matched <- ctx.matched + 1;
        k |> fattr ctx loc attr
      | _ -> fail loc "tsig_attribute")
;;

let attribute (T fname) (T fpayload) =
  T
    (fun ctx loc attr k ->
      let open Parsetree in
      k |> fname ctx loc attr.attr_name.txt |> fpayload ctx loc attr.attr_payload)
;;

let tstr_docattr (T f) =
  T
    (fun ctx loc subj k ->
      let open Parsetree in
      match subj.str_desc with
      | Tstr_attribute
          { attr_payload =
              Parsetree.PStr
                [ { pstr_desc =
                      Pstr_eval
                        ( { pexp_desc = Pexp_constant (Pconst_string (docstr, _, None)) }
                        , _ )
                  }
                ]
          } ->
        ctx.matched <- ctx.matched + 1;
        k |> f ctx loc docstr
      | _ -> fail loc "tstr_docattr")
;;

let tsig_docattr (T f) =
  T
    (fun ctx loc subj k ->
      let open Parsetree in
      match subj.sig_desc with
      | Tsig_attribute
          { attr_payload =
              Parsetree.PStr
                [ { pstr_desc =
                      Pstr_eval
                        ( { pexp_desc = Pexp_constant (Pconst_string (docstr, _, None)) }
                        , _ )
                  }
                ]
          } ->
        ctx.matched <- ctx.matched + 1;
        k |> f ctx loc docstr
      | _ -> fail loc "tsig_docattr")
;;

let payload_pstr (T fstr) =
  of_func (fun ctx loc subj k ->
    match subj with
    | Parsetree.PStr stru -> k |> fstr ctx loc stru
    | _ -> fail loc __FUNCTION__)
;;

let parse_conde cases loc =
  let pats =
    match cases with
    | [] -> failwith "Bad argument"
    | h :: tl -> List.fold_left ~f:( ||| ) ~init:h tl
  in
  parse pats loc
;;

type context = Ast_pattern0.context

let fail = fail
