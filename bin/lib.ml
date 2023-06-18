open Stdppx

let log fmt =
  if true
  then Format.kasprintf (Format.printf "%s\n%!") fmt
  else Format.ifprintf Format.std_formatter fmt
;;

type 'a term =
  | T_int of int
  | T_list_init of 'a list
  | T_list_nil
  | T_list_cons of 'a * 'a
  | Tident of Path.t
  | Tapp of 'a * 'a list
  | Tother of Typedtree.expression

type 'a ast =
  | Pause of 'a
  | St_abstr of 'a
  | St_app of 'a
  | Mplus of 'a * 'a
  | Bind of 'a * 'a
  | Fresh of string list * 'a
  | Unify of ('t term as 't) * 't
  | Call_rel of Path.t * ('t term as 't) list
  | Other of Typedtree.expression
  | Error

(** Relational value bindings *)
module Rvb = struct
  type t =
    { name : string
    ; args : (string * Types.type_expr) list
    ; body : 'a ast as 'a
    }

  let mk name args body = { name; args; body }
end

let pp_comma_list ppf =
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",") ppf
;;

[@@@ocaml.warnerror "-11"]

let pp_term_as_kotlin =
  let open Format in
  let rec helper ppf = function
    | T_int n -> fprintf ppf "%d" n
    (* | _ -> fprintf ppf "%d" 42 *)
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "logicListOf()"
    | T_list_cons (h, tl) -> fprintf ppf "@[(%a + %a)@]" helper h helper tl
    | Tident p -> fprintf ppf "%a" Printtyp.path p
    | Tapp (f, args) -> fprintf ppf "@[%a(%a)@]" helper f (pp_comma_list helper) args
    | Tother e -> fprintf ppf "{| %a |}" Pprintast.expression (MyUntype.expr e)
  in
  helper
;;

let map_ast f = function
  | Pause x -> Pause (f x)
  | St_abstr e -> St_abstr (f e)
  | St_app e -> St_app (f e)
  | Fresh (xs, e) -> Fresh (xs, f e)
  | Mplus (a, b) -> Mplus (f a, f b)
  | Bind (a, b) -> Bind (f a, f b)
  | (Call_rel _ | Unify _ | Other _ | Error) as other -> other
;;

let pp_ast_as_kotlin =
  let open Format in
  let rec helper ppf = function
    | Pause e -> fprintf ppf "@[pause { %a@ }@]" helper e
    | St_abstr l -> fprintf ppf "@[<v 2>@[{ st ->@ %a@ }@]" helper l
    | St_app l -> fprintf ppf "%a(st)" helper l
    | Mplus (l, r) ->
      fprintf ppf "@[<v 2>@[mplus(@]@,@[%a,@]@,@[%a@]@[)@]@]" helper l helper r
    | Bind (l, r) ->
      fprintf ppf "@[<v 2>@[bind(@]@,@[%a@]@,@[%a@]@ @[)@]@]" helper l helper r
    | Fresh (xs, e) ->
      fprintf
        ppf
        "@[<v 2>@[fresh { %a ->@]@,@[%a@]@[}@]@]"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_print_string)
        xs
        helper
        e
    | Unify (l, r) ->
      (* fprintf ppf "@[(@[%a@]@ `===`@ @[%a@])@]" pp_term_as_kotlin l pp_term_as_kotlin r *)
      fprintf ppf "(%a `===` %a)" pp_term_as_kotlin l pp_term_as_kotlin r
    | Call_rel (p, args) ->
      fprintf ppf "@[%a(%a)@]" Printtyp.path p (pp_comma_list pp_term_as_kotlin) args
    | Other e -> fprintf ppf "@[{| Other %a |}@]" Pprintast.expression (MyUntype.expr e)
    | Error -> fprintf ppf "ERROR "
  in
  helper
;;

let pp_typ_as_kotlin ppf typ =
  match Format.asprintf "%a" Printtyp.type_expr typ with
  | s -> Format.fprintf ppf "%s" s
;;

let pp_rvb_as_kotlin ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_comma_list
      (fun ppf (name, typ) -> fprintf ppf "%s: %a" name pp_typ_as_kotlin typ)
      ppf
  in
  Format.fprintf
    ppf
    "@[<v 2>@[fun %s(%a) =@]@ @[%a@]@]\n%!"
    name
    pp_args
    args
    pp_ast_as_kotlin
    body
;;

let translate_term =
  let open Typedtree in
  let rec helper e =
    Tast_pattern.(
      parse_conde
        [ texp_apply1
            (texp_ident
               (path [ "OCanren!"; "Std"; "nil" ] ||| path [ "OCanren"; "Std"; "nil" ]))
            drop
          |> map0 ~f:T_list_nil
        ; texp_apply2
            (texp_ident
               (path [ "OCanren!"; "Std"; "%" ] ||| path [ "OCanren"; "Std"; "%" ]))
            __
            __
          |> map2 ~f:(fun a b -> T_list_cons (helper a, helper b))
        ; texp_apply_nolabelled __ __
          |> map2 ~f:(fun x args -> Tapp (helper x, List.map ~f:helper args))
        ; texp_ident __ |> map1 ~f:(fun x -> Tident x)
        ; __ |> map1 ~f:(fun x -> Tother x)
        ])
      e.exp_loc
      e
      Fun.id
  in
  helper
;;

let translate_expr fallback : (unit, _ ast) Tast_folder.t =
  let open struct
    open Tast_pattern

    let pat_pause () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_apply1
        (texp_ident (path [ "OCanren"; "pause" ] ||| path [ "OCanren!"; "pause" ]))
        (texp_function (case tpat_unit drop __ ^:: nil))
      |> map1 ~f:(fun x -> Pause x)
    ;;

    let pat_st_abstr () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_function
        (case
           (tpat_var (string "st"))
           none
           (* (texp_function (case tpat_unit none __ ^:: nil)) *)
           __
        ^:: nil)
      |> map1 ~f:(fun x -> St_abstr x)
    ;;

    let pat_st_app () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_apply1 __ (texp_ident (path [ "st" ])) |> map1 ~f:(fun x -> St_app x)
    ;;

    let pat_mplus () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_let (value_binding drop drop ^:: nil)
      @@ texp_apply2
           (texp_ident (path [ "OCanren!"; "mplus" ] ||| path [ "OCanren"; "mplus" ]))
           __
           __
      |> map2 ~f:(fun x y -> Mplus (x, y))
    ;;

    let pat_unify () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply2
        (texp_ident (path [ "OCanren!"; "===" ] ||| path [ "OCanren"; "===" ]))
        __
        __
      |> map2 ~f:(fun x y -> Unify (translate_term x, translate_term y))
    ;;

    let pat_bind () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply2
        (texp_ident (path [ "OCanren!"; "bind" ] ||| path [ "OCanren"; "bind" ]))
        __
        __
      |> map2 ~f:(fun x y -> Bind (x, y))
    ;;

    let pat_call () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply_nolabelled (texp_ident __) __
      |> map2 ~f:(fun f args -> Call_rel (f, List.map ~f:translate_term args))
    ;;

    let pat_fresh () : _ =
      let rec helper acc e =
        parse
          (texp_let
             (value_binding
                (tpat_var __)
                (texp_apply1
                   (texp_ident (path [ "OCanren"; "State"; "fresh" ]))
                   (texp_ident (path [ "st" ])))
             ^:: nil)
             __
          |> map2 ~f:(fun a b -> `Let (a, b))
          ||| (__ |> map1 ~f:(fun x -> `Other x)))
          e.Typedtree.exp_loc
          e
          ~on_error:(fun _ -> failwith "should not happen")
          (fun rez ->
            match rez, acc with
            | `Other _, [] -> fail e.exp_loc ""
            | `Other e, acc -> Fresh (List.rev acc, e)
            | `Let (name, e), acc -> helper (name :: acc) e)
      in
      of_func (fun _ctx _loc e k -> k (helper [] e))
    ;;

    let pat () =
      pat_pause ()
      ||| pat_mplus ()
      ||| pat_bind ()
      ||| pat_st_abstr ()
      ||| pat_st_app ()
      ||| pat_fresh ()
      ||| pat_unify ()
      ||| pat_call ()
    ;;
  end in
  Printf.printf "%s %d\n" __FILE__ __LINE__;
  let open Tast_folder in
  { fallback with
    expr =
      (fun self inh expr ->
        let open Typedtree in
        let loc = expr.exp_loc in
        let ast =
          Tast_pattern.parse
            (pat ())
            loc
            ~on_error:(fun _desc () -> Other expr)
            expr
            (fun ast () ->
              match ast with
              | _ -> ast)
            ()
        in
        map_ast (fun e -> fst (self.expr self inh e)) ast, expr
        (* match ast with
        | Pause e -> self.expr self inh e
        | St_abstr e -> self.expr self inh e
        | Mplus (a, b) -> failwith "mplus not supported"
        | Other e -> Other e, expr
        | Error -> Error, expr) *))
  ; stru_item =
      (fun _self _inh _si ->
        assert false
        (* match si.str_desc with
        | Tstr_attribute _ -> ()
        | _ -> self.stru_item self inh si *))
  }
;;

let translate fallback : (Rvb.t list ref, unit) Tast_folder.t =
  let extract_rel_arguments n e =
    let rec helper n acc e =
      if n <= 0
      then List.rev acc, e
      else
        Tast_pattern.(parse (texp_function (case (tpat_var_type __ __) none __ ^:: nil)))
          Location.none
          e
          (fun name typ body -> helper (n - 1) ((name, typ) :: acc) body)
          ~on_error:(fun _ -> assert false)
    in
    helper n [] e
  in
  let expr_is_a_goal (e : Typedtree.expression) =
    let rec helper acc : Types.type_expr -> _ =
     fun e ->
      Tast_pattern.parse
        Tast_pattern.(
          typ_arrow drop __
          |> map1 ~f:(fun x -> `Arr x)
          ||| (typ_constr (path [ "OCanren"; "goal" ]) nil
              ||| typ_arrow
                    (typ_constr (path [ "OCanren"; "State"; "t" ]) nil)
                    (typ_constr (path [ "OCanren"; "Stream"; "t" ]) drop)
              |> map0 ~f:`Goal))
        Location.none
        e
        (fun x ->
          match x with
          | `Goal -> Some acc
          | `Arr x -> helper (acc + 1) x)
        ~on_error:(fun _ -> None)
    in
    Format.eprintf
      "@[<2>Check expr_is_a_goal:@,%a@]\n"
      Printtyp.type_expr
      e.Typedtree.exp_type;
    helper 0 e.Typedtree.exp_type
  in
  Printf.printf "%s %d\n" __FILE__ __LINE__;
  let on_type_mangle_spec payl =
    match payl with
    | Parsetree.PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] ->
      let open Ppxlib.Ast_pattern in
      let rec helper acc e =
        parse
          (pexp_construct (lident (string "::")) none
          |>

          |||
          pexp_construct
             (lident (string "::"))
             (some
                (pexp_tuple
                   (pexp_tuple
                      (pexp_constant (pconst_string __ drop none)
                      ^:: pexp_constant (pconst_string __ drop none)
                      ^:: nil)
                   ^:: __
                   ^:: nil))))
          e.Parsetree.pexp_loc
          e
          (fun key v rest -> helper acc rest)
      in
      helper [] e
    | _ -> ()
  in
  let open Tast_folder in
  { fallback with
    expr =
      (fun _self _inh expr ->
        let _ =
          let te = translate_expr Tast_folder.default in
          te.expr te () expr
        in
        (), expr)
  ; stru_item =
      (fun _self inh si ->
        let on_rel_decl = function
          | { Typedtree.vb_pat = { pat_desc = Tpat_var (_, { txt = name; _ }); _ }; _ } as
            vb ->
            (match expr_is_a_goal vb.vb_expr with
             | None ->
               Format.eprintf "Not a goal: %s\n%!" name;
               (), si
             | Some argcount ->
               (* we need extract arguments and run on expression *)
               let iter_expr = translate_expr Tast_folder.default in
               let args, body = extract_rel_arguments argcount vb.vb_expr in
               let rez, _ = iter_expr.expr iter_expr () body in
               let () =
                 match rez with
                 | Error -> Format.eprintf "an error in value_binding name = %s\n%!" name
                 | rez ->
                   let rvb = Rvb.mk name args rez in
                   inh := rvb :: !inh;
                   Format.printf "%a\n" pp_rvb_as_kotlin rvb
               in
               (), si)
          | _ -> assert false
        in
        match si.str_desc with
        | Tstr_value (_, [ vb ]) -> on_rel_decl vb
        | Tstr_value (_, (_ :: _ :: _ as vbs)) ->
          List.iter vbs ~f:(fun x ->
            let _, _ = on_rel_decl x in
            ());
          (), si
        | Tstr_value (_, []) ->
          Printf.ksprintf failwith "Should not happen (%s %d)" __FILE__ __LINE__
        | Tstr_attribute
            { attr_name = { txt = "klogic.type.mangle"; _ }; attr_payload; _ } ->
          log "%s\n%!" "klogic.type.mangle";
          on_type_mangle_spec attr_payload;
          (* TODO: specify mangling of names as an attribute *)
          (), si
        | Tstr_attribute _ | Tstr_type _ | Tstr_open _ -> (), si
        | _ ->
          Format.eprintf "%a\n%!" Pprintast.structure_item (MyUntype.untype_stru_item si);
          Printf.ksprintf failwith "Not implemented in 'folder' (%s %d)" __FILE__ __LINE__
        (* self.stru_item self inh si *))
  }
;;

let translate_implementation stru =
  let acc = ref [] in
  let folder = translate Tast_folder.default in
  let _rez, _ = folder.Tast_folder.stru folder acc stru in
  Stdlib.Result.Ok (List.rev !acc)
;;

let analyze_cmt source_file stru =
  Out_channel.with_file "asdf.kt" ~f:(fun ch ->
    match translate_implementation stru with
    | Stdlib.Result.Ok xs ->
      Printf.fprintf ch "// There are %d realtions\n" (List.length xs);
      let ppf = Format.formatter_of_out_channel ch in
      List.iter ~f:(pp_rvb_as_kotlin ppf) xs
    | Error _ -> assert false)
;;

let run source_file =
  let _cmi_info, cmt_info = Cmt_format.read source_file in
  Option.iter cmt_info ~f:(fun cmt ->
    match cmt.Cmt_format.cmt_annots with
    | Cmt_format.Implementation stru -> analyze_cmt source_file stru
    | Cmt_format.Interface _
    | Cmt_format.Packed _
    | Cmt_format.Partial_implementation _
    | Cmt_format.Partial_interface _ ->
      Printf.eprintf "%s %d\n%!" Caml.__FILE__ Caml.__LINE__;
      Caml.exit 1)
;;
