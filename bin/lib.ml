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
  | New_scope of 'a
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
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "logicListOf()"
    | T_list_cons (h, tl) -> fprintf ppf "@[(%a + %a)@]" helper h helper tl
    (* | Tident p -> fprintf ppf "%a" Printtyp.path p *)
    (* TODO: Printtyp.path sometimes fives /n in the end. *)
    | Tident p -> fprintf ppf "%s" (Path.name p)
    | Tapp (f, args) -> fprintf ppf "@[%a(%a)@]" helper f (pp_comma_list helper) args
    | Tother e ->
      fprintf ppf "/* ERROR ? */{|  %a |}" Pprintast.expression (MyUntype.expr e)
  in
  helper
;;

let map_ast f = function
  | Pause x -> Pause (f x)
  | St_abstr e -> St_abstr (f e)
  | St_app e -> St_app (f e)
  | Fresh (xs, e) -> Fresh (xs, f e)
  | New_scope x -> New_scope (f x)
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
    | New_scope x -> helper ppf x
    | Mplus (l, r) ->
      fprintf ppf "@[<v 2>@[mplus(@]@,@[%a,@]@,@[%a@]@[)@]@]" helper l helper r
    | Bind (l, r) ->
      fprintf ppf "@[<v 2>@[bind(@]@,@[%a,@]@,@[%a@]@ @[)@]@]" helper l helper r
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

module Inh_info = struct
  type t =
    { type_mangle_hints : (string, string) Hashtbl.t
    ; mutable rvbs : Rvb.t list
    ; mutable preamble : string
    }

  let create () = { type_mangle_hints = Hashtbl.create 13; rvbs = []; preamble = "" }
  let add_rvb t rvb = t.rvbs <- rvb :: t.rvbs
  let lookup_typ_exn t typ = Hashtbl.find t.type_mangle_hints typ

  let add_hints info hints =
    log "add %d hints" (List.length hints);
    List.iter hints ~f:(fun (key, data) ->
      log "adding a type hint %s -> %s%!" key data;
      Hashtbl.add_exn info.type_mangle_hints ~key ~data)
  ;;

  let iter_vbs { rvbs; _ } ~f = List.iter ~f (List.rev rvbs)
  let add_preamble t s = t.preamble <- t.preamble ^ s
  let preamble { preamble; _ } = preamble
end

let pp_typ_as_kotlin inh_info ppf typ =
  let caml_repr = Format.asprintf "%a" Printtyp.type_expr typ in
  match Inh_info.lookup_typ_exn inh_info caml_repr with
  | s -> Format.fprintf ppf "%s" s
  | exception Not_found -> Format.fprintf ppf "%s" caml_repr
;;

let pp_rvb_as_kotlin inh_info ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
      (fun ppf (name, typ) -> fprintf ppf "%s: %a" name (pp_typ_as_kotlin inh_info) typ)
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
        ; texp_apply1
            (texp_ident (path [ "OCanren!"; "!!" ] ||| path [ "OCanren"; "!!" ]))
            (eint __)
          |> map1 ~f:(fun n -> T_int n)
        ; texp_apply_nolabelled __ __
          |> map2 ~f:(fun x args -> Tapp (helper x, List.map ~f:helper args))
        ; texp_ident __ |> map1 ~f:(fun x -> Tident x)
        ; __
          |> map1 ~f:(fun x ->
               Format.printf "Tother parsed: @[%a@]\n%!" MyPrinttyped.expr x;
               Tother x)
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

    let pat_new_scope () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_let (value_binding (tpat_var (string "st")) drop ^:: nil) __
      |> map1 ~f:(fun x -> New_scope x)
    ;;

    let pat_mplus () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      (* texp_let (value_binding drop drop ^:: nil)
      @@ *)
      texp_apply2
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
      ||| pat_new_scope ()
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
        map_ast (fun e -> fst (self.expr self inh e)) ast, expr)
  ; stru_item = (fun _self _inh _si -> assert false)
  }
;;

let translate fallback : (Inh_info.t, unit) Tast_folder.t =
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
  let on_type_mangle_spec inh_info payl =
    match payl with
    | Parsetree.PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] ->
      let open Ppxlib.Ast_pattern in
      let rec helper acc e =
        log "run helper on %a, acc.length = %d" Pprintast.expression e (List.length acc);
        parse
          (pexp_construct (lident (string "[]")) drop
           |> map0 ~f:None
           ||| (pexp_construct
                  (lident (string "::"))
                  (some
                     (pexp_tuple
                        (pexp_tuple
                           (pexp_constant (pconst_string __ drop none)
                            ^:: pexp_constant (pconst_string __ drop none)
                            ^:: nil)
                         ^:: __
                         ^:: nil)))
                |> map2 ~f:(fun a b -> a, b)
                |> map2 ~f:(fun p tl -> Some (p, tl))))
          e.Parsetree.pexp_loc
          e
          ~on_error:(fun () ->
            Format.eprintf
              "Error during during parsing:\n%a\n%!"
              (Printast.expression 2)
              e;
            assert false)
          (function
           | None -> List.rev acc
           | Some (item, rest) -> helper (item :: acc) rest)
      in
      helper [] e |> Inh_info.add_hints inh_info
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
                   Inh_info.add_rvb inh rvb;
                   Format.printf "%a\n" (pp_rvb_as_kotlin inh) rvb
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
            { attr_name = { txt = "klogic.preamble"; _ }
            ; attr_payload =
                Parsetree.PStr
                  [ { pstr_desc =
                        Pstr_eval
                          ( { pexp_desc =
                                Pexp_constant (Pconst_string (s, _, (None | Some "")))
                            ; _
                            }
                          , _ )
                    ; _
                    }
                  ]
            ; _
            } ->
          Inh_info.add_preamble inh s;
          (), si
        | Tstr_attribute
            { attr_name = { txt = "klogic.type.mangle"; _ }; attr_payload; _ } ->
          log "%s\n%!" "klogic.type.mangle";
          on_type_mangle_spec inh attr_payload;
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
  let folder = translate Tast_folder.default in
  let inh = Inh_info.create () in
  let _, _ = folder.Tast_folder.stru folder inh stru in
  Stdlib.Result.Ok inh
;;

let analyze_cmt _source_file stru =
  Out_channel.with_file "asdf.kt" ~f:(fun ch ->
    match translate_implementation stru with
    | Stdlib.Result.Ok info ->
      Printf.fprintf ch "%s\n" (Inh_info.preamble info);
      Printf.fprintf ch "// There are %d relations\n" (List.length info.Inh_info.rvbs);
      let ppf = Format.formatter_of_out_channel ch in
      Inh_info.iter_vbs ~f:(pp_rvb_as_kotlin info ppf) info
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
