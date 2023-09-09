open Stdppx
open AST

let log fmt =
  if true
  then Format.kasprintf (Format.printf "%s\n%!") fmt
  else Format.ifprintf Format.std_formatter fmt
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
        (texp_ident
           (choice
              [ path [ "OCanren"; "pause" ]
              ; path [ "OCanren!"; "pause" ]
              ; path [ "OCanren!"; "delay" ]
              ; path [ "OCanren"; "delay" ]
              ]))
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
      |> map2 ~f:(fun x y ->
           log "Unification constructed";
           Unify (translate_term x, translate_term y))
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
      |> map2 ~f:(fun f args ->
           log "Call constructed";
           Call_rel (f, List.map ~f:translate_term args))
    ;;

    let pat_conde () : _ =
      texp_apply1 (texp_ident (path [ "OCanren"; "conde" ])) (texp_list __)
      |> map1 ~f:(fun xs ->
           log "conde constructed with %d args" (List.length xs);
           Conde xs)
    ;;

    let pat_conj_many () : _ =
      texp_apply1 (texp_ident (path [ "OCanren"; "?&" ])) (texp_list __)
      |> map1 ~f:(fun xs ->
           (* log "conde constructed with %d args" (List.length xs); *)
           Conj_multi xs)
    ;;

    let pat_conj2 () : _ =
      texp_apply2
        (texp_ident (choice [ path [ "OCanren"; "&&&" ]; path [ "OCanren!"; "&&&" ] ]))
        __
        __
      |> map2 ~f:(fun l r -> Infix_conj2 (l, r))
    ;;

    let pat_fresh () : _ =
      (* log "%d helper: @[%a@]\n" __LINE__ MyPrinttyped.expr e; *)
      choice
        [ texp_apply1
            (texp_ident
               (path [ "OCanren"; "Fresh"; "one" ])
               (* ||| texp_ident (path [ "Fresh"; "one" ]) *)
               (* ||| texp_ident (path [ "OCanren"; "Fresh"; "one" ]) *))
            (as__ (texp_function (case (tpat_var __) none __ ^:: nil)))
          |> map3 ~f:(fun name func rhs () ->
               log "%s %d" __FILE__ __LINE__;
               `Call_fresh (name, func, rhs))
          (*    ; __
               |> map1 ~f:(fun x () ->
                    log "%s %d" __FILE__ __LINE__;
                    `Other x) *)
        ]
      |> map1 ~f:(fun rez ->
           match rez () with
           | `Other _ -> fail Location.none ""
           | `Call_fresh (_, name, rhs) -> Fresh ([ name, Predef.type_int ], rhs)
           (* | `Let (name, rhs_expr, e), acc ->
              helper ((name, rhs_expr.Typedtree.exp_type) :: acc) e *))
    ;;

    let pat () =
      choice
        [ pat_pause ()
        ; pat_fresh ()
          (* ; pat_new_scope () *)
          (* ; pat_mplus () *)
          (* ; pat_bind () *)
        ; pat_conj2 ()
        ; pat_conj_many ()
          (* ; pat_st_abstr () *)
          (* ; pat_st_app () *)
        ; pat_unify ()
        ; pat_conde ()
        ; pat_call ()
        ]
    ;;
  end in
  (* Printf.printf "%s %d\n" __FILE__ __LINE__; *)
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
    (* Format.eprintf
      "@[<2>Check expr_is_a_goal:@,%a@]\n"
      Printtyp.type_expr
      e.Typedtree.exp_type; *)
    helper 0 e.Typedtree.exp_type
  in
  (* Printf.printf "%s %d\n" __FILE__ __LINE__; *)
  let on_type_mangle_spec inh_info payl =
    match payl with
    | Parsetree.PStr [ { pstr_desc = Pstr_eval (e, _); _ } ] ->
      let open Ppxlib.Ast_pattern in
      let rec helper acc e =
        (* log "run helper on %a, acc.length = %d" Pprintast.expression e (List.length acc); *)
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
                   Format.printf "%a\n" (pp_rvb_as_kotlin ~pretty:false inh) rvb;
                   Format.printf
                     "\027[31m@[<v 2>%a@]@ %!\027[m"
                     (AST.Fold_syntax_macro.pp inh)
                     AST.Fold_syntax_macro.(upper @@ transform rez)
               in
               (), si)
          | { Typedtree.vb_pat = { pat_desc = Tpat_any; _ }; _ } -> (), si
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
            { attr_name = { txt = "klogic.preamble" | "klogic.prologue"; _ }
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
            { attr_name = { txt = "klogic.epilogue"; _ }
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
          Inh_info.add_epilogue inh s;
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

let analyze_cmt _source_file out_file stru =
  Out_channel.with_file out_file ~f:(fun ch ->
    match translate_implementation stru with
    | Stdlib.Result.Ok info ->
      Printf.fprintf ch "%s\n" (Inh_info.preamble info);
      Printf.fprintf ch "// There are %d relations\n" (List.length info.Inh_info.rvbs);
      let ppf = Format.formatter_of_out_channel ch in
      Inh_info.iter_vbs info ~f:(function
        | Inh_info.RVB rvb ->
          pp_rvb_as_kotlin ~pretty:Trans_config.(config.pretty) info ppf rvb
        | Plain_kotlin s -> Format.fprintf ppf "%s" s);
      Printf.fprintf ch "%s\n" (Inh_info.epilogue info);
      Format.pp_print_flush ppf ();
      flush ch
    | Error _ -> assert false)
;;

let run source_file out_file =
  let _cmi_info, cmt_info = Cmt_format.read source_file in
  Option.iter cmt_info ~f:(fun cmt ->
    match cmt.Cmt_format.cmt_annots with
    | Cmt_format.Implementation stru -> analyze_cmt source_file out_file stru
    | Cmt_format.Interface _
    | Cmt_format.Packed _
    | Cmt_format.Partial_implementation _
    | Cmt_format.Partial_interface _ ->
      Printf.eprintf "%s %d\n%!" Caml.__FILE__ Caml.__LINE__;
      Caml.exit 1)
;;
