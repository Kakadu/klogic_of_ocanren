open Stdppx
open AST

let log fmt =
  if true
  then Format.kasprintf (Format.printf "%s\n%!") fmt
  else Format.ifprintf Format.std_formatter fmt
;;

(*
   let parse_term fself =
   Tast_pattern.(
   parse_conde
   [ texp_apply1
          (texp_ident
             (choice
                [ path [ "OCanren!"; "Std"; "nil" ]
                ; path [ "OCanren"; "Std"; "List"; "nil" ]
                ; path [ "OCanren"; "Std"; "nil" ]
                ]))
          drop
        |> map0 ~f:T_list_nil
      ; texp_apply2
          (texp_ident
             (choice
                [ path [ "OCanren!"; "Std"; "%" ]
                ; path [ "OCanren"; "Std"; "%" ]
                ; path [ "OCanren"; "Std"; "List"; "cons" ]
                ]))
          __
          __
        |> map2 ~f:(fun a b -> T_list_cons (a, b))
      ; texp_apply1
          (texp_ident (path [ "OCanren!"; "!!" ] ||| path [ "OCanren"; "!!" ]))
          (eint __)
        |> map1 ~f:(fun n -> T_int n)
      ; texp_apply_nolabelled __ __
        |> map2 ~f:(fun x args -> Tapp (x, List.map ~f:helper args))
      ; texp_ident __ |> map1 ~f:(fun x -> Tident x)
      ; __
        |> map1 ~f:(fun x ->
             Format.printf "Other parsed: @[%a@]\n%!" MyPrinttyped.expr x;
             Other x)
      ])
   ;; *)

let translate_expr fallback : (unit, ('a ast as 'a)) Tast_folder.t =
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

    let _pat_st_abstr () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_function
        (case
           (tpat_var (string "st"))
           none
           (* (texp_function (case tpat_unit none __ ^:: nil)) *)
           __
        ^:: nil)
      |> map1 ~f:(fun x -> St_abstr x)
    ;;

    let _pat_st_app () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_apply1 __ (texp_ident (path [ "st" ])) |> map1 ~f:(fun x -> St_app x)
    ;;

    let _pat_new_scope () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_let (value_binding (tpat_var (string "st")) drop ^:: nil) __
      |> map1 ~f:(fun x -> New_scope x)
    ;;

    let _pat_mplus () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply2
        (texp_ident (path [ "OCanren!"; "mplus" ] ||| path [ "OCanren"; "mplus" ]))
        __
        __
      |> map2 ~f:(fun x y -> Mplus (x, y))
    ;;

    let pat_standart_operator ~name ~mk :
      (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t
      =
      texp_apply2
        (texp_ident (path [ "OCanren!"; name ] ||| path [ "OCanren"; name ]))
        __
        __
      |> map2 ~f:mk
    ;;

    let pat_unify () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      pat_standart_operator ~name:"===" ~mk:(fun x y -> Unify (x, y))
    ;;

    let pat_diseq () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      pat_standart_operator ~name:"=/=" ~mk:(fun x y -> Diseq (x, y))
    ;;

    let _pat_bind () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply2
        (texp_ident (path [ "OCanren!"; "bind" ] ||| path [ "OCanren"; "bind" ]))
        __
        __
      |> map2 ~f:(fun x y -> Bind (x, y))
    ;;

    let pat_call () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_apply_nolabelled (texp_ident __) __
      |> map2 ~f:(fun f args -> (* TODO: type analysis *)
                                Call_rel (f, args))
    ;;

    let pat_conde () : _ =
      texp_apply1 (texp_ident (path [ "OCanren"; "conde" ])) (texp_list __)
      |> map1 ~f:(fun xs ->
        (* log "conde constructed with %d args" (List.length xs); *)
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
      |> map2 ~f:(fun x y -> Infix_conj2 (x, y))
    ;;

    let pat_abstraction () =
      of_func (fun _ctx _loc e k ->
        let rec helper acc e =
          match e.Typedtree.exp_desc with
          | Texp_function
              { cases = [ { c_lhs = { pat_desc = Tpat_var (_, { txt }) }; c_rhs } ] } ->
            (match Types.get_desc e.exp_type with
            | Tarrow (_, tl, _tr, _) -> helper ((txt, tl) :: acc) c_rhs
            | _ -> fail e.exp_loc "pat_abstraction")
          | _ ->
            (match acc with
            | [] -> fail e.exp_loc "pat_abstraction"
            | _ -> List.rev acc, e)
        in
        k (Tabstr (helper [] e)))
    ;;

    type fresh_rez =
      | Call_fresh of (string * Types.type_expr) list * Typedtree.expression

    let pat_fresh () : _ =
      let ( ** ) lhs rhs = texp_lambda (tpat_var lhs) rhs in
      choice
        [ texp_apply1
            (texp_ident (path [ "OCanren"; "Fresh"; "one" ]))
            (texp_ascription (__ ** __) (__ @-> drop))
          |> map3 ~f:(fun name rhs typ ->
            (* log "%d: %a\n" __LINE__ Printtyp.type_expr typ; *)
            Call_fresh ([ name, typ ], rhs))
        ; texp_apply1
            (texp_ident (path [ "OCanren"; "Fresh"; "two" ]))
            (texp_ascription (__ ** __ ** __) (as__ (__ @-> __ @-> drop)))
          |> map6 ~f:(fun name1 name2 rhs _typ typ1 typ2 ->
            (* log "%d: %a\n" __LINE__ Printtyp.type_expr typ; *)
            Call_fresh ([ name1, typ1; name2, typ2 ], rhs))
        ; texp_apply1
            (texp_ident (path [ "OCanren"; "Fresh"; "three" ]))
            (texp_ascription
               (__ ** __ ** __ ** __ |> pack3)
               (as__ (__ @-> __ @-> __ @-> drop |> pack3)))
          |> map4 ~f:(fun (name1, name2, name3) rhs _typ (typ1, typ2, typ3) ->
            (* log "%d: %a\n" __LINE__ Printtyp.type_expr typ; *)
            Call_fresh ([ name1, typ1; name2, typ2; name3, typ3 ], rhs))
          (*  *)
        ; (let ( ** ) lhs rhs = texp_lambda (tpat_var lhs) rhs in
           texp_apply1
             (texp_ident (path [ "OCanren"; "Fresh"; "four" ]))
             (texp_ascription
                (__ ** __ ** __ ** __ ** __ |> pack4)
                (__ @-> __ @-> __ @-> __ @-> drop |> pack4))
           |> map3 ~f:(fun (name1, name2, name3, name4) rhs (t1, t2, t3, t4) ->
             Call_fresh ([ name1, t1; name2, t2; name3, t3; name4, t4 ], rhs)))
        ; (let ( ** ) lhs rhs = texp_lambda (tpat_var lhs) rhs in
           texp_apply1
             (texp_ident (path [ "OCanren"; "Fresh"; "five" ]))
             (texp_ascription
                (__ ** __ ** __ ** __ ** __ ** __ |> pack5)
                (__ @-> __ @-> __ @-> __ @-> __ @-> drop |> pack5))
           |> map3 ~f:(fun (name1, name2, name3, name4, name5) rhs (t1, t2, t3, t4, t5) ->
             Call_fresh ([ name1, t1; name2, t2; name3, t3; name4, t4; name5, t5 ], rhs)))
        ]
      |> map1 ~f:(function Call_fresh (pats, rhs) -> Fresh (pats, rhs))
    ;;

    let pat_wildcard () : _ =
      texp_apply1
        (texp_ident (path [ "OCanren"; "wc" ]))
        (texp_ascription (texp_lambda (tpat_var __) __) (__ @-> drop))
      |> map3 ~f:(fun name rhs typ -> Wildcard (name, typ, rhs))
    ;;

    let tnil () =
      texp_apply1
        (texp_ident
           (choice
              [ path [ "OCanren!"; "Std"; "nil" ]
              ; path [ "OCanren"; "Std"; "List"; "nil" ]
              ; path [ "OCanren"; "Std"; "nil" ]
              ]))
        drop
      |> map0 ~f:T_list_nil
    ;;

    let tcons () =
      texp_apply2
        (texp_ident
           (choice
              [ path [ "OCanren!"; "Std"; "%" ]
              ; path [ "OCanren"; "Std"; "%" ]
              ; path [ "OCanren"; "Std"; "List"; "cons" ]
              ]))
        __
        __
      |> map2 ~f:(fun a b -> T_list_cons (a, b))
    ;;

    (* let tsingleton () =
      texp_apply1
        (texp_ident
           (choice [ path [ "OCanren!"; "Std"; "!<" ]; path [ "OCanren"; "Std"; "!<" ] ]))
        __
      |> map1 ~f:(fun a -> T_list_singleton a)
    ;; *)

    let tint () =
      texp_apply1
        (texp_ident (path [ "OCanren!"; "!!" ] ||| path [ "OCanren"; "!!" ]))
        (eint __)
      |> map1 ~f:(fun n -> T_int n)
    ;;

    let tstring () =
      texp_apply1
        (texp_ident (path [ "OCanren!"; "!!" ] ||| path [ "OCanren"; "!!" ]))
        (estring __)
      |> map1 ~f:(fun n -> T_string n)
    ;;

    let tbool () =
      texp_apply1
        (texp_ident (path [ "OCanren!"; "!!" ] ||| path [ "OCanren"; "!!" ]))
        ebool
      |> map1 ~f:(fun n -> T_bool n)
    ;;

    let tunit () = texp_construct (lident (string "()")) drop nil |> map0 ~f:Tunit
    let tident () = texp_ident __ |> map1 ~f:(fun x -> Tident x)

    let pat () =
      choice
        [ tnil ()
        ; tcons () (* ; tsingleton () *)
        ; tint ()
        ; tbool ()
        ; tstring ()
        ; pat_pause ()
        ; pat_fresh ()
        ; pat_wildcard ()
        ; pat_conj2 ()
        ; pat_conj_many ()
          (* ; pat_st_abstr () *)
          (* ; pat_st_app () *)
        ; pat_unify ()
        ; pat_diseq ()
        ; pat_conde ()
        ; pat_call ()
        ; tident ()
        ; tunit ()
        ; pat_abstraction ()
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
        match expr.exp_desc with
        | Texp_open (_, rhs) -> self.expr self inh rhs
        | _ ->
          let ast =
            (* log "%d:  @[%a@]\n" __LINE__ MyPrinttyped.expr expr; *)
            (* log "%d:  @[%a@]\n" __LINE__ Printtyp.type_expr expr.Typedtree.exp_type; *)
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

let do_skip_vb vb = Tast_folder.has_attr "skip_from_klogic" vb.Typedtree.vb_attributes

let do_skip_structure_item item =
  match item.Typedtree.str_desc with
  | Tstr_module { mb_attributes = attrs } | Tstr_eval (_, attrs) ->
    Tast_folder.has_attr "skip_from_klogic" attrs
  | _ ->
    Format.printf
      "Check: @[%a@] as false \n"
      Pprintast.structure
      (Untypeast.untype_structure
         { str_items = [ item ]; str_type = []; str_final_env = Env.empty });
    false
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
  let on_type_mangle_spec inh_info payl ~k =
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
      k (helper [] e)
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
      (fun self inh si ->
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
                match AST.simplify_ast rez with
                (* | Error -> Format.eprintf "an error in value_binding name = %s\n%!" name *)
                | rez ->
                  let rvb = Rvb.mk name args rez in
                  Inh_info.add_rvb inh rvb;
                  Format.printf "\027[m@[%a\027[m\n" (Pp_kotlin.pp_rvb_as_kotlin inh) rvb
                (* Format.printf
                     "\027[31m@[<v 2>%a@]@ %!\027[m"
                     (AST.Fold_syntax_macro.pp inh)
                     AST.Fold_syntax_macro.(upper @@ transform rez) *)
              in
              (), si)
          | { Typedtree.vb_pat =
                { pat_desc = Tpat_construct ({ txt = Lident "()" }, _, _, _); _ }
            ; _
            }
          | { Typedtree.vb_pat = { pat_desc = Tpat_any; _ }; _ } -> (), si
          | vb ->
            Format.eprintf
              "Unsupported: %a\n"
              Pprintast.pattern
              (Untypeast.untype_pattern vb.vb_pat);
            assert false
        in
        if do_skip_structure_item si
        then (), si
        else
          Tast_pattern.(
            parse
              (choice
                 [ as__ (tstr_value __)
                   |> map2 ~f:(fun si vbs ->
                     if do_skip_structure_item si
                     then (), si
                     else (
                       let _ =
                         List.iter
                           ~f:(fun x ->
                             if do_skip_vb x then () else ignore (on_rel_decl x))
                           vbs
                       in
                       (), si))
                 ; tstr_module
                     __
                     (tmod_functor
                        (tfun_param_named __ (tmodule_type_ident (lident __)))
                        (tmod_ascription
                           (tmod_structure __)
                           (tmodule_type_ident (lident __))))
                   |> map5 ~f:(fun (name : Ident.t) arg_name arg_typ mod_body typ ->
                     let name = Ident.name name in
                     let arg_name = Ident.name arg_name in
                     let new_inh_info = Inh_info.create () in
                     let _, _ = self.stru self new_inh_info mod_body in
                     Inh_info.add_functor ~name ~typ ~arg_name ~arg_typ inh new_inh_info;
                     (* functor logging *)
                     Format.printf
                       "%a"
                       (Pp_kotlin.pp_functor_as_kotlin ~name ~typ ~arg_name ~arg_typ inh)
                       (List.rev new_inh_info.rvbs);
                     (), si)
                 ; tstr_attribute (attribute (string "klogic.ident.mangle") __)
                   |> map1 ~f:(fun attr_payload ->
                     print_endline "klogic.ident.mangle";
                     on_type_mangle_spec inh attr_payload ~k:(Inh_info.add_expr_hints inh);
                     (), si)
                 ])
              si.str_loc)
            si
            Fun.id
            ~on_error:(fun _ ->
              match si.str_desc with
              (*           | Tstr_value (_, [ vb ]) -> on_rel_decl vb
                           | Tstr_value (_, (_ :: _ :: _ as vbs)) ->
                           List.iter vbs ~f:(fun x ->
                           let _, _ = on_rel_decl x in
                           ());
                           (), si *)
              | Tstr_value (_, []) ->
                Printf.ksprintf failwith "Should not happen (%s %d)" __FILE__ __LINE__
              | Tstr_attribute
                  { attr_name = { txt = "klogic.preamble" | "klogic.prologue"; _ }
                  ; attr_payload =
                      Parsetree.PStr
                        [ { pstr_desc =
                              Pstr_eval
                                ( { pexp_desc =
                                      Pexp_constant
                                        (Pconst_string (s, _, (None | Some "")))
                                  ; _
                                  }
                                , _ )
                          ; _
                          }
                        ]
                  ; _
                  } ->
                Inh_info.add_preamble Kotlin inh s;
                (), si
              | Tstr_attribute
                  { attr_name = { txt = "scheme.preamble" | "scheme.prologue"; _ }
                  ; attr_payload =
                      Parsetree.PStr
                        [ { pstr_desc =
                              Pstr_eval
                                ( { pexp_desc =
                                      Pexp_constant
                                        (Pconst_string (s, _, (None | Some "")))
                                  ; _
                                  }
                                , _ )
                          ; _
                          }
                        ]
                  ; _
                  } ->
                Inh_info.add_preamble Scheme inh s;
                (), si
              | Tstr_attribute
                  { attr_name = { txt = "klogic.epilogue"; _ }
                  ; attr_payload =
                      Parsetree.PStr
                        [ { pstr_desc =
                              Pstr_eval
                                ( { pexp_desc =
                                      Pexp_constant
                                        (Pconst_string (s, _, (None | Some "")))
                                  ; _
                                  }
                                , _ )
                          ; _
                          }
                        ]
                  ; _
                  } ->
                Inh_info.add_epilogue Kotlin inh s;
                (), si
              | Tstr_attribute
                  { attr_name = { txt = "klogic.type.mangle"; _ }; attr_payload; _ } ->
                log "%s\n%!" "klogic.type.mangle";
                on_type_mangle_spec inh attr_payload ~k:(Inh_info.add_hints inh);
                (* TODO: specify mangling of names as an attribute *)
                (), si
              | Tstr_modtype
                  { mtd_type = Some { mty_desc = Tmty_signature sign; _ }
                  ; mtd_name = { txt; _ }
                  ; _
                  } ->
                Inh_info.add_modtype inh txt sign;
                (* modtype logging *)
                Format.printf "%a" (Pp_kotlin.pp_modtype_as_kotlin inh txt) sign;
                (* log "%s %d" __FILE__ __LINE__; *)
                (), si
              | Tstr_attribute _ | Tstr_type _ | Tstr_open _ -> (), si
              | _ ->
                Format.eprintf
                  "%a\n%!"
                  Pprintast.structure_item
                  (MyUntype.untype_stru_item si);
                Printf.ksprintf
                  failwith
                  "Not implemented in 'folder' (%s %d)"
                  __FILE__
                  __LINE__))
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
    let ppf = Format.formatter_of_out_channel ch in
    match translate_implementation stru with
    | Error _ -> assert false
    | Ok info ->
      (match Trans_config.config.lang with
      | Trans_config.Kotlin ->
        Printf.fprintf ch "%s\n" (Inh_info.get_preamble Trans_config.Kotlin info);
        Printf.fprintf ch "// There are %d relations\n" (List.length info.Inh_info.rvbs);
        Inh_info.iter_vbs info ~f:(Pp_kotlin.pp_item ~toplevel:true info ppf);
        Printf.fprintf ch "%s\n" (Inh_info.get_epilogue Trans_config.Kotlin info);
        Format.pp_print_flush ppf ();
        flush ch
      | Scheme ->
        Format.fprintf ppf "%a%!" Pp_scheme.pp info;
        Format.pp_print_flush ppf ();
        flush ch))
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
