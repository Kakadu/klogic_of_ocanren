open Stdppx

let log fmt =
  if true
  then Format.kasprintf (Format.printf "%s\n%!") fmt
  else Format.ifprintf Format.std_formatter fmt
;;

type 'a ast =
  | Pause of 'a
  | St_abstr of 'a
  | Mplus of 'a * 'a
  | Other of Typedtree.expression
  | Error

let map_ast f = function
  | Pause x -> Pause (f x)
  | St_abstr x -> St_abstr (f x)
  | Mplus (a, b) -> Mplus (f a, f b)
  | (Other _ | Error) as other -> other
;;

let pp_ast_as_kotlin =
  let open Format in
  let rec helper ppf = function
    | Pause e -> fprintf ppf "pause { %a } " helper e
    | St_abstr l -> fprintf ppf "({ st -> %a })" helper l
    | Mplus (l, r) -> fprintf ppf "mplus(%a, %a)" helper l helper r
    | Other e -> fprintf ppf "Other %a" Pprintast.expression (MyUntype.expr e)
    | Error -> fprintf ppf "ERROR "
  in
  helper
;;

let translate_expr fallback : (unit, _ ast) Tast_folder.t =
  let open struct
    open Tast_pattern

    let pat_pause () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_apply1
        (texp_ident (path [ "OCanren!"; "pause" ]))
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

    (*  *)
    let pat_mplus () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_let (value_binding drop drop ^:: nil)
      @@ texp_apply2 (texp_ident (path [ "OCanren!"; "mplus " ])) __ __
      |> map2 ~f:(fun x y -> Mplus (x, y))
    ;;

    let pat () = pat_pause () ||| pat_mplus () ||| pat_st_abstr ()
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
      (fun self inh si ->
        assert false
        (* match si.str_desc with
        | Tstr_attribute _ -> ()
        | _ -> self.stru_item self inh si *))
  }
;;

let translate fallback : (unit, unit) Tast_folder.t =
  let extract_rel_arguments n e =
    let rec helper n acc e =
      if n <= 0
      then List.rev acc, e
      else
        Tast_pattern.(parse (texp_function (case (tpat_var __) none __ ^:: nil)))
          Location.none
          e
          (fun name body -> helper (n - 1) (name :: acc) body)
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
    (*  *)
    (* Format.eprintf "@[<2>Check expr_is_a_goal:@,%a@]\n" MyPrinttyped.expr e; *)
    Format.eprintf
      "@[<2>Check expr_is_a_goal:@,%a@]\n"
      Printtyp.type_expr
      e.Typedtree.exp_type;
    helper 0 e.Typedtree.exp_type
  in
  Printf.printf "%s %d\n" __FILE__ __LINE__;
  let open Tast_folder in
  { fallback with
    expr =
      (fun self inh expr ->
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
                 match rez with
                 | Error -> Format.eprintf "an error in value_binding name = %s\n%!" name
                 | rez ->
                   Format.printf
                     "\n@[fun %s(%d) { %a }@]\n"
                     name
                     (List.length args)
                     pp_ast_as_kotlin
                     rez
               in
               (), si)
          | _ -> assert false
        in
        match si.str_desc with
        | Tstr_value
            ( _
            , [ ({ vb_pat = { pat_desc = Tpat_var (_, { txt = name; _ }); _ }; _ } as vb)
              ] ) ->
          on_rel_decl vb
          (* (match expr_is_a_goal vb.vb_expr with
           | None -> (), si
           | Some argcount ->
             (* we need extract arguments and run on expression *)
             let iter_expr = translate_expr Tast_folder.default in
             let args, body = extract_rel_arguments argcount vb.vb_expr in
             let _ = iter_expr.expr iter_expr () body in
             Format.printf " fun %s(%d) { }\n" name (List.length args);
             (), si) *)
        | Tstr_value (_, (_ :: _ :: _ as vbs)) ->
          List.iter vbs ~f:(fun x ->
            let _, _ = on_rel_decl x in
            ());
          (), si
          (* Format.eprintf "%a\n%!" Pprintast.structure_item (MyUntype.untype_stru_item si);
          Printf.ksprintf failwith "Not implemented in 'folder' (%s %d)" __FILE__ __LINE__ *)
        | Tstr_value (_, []) ->
          Printf.ksprintf failwith "Should not happen (%s %d)" __FILE__ __LINE__
        (* | Tstr_value (_, [ _ ])  *)
        | Tstr_type _ | Tstr_open _ | Tstr_attribute _ -> (), si
        | _ ->
          Format.eprintf "%a\n%!" Pprintast.structure_item (MyUntype.untype_stru_item si);
          Printf.ksprintf failwith "Not implemented in 'folder' (%s %d)" __FILE__ __LINE__
        (* self.stru_item self inh si *))
  }
;;

let analyze_cmt source_file stru =
  Out_channel.with_file "asdf.kt" ~f:(fun _ ->
    let folder = translate Tast_folder.default in
    (* let (_ : int) = folder.Tast_folder.stru in *)
    let _rez, _ = folder.Tast_folder.stru folder () stru in
    ())
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
