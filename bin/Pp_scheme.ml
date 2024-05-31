open Stdppx
open AST

let pp_ast_as_scheme inh_info =
  let path_is_none path =
    (* Format.eprintf "log[path_is_none]: %a\n%!" Path.print path; *)
    String.equal (Format.asprintf "%a" Path.print path) "OCanren!.Std.none"
  in
  let wcs = ref SS.empty in
  let with_wc name f =
    wcs := SS.add name !wcs;
    f ();
    wcs := SS.remove name !wcs
  in
  let once_used = ref SS.empty in
  let with_once_used name f =
    once_used := SS.add name !once_used;
    f ();
    once_used := SS.remove name !once_used
  in
  let open Format in
  let rec helper ?(par = true) ppf = function
    | Pause e -> fprintf ppf "@[pause { %a@ }@]" nopar e
    | St_abstr l -> fprintf ppf "@[<v 2>@[{ st: State ->@ %a@ }@]" default l
    | St_app l -> fprintf ppf "%a(st)" default l
    | New_scope x -> helper ppf x
    | Mplus (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[mplus@]@,@,@[(%a)@])@]" default l default r
    | Bind (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[bind@]@,@[(%a)@])@]" default l default r
    | Fresh ([ (v1, vtyp) ], rhs)
      when match rhs with
           | Pause _ -> false
           | _ -> true ->
      (match check_uses v1 rhs with
      | Uses_count.Once -> with_once_used v1 (fun () -> default ppf rhs)
      | _ ->
        fprintf
          ppf
          "@[freshTypesVars { %s: %a -> %a}]"
          v1
          (pp_typ_as_kotlin inh_info)
          vtyp
          default
          rhs)
    | Fresh (xs, Pause e) ->
      fprintf ppf "@[@[<hov 2>freshTypedVars { ";
      pp_comma_list
        (fun ppf (name, typ) ->
          fprintf ppf "@[%s: %a@]" name (pp_typ_as_kotlin inh_info) typ)
        ppf
        xs;
      fprintf ppf " ->@]@ %a@ @[}@]@]" default e
    | Fresh (xs, e) ->
      (* fprintf ppf "/* NOTE: fresh without delay */@ "; *)
      fprintf ppf "@[<hov>@[freshTypedVars {";
      pp_comma_list
        (fun ppf (name, typ) ->
          fprintf ppf "@[ %s : %a@]" name (pp_typ_as_kotlin inh_info) typ)
        ppf
        xs;
      fprintf ppf " ->@]@ %a@ @[}@]@]" default e
    | Wildcard (v, _t, e) -> with_wc v (fun () -> default ppf e)
    | Unify (l, r) when par ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "(%a `===` %a)" default l default r
    (* fprintf ppf "(%a debugUnify %a)" pp_term_as_kotlin l pp_term_as_kotlin r *)
    | Unify (l, r) ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "%a `===` %a" default l default r
    | Diseq (l, r) when par ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "(%a `!==` %a)" default l default r
    | Diseq (l, r) ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "%a `!==` %a" default l default r
    | Call_rel (path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Call_rel (p, args) ->
      let kotlin_func =
        (* let repr = Format.asprintf "%a" Printtyp.path p in *)
        let repr = Path.name p in
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> Format.asprintf "%a" print_path p
        | s -> s
      in
      fprintf ppf "@[%s(%a)@]" kotlin_func (pp_comma_list default) args
    | Tapp (Tident path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Tapp (f, args) ->
      Format.printf "Application %d\n%!" __LINE__;
      (*  *)
      fprintf ppf "@[%a(%a)@]" default f (pp_comma_list default) args
    | Tident p ->
      let repr = Path.name p in
      if SS.mem repr !wcs
      then fprintf ppf "wildcard()"
      else if SS.mem repr !once_used
      then fprintf ppf "_f()"
      else (
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> fprintf ppf "%a" print_path p
        | s -> fprintf ppf "%s" s)
    (* | Tident p -> fprintf ppf "%a" print_ident @@ Path.name p *)
    (* | Conde xs -> fprintf ppf "@[conde(%a)@]" (pp_comma_list helper) xs *)
    | Conde xs ->
      fprintf ppf "@[<v 6>conde(";
      List.iteri xs ~f:(fun i e ->
        if i <> 0 then fprintf ppf ",@ ";
        nopar
          ppf
          (match e with
          | Pause x -> x
          | _ -> e));
      fprintf ppf ")@]"
    | Conj_multi xs ->
      (* fprintf ppf "@[and(%a)@]" (pp_comma_list helper) xs *)
      fprintf ppf "@[<v 4>and(";
      List.iteri xs ~f:(fun i ->
        if i <> 0 then fprintf ppf ",@ ";
        nopar ppf);
      fprintf ppf ")@]"
    | Infix_conj2 (l, r) -> fprintf ppf "@[and(%a,@, %a)@]" nopar l nopar r
    | T_int n -> fprintf ppf "%d.toLogic()" n
    | T_bool n -> fprintf ppf "%b.toLogicBool()" n
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "nilLogicList()"
    | T_list_cons (h, tl) -> fprintf ppf "@[(%a + %a)@]" default h default tl
    | Tabstr ([ (name, typ) ], rhs) ->
      fprintf ppf "@[{ %s: %a -> %a }@]" name (pp_typ_as_kotlin inh_info) typ nopar rhs
    | Tabstr (names, rhs) ->
      fprintf ppf "@[{ ";
      List.iteri names ~f:(fun i (name, typ) ->
        if i <> 0 then fprintf ppf ", ";
        fprintf ppf "@[%a: %a@]" print_ident name (pp_typ_as_kotlin inh_info) typ);
      fprintf ppf " -> %a }@]" nopar rhs
    | Tunit -> fprintf ppf "" (* fprintf ppf "/* Unit */" *)
    | Other e -> fprintf ppf "@[{| Other %a |}@]" Pprintast.expression (MyUntype.expr e)
  and default ppf = helper ~par:true ppf
  and nopar ppf = helper ~par:false ppf in
  helper ~par:false
;;

let pp_rvb_as_scheme inh_info ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
      (fun ppf (name, typ) ->
        fprintf ppf "@[%a: %a@]" print_ident name (pp_typ_as_kotlin inh_info) typ)
      ppf
  in
  let tvars =
    List.fold_left
      ~f:(fun acc (_, typ) -> S.union acc (collect_type_variables typ))
      ~init:S.empty
      args
  in
  fprintf ppf "@[<v>";
  fprintf ppf "@[context(RelationalContext)@]@ ";
  fprintf
    ppf
    "@[<v 2>@[<hov 6>%sfun %s %a(%a@,@[): Goal =@]@]@ "
    ""
    (if S.is_empty tvars
     then ""
     else (
       let names =
         S.fold
           (fun s acc ->
             let mangled = ocaml_to_kotlin_tvar s in
             sprintf "%s : Term<%s>" mangled mangled :: acc)
           tvars
           []
       in
       "<" ^ String.concat ~sep:", " names ^ ">"))
    print_ident
    name
    pp_args
    args;
  fprintf ppf "%a" (pp_ast_as_kotlin inh_info) body;
  fprintf ppf "@]@ @,@]"
;;

let pp_item ~toplevel:_ info fmt =
  let open Format in
  let printfn ppf = Format.kasprintf (Format.fprintf fmt "%s") ppf in
  function
  | Inh_info.RVB rvb ->
    printfn "; %s %d\n" rvb.name __LINE__;
    pp_rvb_as_scheme info fmt rvb (* printfn "%a" (pp_ast_as_scheme info) body *)
  | Plain_kotlin _ -> printfn "; fuck %d" __LINE__
  | Functor1 { name = _; typ = _; arg_name = _; arg_typ = _; body = _ } ->
    printfn "; fuck %d" __LINE__
  | _ -> printfn "; fuck %d" __LINE__
;;

let pp : Format.formatter -> AST.Inh_info.t -> unit =
 fun ppf info ->
  Format.fprintf ppf "%s\n" (Inh_info.preamble info);
  Format.fprintf ppf ";;; There are %d relations\n" (List.length info.Inh_info.rvbs);
  Inh_info.iter_vbs info ~f:(pp_item ~toplevel:true info ppf)
;;
