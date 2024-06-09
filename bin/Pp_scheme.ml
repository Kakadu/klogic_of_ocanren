open Stdppx
open AST
open Trans_config

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
  let rec term_helper ?(q = false) ppf = function
    | Tident p ->
      let repr = Path.name p in
      (* if SS.mem repr !wcs
      then fprintf ppf "wildcard()"
      else if SS.mem repr !once_used
      then fprintf ppf "_f()"
      else  *)
      (match Inh_info.lookup_expr_exn inh_info repr with
      | exception Not_found ->
        fprintf ppf "%s%a" (if q then "," else "") Pp_kotlin.print_path p
      | s -> fprintf ppf "%s" s)
    | T_int n -> fprintf ppf "%d" n
    | T_bool n -> fprintf ppf "%b" n
    | T_string s -> fprintf ppf "'%s" s
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space (term_helper ~q)) ls
    | T_list_nil -> fprintf ppf "'()"
    | T_list_cons (_, _) as lst ->
      let rec classify acc = function
        | T_list_nil -> `Finite (List.rev acc)
        | T_list_cons (x, xs) -> classify (x :: acc) xs
        | tl -> `Arbitrary (List.rev acc, tl)
      in
      (match classify [] lst with
      | `Finite ts ->
        fprintf ppf "@[(";
        pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " ") (term_helper ~q) ppf ts;
        fprintf ppf ")@]"
      | `Arbitrary (args, tl) ->
        fprintf ppf "@[(";
        pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt " ") (term_helper ~q) ppf args;
        fprintf ppf " . %a)@]" (term_helper ~q) tl)
    | Call_rel (path, [ l ])
      when match Format.asprintf "%a" Path.print path with
           | "Scheme_ast!.Gterm.symb" -> true
           | _ -> false ->
      fprintf ppf "@[(%ssymb %a)@]" (if q then "" else "'") (term_helper ~q) l
    | Call_rel (path, [ l; r ])
      when match Format.asprintf "%a" Path.print path with
           | "OCanren!.Std.pair" | "OCanren!.Std.Pair.pair" -> true
           | _ -> false -> fprintf ppf "@[(%a %a)@]" (term_helper ~q) l (term_helper ~q) r
    | Call_rel (path, [ l ])
      when match Format.asprintf "%a" Path.print path with
           | "Scheme_ast!.Gterm.seq" -> true
           | _ -> false ->
      fprintf ppf "@[(%sseq %a)@]" (if q then "" else "'") (term_helper ~q) l
    | Call_rel (path, [ l ])
      when match Format.asprintf "%a" Path.print path with
           | "Scheme_ast.Gresult.val_" | "Scheme_ast!.Gresult.val_" -> true
           | _ -> false ->
      fprintf ppf "@[(%sval %a)@]" (if q then "" else "'") (term_helper ~q) l
    | Call_rel (path, [ a; b; c ])
      when match Format.asprintf "%a" Path.print path with
           | "Scheme_ast.Gresult.closure" | "Scheme_ast!.Gresult.closure" -> true
           | _ -> false ->
      fprintf
        ppf
        "@[(%sclosure (%a %a %a))@]"
        (if q then "" else "'")
        (term_helper ~q)
        a
        (term_helper ~q)
        b
        (term_helper ~q)
        c
    | Tapp (_, _) | Tunit -> assert false
    | ( Pause _ | St_abstr _ | St_app _
      | Mplus (_, _)
      | Conde _ | Conj_multi _
      | Infix_conj2 (_, _)
      | New_scope _
      | Bind (_, _)
      | Fresh (_, _)
      | Wildcard (_, _, _)
      | Unify (_, _)
      | Diseq (_, _)
      | Call_rel (_, _)
      | Tabstr _ | Other _ ) as other ->
      Format.eprintf "@[%a@]\n%!" AST.pp other;
      fprintf ppf "#| %a |#" AST.pp other
  and quoted_term eta = term_helper ~q:true eta
  and non_quoted eta = term_helper ~q:false eta in
  let on_term ppf = function
    | Tident p ->
      let repr = Path.name p in
      if SS.mem repr !wcs
      then fprintf ppf "wildcard()"
      else if SS.mem repr !once_used
      then fprintf ppf "_f()"
      else (
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> fprintf ppf "%a" Pp_kotlin.print_path p
        | s -> fprintf ppf "%s" s)
    | t ->
      if AST.has_vars_inside t
      then fprintf ppf "`%a" quoted_term t
      else fprintf ppf "%a" non_quoted t
  in
  let rec helper ppf = function
    | Pause e -> fprintf ppf "@[(inc %a)@]" default e
    | St_abstr l -> fprintf ppf "@[<v 2>@[{ st: State ->@ %a@ }@]" default l
    | St_app l -> fprintf ppf "%a(st)" default l
    | New_scope x -> helper ppf x
    | Mplus (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[mplus@]@,@,@[(%a)@])@]" default l default r
    | Bind (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[bind@]@,@[(%a)@])@]" default l default r
    | Fresh ([ (v1, _vtyp) ], rhs)
      when match rhs with
           | Pause _ -> false
           | _ -> true ->
      (match Pp_kotlin.check_uses v1 rhs with
      | Pp_kotlin.Uses_count.Once -> with_once_used v1 (fun () -> default ppf rhs)
      | _ -> fprintf ppf "@[(fresh (%s) %a)]" v1 default rhs)
    | Fresh (args, Pause (Conj_multi xs)) | Fresh (args, Conj_multi xs) ->
      fprintf ppf "@[<v 2>@[(fresh (";
      pp_list (fun ppf (name, _) -> fprintf ppf "%s" name) ppf args;
      fprintf ppf ")@]@ ";
      List.iter ~f:(fprintf ppf "%a@ " default) xs;
      fprintf ppf ")@]"
    | Fresh (xs, Pause e) ->
      fprintf ppf "@[@[<hov 2>(fresh (";
      pp_list (fun ppf (name, _) -> fprintf ppf "%s " name) ppf xs;
      fprintf ppf ")@]@ %a@ )@]" default e
    | Fresh (xs, e) ->
      (* fprintf ppf "/* NOTE: fresh without delay */@ "; *)
      fprintf ppf "@[<hov>@[(fresh (";
      pp_list (fun ppf (name, _) -> fprintf ppf " %s " name) ppf xs;
      fprintf ppf ")@]@ %a@ )@]" default e
    | Wildcard (v, _t, e) -> with_wc v (fun () -> default ppf e)
    | Unify (l, r) ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "(== %a %a)" on_term l on_term r
    | Diseq (l, r) -> fprintf ppf "(=/= %a %a)" on_term l on_term r
    | Call_rel (path, [ Tunit ]) when path_is_none path ->
      failwith "not implemented" (* fprintf ppf "None()" *)
    | Call_rel (p, args) ->
      let kotlin_func =
        let repr = Path.name p in
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> Format.asprintf "%a" Pp_kotlin.print_path p
        | s -> s
      in
      fprintf ppf "@[(%s %a)@]" kotlin_func (pp_list on_term) args
    | Tapp (Tident path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Tapp (f, args) ->
      Format.printf "Application %d\n%!" __LINE__;
      (*  *)
      fprintf ppf "@[%a(%a)@]" default f (pp_list default) args
    | Conde xs ->
      fprintf ppf "@[<v 6>(conde ";
      List.iter xs ~f:(fun e ->
        (* TODO: eliminate pauses? *)
        match e with
        | Pause (Conj_multi xs) | Conj_multi xs ->
          fprintf
            ppf
            "(@[<hov>%a@])@ "
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@ ") default)
            xs
        | Infix_conj2 (l, r) -> fprintf ppf "(%a@ %a)@ " default l default r
        | (Unify _ | Call_rel _ | Fresh _) as e -> fprintf ppf "(%a)@ " default e
        | x ->
          Format.eprintf
            "@[%s@]\n%!"
            (AST.show_ast (fun ppf _ -> Format.fprintf ppf "?") x);
          assert false);
      fprintf ppf ")@]@, "
    | Conj_multi xs ->
      fprintf ppf "@[<v 4>and(";
      List.iter xs ~f:(default ppf);
      fprintf ppf ")@]"
    | Infix_conj2 (l, r) -> fprintf ppf "@[and(%a,@, %a)@]" default l default r
    | ( T_int _
      | T_bool _
      | Tident _
      | T_list_init _
      | T_list_nil
      | T_list_cons _
      | T_string _ ) as term -> on_term ppf term
    (* | Tident p ->
      let repr = Path.name p in
      if SS.mem repr !wcs
      then fprintf ppf "wildcard()"
      else if SS.mem repr !once_used
      then fprintf ppf "_f()"
      else (
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> fprintf ppf "%a" print_path p
        | s -> fprintf ppf "%s" s)
    | T_int n -> fprintf ppf "%d" n
    | T_bool n -> fprintf ppf "%b" n *)
    (* | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "'()"
    | T_list_cons (h, tl) -> fprintf ppf "@[(%a + %a)@]" default h default tl *)
    | Tabstr ([ (name, _) ], rhs) -> fprintf ppf "@[{ %s  -> %a }@]" name default rhs
    | Tabstr (names, rhs) ->
      fprintf ppf "@[{ ";
      List.iteri names ~f:(fun i (name, _) ->
        if i <> 0 then fprintf ppf ", ";
        fprintf ppf "@[%a @]" Pp_kotlin.print_ident name);
      fprintf ppf " -> %a }@]" default rhs
    | Tunit -> fprintf ppf "" (* fprintf ppf "/* Unit */" *)
    | Other e -> fprintf ppf "@[{| Other %a |}@]" Pprintast.expression (MyUntype.expr e)
  and default ppf = helper ppf in
  helper
;;

let pp_rvb_as_scheme inh_info ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf " ")
      (fun ppf (name, _) -> fprintf ppf "%a" Pp_kotlin.print_ident name)
      ppf
  in
  let body = AST.simplify_ast body in
  (* fprintf ppf "#|\n%a\n|#\n%!" AST.pp body; *)
  fprintf ppf "@[<v 2>";
  fprintf
    ppf
    "@[<v 2>@[(define %a@]@ @[(lambda (%a)@]@]@ "
    Pp_kotlin.print_ident
    name
    pp_args
    args;
  fprintf ppf "@[%a@]" (pp_ast_as_scheme inh_info) body;
  fprintf ppf "))@]@,";
  ()
;;

let pp_item ~toplevel:_ info fmt =
  let printfn ppf = Format.kasprintf (Format.fprintf fmt "%s") ppf in
  function
  | Inh_info.RVB rvb ->
    printfn "; %s %d\n" rvb.name __LINE__;
    pp_rvb_as_scheme info fmt rvb (* printfn "%a" (pp_ast_as_scheme info) body *)
  | Plain_kotlin s -> Format.fprintf fmt "%s" s
  | Functor1 _ -> printfn "; Functors are not supported"
  | MT_as_interface _ -> printfn "; Interfaces are not supported"
;;

let pp : Format.formatter -> AST.Inh_info.t -> unit =
 fun ppf info ->
  Format.fprintf ppf "%s\n" (List.assoc Scheme (Inh_info.preamble info));
  Format.fprintf ppf ";;; There are %d relations\n" (List.length info.Inh_info.rvbs);
  Inh_info.iter_vbs info ~f:(pp_item ~toplevel:true info ppf);
  Format.fprintf ppf "%s\n" (Inh_info.get_epilogue Trans_config.Scheme info)
;;
