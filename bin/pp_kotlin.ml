open Stdppx
open AST

let unparse_arrows typ =
  let rec helper acc te =
    Tast_pattern.(parse (typ_arrow __ __) Location.none)
      ~on_error:(fun _ -> List.rev acc, te)
      te
      (fun h tl -> helper (h :: acc) tl)
  in
  helper [] typ
;;

let ocaml_to_kotlin_tvar s = String.map s ~f:Char.uppercase_ascii

let rec pp_typ_as_kotlin inh_info =
  let to_caml_string typ =
    Format.asprintf "%a" Printtyp.type_expr typ |> Str.global_replace (Str.regexp "\n") ""
  in
  let textual ppf typ ~fk =
    let caml_repr = to_caml_string typ in
    match Inh_info.lookup_typ_exn inh_info caml_repr with
    | s -> Format.fprintf ppf "%s/*%d*/" s __LINE__
    | exception Not_found -> fk ()
  in
  let rec helper ~add ppf (typ : Types.type_expr) =
    (* Format.eprintf "Run helper on %S\n%!" (to_caml_string typ); *)
    let sk =
      let string_of_path p =
        match Path.flatten p with
        | `Ok (id, xs) -> String.concat ~sep:"." (Ident.name id :: xs)
        | `Contains_apply -> assert false
      in
      let open Format in
      fun x () ->
        let pp_args args =
          match args with
          | [] -> ()
          | _ ->
            fprintf
              ppf
              "<%a>"
              (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") helper_no)
              args
        in
        let run x =
          match x with
          | `Unit -> ()
          | `Logic_list arg -> fprintf ppf "LogicList<%a>" helper_no arg
          | `Logic_option arg -> fprintf ppf "LogicOption<%a>" helper_no arg
          | `Ilogic_of_t (path, _)
            when String.equal "Peano.HO.Std.Nat.t" (string_of_path path) ->
            fprintf ppf "PeanoLogicNumber"
          | `Ilogic_of_t (path, [ arg; _ ])
            when String.equal "OCanren.Std.List.t" (string_of_path path) ->
            fprintf ppf "LogicList<%a>" helper_no arg
          | `Logic_nat -> fprintf ppf "PeanoLogicNumber"
          | `Int_ilogic -> fprintf ppf "LogicInt"
          | `Bool_ilogic -> fprintf ppf "LogicBool"
          | `Ilogic_of_poly name -> fprintf ppf "%s" (ocaml_to_kotlin_tvar name)
          | `Ilogic_of_t (path, arg1 :: _)
            when String.equal "Targ.t" (string_of_path path)
                 (* TODO(Kakadu): Elimintate dirty hack! *) ->
            Format.fprintf ppf "Jarg<%a>" (helper ~add:false) arg1
          | `Ilogic_of_t (path, arg1 :: _)
            when String.equal "CC_subst.t" (string_of_path path)
                 (* TODO(Kakadu): Elimintate dirty hack! *) ->
            Format.fprintf ppf "ClosureConversion<%a>" (helper ~add:false) arg1
          | `Ilogic_of_t (path, [ arg1; _; _ ])
            when String.equal "Decl.t" (string_of_path path)
                 (* TODO(Kakadu): Elimintate dirty hack! *) ->
            Format.fprintf ppf "Decl<%a>" (helper ~add:false) arg1
          | `Ilogic_of_t (path, args) ->
            (* Format.eprintf "Ilogic_of_t: Path.name = %S\n%!" (Path.name path); *)
            (* Format.eprintf "Path = %a\n%!" Path.print path; *)
            (* We assume here, that path is in the form PATH.t, so we need to scan arguments,
               and find an argument, with toplevel type PATH.injected
            *)
            let expected_path = String.drop_suffix (Path.name path) 1 ^ "injected" in
            (try
               let arg =
                 List.find args ~f:(fun t ->
                   match Types.get_desc t with
                   | Tconstr (path2, _, _)
                     when String.equal expected_path (Path.name path2) -> true
                   | _ -> false)
               in
               (* TODO(Kakadu): understand why false works and ~add doesn't *)
               helper ~add:false ppf arg
             with
            | Not_found ->
              (match Inh_info.lookup_typ_exn inh_info expected_path with
              | s ->
                Format.fprintf ppf "%s/*%d*/" s __LINE__;
                pp_args args
              | exception Not_found ->
                Format.fprintf ppf "/* Error path = %s */" (Path.name path)))
          | `Goal -> fprintf ppf "Goal"
          | `Constr_with_args (path, args) ->
            (* let __ _ =
               Format.eprintf
               "Constr_with_args (%s, _)\t add=%b\n%!"
               (string_of_path path)
               add
               in *)
            let caml_repr = string_of_path path in
            let () =
              match Inh_info.lookup_typ_exn inh_info caml_repr with
              | s ->
                (* Format.fprintf ppf "%s/*%d (argc=%d)*/" s __LINE__ (List.length args); *)
                Format.fprintf ppf "%s" s
              | exception Not_found ->
                Format.fprintf ppf "/* %a */Error" Printtyp.type_expr typ
            in
            pp_args args
          (* | `Function ([ arg1 ], rez) ->
             fprintf ppf "@[ %a -> %a @]" (helper ~add:true) arg1 (helper ~add:true) rez *)
          | `Function (args, rez) ->
            (* eprintf "rez = @[%a@]\n!" Printtyp.type_expr rez; *)
            (* let argslen = List.length args in *)
            (* eprintf "argslen = %d\n%!" argslen; *)
            (* assert (List.length args = 2 || List.length args = 3); *)
            fprintf ppf "@[@[(";
            List.iteri args ~f:(fun i ->
              if i <> 0 then fprintf ppf ", ";
              helper ~add:true ppf);
            fprintf ppf ")@] -> %a@]" (helper ~add:true) rez
          (* assert false *)
        in
        let need_add_term =
          match x with
          | `Function _ | `Goal | `Unit ->
            (* eprintf "%s %d\n%!" __FILE__ __LINE__; *)
            false
          | `Constr_with_args (path, _)
            when String.equal (string_of_path path) "OCanren!.goal" ->
            (* eprintf "%s %d\n%!" __FILE__ __LINE__; *)
            false
          | _ -> true
        in
        if add && need_add_term then fprintf ppf "Term<%a>" (fun _ -> run) x else run x
    in
    let pilogic () =
      let open Tast_pattern in
      path [ "OCanren"; "ilogic" ]
      ||| path [ "OCanren!"; "ilogic" ]
      ||| path [ "OCanren__"; "Logic"; "ilogic" ]
      ||| path [ "OCanren__!"; "Logic"; "ilogic" ]
    in
    let pinj_list () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "List"; "injected" ]
    in
    let pinj_list_t () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "List"; "t" ] ||| path [ "OCanren!"; "Std"; "List"; "t" ]
    in
    let pinj_nat () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Nat"; "injected" ]
      ||| path [ "OCanren"; "Std"; "Nat"; "groundi" ]
    in
    let pinj_nat_t () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Nat"; "t" ]
    in
    let _pinj_option () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Option"; "injected" ]
      ||| path [ "OCanren"; "Std"; "Option"; "groundi" ]
    in
    let pinj_option_t () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Option"; "ground" ]
      ||| path [ "OCanren"; "Std"; "Option"; "t" ]
    in
    Tast_pattern.(
      parse_conde
        [ typ_constr (path [ "unit" ]) nil |> map0 ~f:`Unit
        ; choice
            [ typ_constr
                (pilogic ())
                (typ_constr
                   (pinj_list_t ())
                   (__ ^:: typ_constr (pinj_list ()) (drop ^:: nil) ^:: nil)
                ^:: nil)
            ; typ_constr (pinj_list ()) (__ ^:: nil)
            ]
          |> map1 ~f:(fun x -> `Logic_list x)
        ; typ_arrows __ __ |> map2 ~f:(fun args rez -> `Function (args, rez))
        ; typ_constr (path [ "OCanren"; "goal" ]) nil |> map0 ~f:`Goal
        ; typ_constr
            (pilogic ())
            (typ_constr (pinj_nat_t ()) (typ_constr (pinj_nat ()) nil ^:: nil) ^:: nil)
          |> map0 ~f:`Logic_nat
        ; typ_constr (pilogic ()) (typ_constr (pinj_option_t ()) (__ ^:: nil) ^:: nil)
          |> map1 ~f:(fun x -> `Logic_option x)
        ; typ_constr (pilogic ()) (typ_constr (path [ "int" ]) nil ^:: nil)
          |> map0 ~f:`Int_ilogic
        ; typ_constr (pilogic ()) (typ_constr (path [ "bool" ]) nil ^:: nil)
          |> map0 ~f:`Bool_ilogic
        ; typ_constr (pilogic ()) (typ_var __ ^:: nil)
          |> map1 ~f:(fun name -> `Ilogic_of_poly name)
        ; typ_var __ |> map1 ~f:(fun name -> `Ilogic_of_poly name)
        ; typ_constr (pilogic ()) (typ_constr __ (as__ drop) ^:: nil)
          |> map2 ~f:(fun path args ->
            if String.ends_with ~suffix:".t" (Path.name path)
            then `Ilogic_of_t (path, args)
            else fail Location.none "Fallthough in `Ilogic_of_t")
        ; typ_constr __ __ |> map2 ~f:(fun cpath args -> `Constr_with_args (cpath, args))
        ])
      Location.none
      typ
      ~on_error:(fun _err () ->
        (* Format.eprintf "Error happend on %S: %s\n%!" (to_caml_string typ) err; *)
        textual ppf typ ~fk:(fun () ->
          match unparse_arrows typ with
          | [], rest ->
            textual ppf rest ~fk:(fun () ->
              Format.fprintf ppf " /*%s 111 */" (to_caml_string rest))
          | args, rest ->
            Format.fprintf ppf "(";
            List.iteri args ~f:(fun i typ ->
              if i <> 0 then Format.fprintf ppf ", ";
              pp_typ_as_kotlin inh_info ppf typ);
            Format.fprintf ppf ") -> %a" (pp_typ_as_kotlin inh_info) rest))
      sk
      ()
  and helper_no eta = helper ~add:false eta in
  helper ~add:true
;;

(*
   module Fold_syntax_macro = struct
  type 'a t =
    | Conde of 'a t list
    | Conj2 of 'a t * 'a t
    | Conj_multi of 'a t list
    | Bind2 of 'a * 'a
    | New_scope of 'a
    | Fresh of (string * Types.type_expr) list * 'a
    | Bind_star of 'a list
    | Mplus_star of 'a list
    | Mplus of 'a * 'a
    | Abstr of 'a
    | App of 'a
    | Delay of 'a
    | Call of Path.t * ('t term as 't) list
    | U of ('t term as 't) * ('t term as 't)
  (* [@@deriving map] *)

  let map f = function
    | Conde xs -> Conde (List.map ~f xs)
    | Bind_star xs -> Bind_star (List.map ~f xs)
    | Mplus_star xs -> Mplus_star (List.map ~f xs)
    | Bind2 (l, r) -> Bind2 (f l, f r)
    | Conj2 (l, r) -> Conj2 (f l, f r)
    | Conj_multi xs -> Conj_multi (List.map ~f xs)
    | Mplus (l, r) -> Mplus (f l, f r)
    | New_scope a -> New_scope (f a)
    | Fresh (v, a) -> Fresh (v, f a)
    | Abstr a -> Abstr (f a)
    | App a -> App (f a)
    | Delay a -> Delay (f a)
    | (Call _ | U _) as x -> x
  ;;

  let transform : ('a ast as 'a) -> ('b t as 'b) =
    let rec helper = function
      | Unify (a, b) -> U (a, b)
      | Bind (a, b) -> Bind2 (helper a, helper b)
      | Other _ -> failwith "Bad argument of transform"
      | Call_rel (f, args) -> Call (f, args)
      | St_abstr a -> Abstr (helper a)
      | St_app a -> App (helper a)
      | Pause a -> Delay (helper a)
      | Conde xs -> Conde (List.map ~f:helper xs)
      | Conj_multi xs -> Conj_multi (List.map ~f:helper xs)
      | Infix_conj2 (l, r) -> Conj2 (helper l, helper r)
      | Mplus (a, b) -> Mplus (helper a, helper b)
      | New_scope a -> New_scope (helper a)
      | Fresh (args, e) -> Fresh (args, helper e)
    in
    helper
  ;;

  let pp inh_info : _ -> ('a t as 'a) -> unit =
    let open Format in
    let rec helper ppf = function
      | U (l, r) ->
        (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
        fprintf ppf "@[(%a `===` %a)@]" pp_term_as_kotlin l pp_term_as_kotlin r
      | Conde xs -> fprintf ppf "@[<v 2>@[conde (@]%a@[)@]@]" (pp_comma_list helper) xs
      | Conj_multi xs -> fprintf ppf "@[<v 2>@[and (@]%a@[)@]@]" (pp_comma_list helper) xs
      | Call (f, args) ->
        fprintf ppf "@[%a(%a)@]" Printtyp.path f (pp_comma_list pp_term_as_kotlin) args
      | New_scope a -> fprintf ppf "/* ERROR */ %a" helper a
      | Mplus (a, b) -> fprintf ppf "/* ERROR */ Mplus (%a, %a)" helper a helper b
      | Mplus_star xs -> fprintf ppf "/* ERROR */ conde( %a ) ]" (pp_comma_list helper) xs
      | Bind_star xs -> fprintf ppf "@[<v 4>@[and(@]%a@[)@]@]" (pp_comma_list helper) xs
      | Abstr a -> fprintf ppf "/* ERROR */ { st -> %a }" helper a
      | App a -> fprintf ppf "/* ERROR */ %a(st)" helper a
      | Bind2 (l, r) -> fprintf ppf "/* ERROR? */  (%a and %a)" helper l helper r
      | Conj2 (l, r) -> fprintf ppf "(%a and %a)" helper l helper r
      | Fresh (xs, Delay e) ->
        fprintf ppf "@[<hov>@[freshTypedVars {";
        pp_comma_list
          (fun ppf (name, typ) ->
            fprintf ppf "@[ %s : %a@]" name (pp_typ_as_kotlin inh_info) typ)
          ppf
          xs;
        fprintf ppf " ->@]@ %a@ @[}@]@]" helper e
      | Fresh (xs, e) ->
        fprintf ppf "/* NOTE: fresh without delay */@ ";
        fprintf ppf "@[<hov>@[freshTypedVars {";
        pp_comma_list
          (fun ppf (name, typ) ->
            fprintf ppf "@[ %s : %a@]" name (pp_typ_as_kotlin inh_info) typ)
          ppf
          xs;
        fprintf ppf " ->@]@ %a@ @[}@]@]" helper e
      | Delay e -> fprintf ppf "delay { %a }" helper e
    in
    helper
  ;;

  let upper ?(verbose = false) : ('a t as 'a) -> ('b t as 'b) =
    let is_bind_star_app_head = function
      | Bind_star (App _ :: _) | App _ -> true
      | _ -> false
    in
    let rec helper e =
      let e = map helper e in
      if verbose
      then Format.printf "@[transformed: @[%a@]@]\n\n%!" (pp (Inh_info.create ())) e;
      match e with
      | Bind_star (Bind_star xs :: ys) -> helper (Bind_star (xs @ ys))
      | Bind2 (Bind2 (a, b), c) -> helper (Bind_star [ helper a; helper b; helper c ])
      | Bind2 (a, b) -> helper (Bind_star [ helper a; helper b ])
      | Mplus (a, Mplus_star xs) -> Mplus_star (a :: xs)
      | Mplus (a, Delay b) -> Mplus_star [ a; b ]
      | Abstr (Delay (Fresh (name, Bind_star [ App h ])))
      | Abstr (Delay (Fresh (name, App h))) -> helper @@ Fresh (name, h)
      | Abstr (Delay (Fresh (name, Bind_star (App h :: tl)))) ->
        helper @@ Fresh (name, Bind_star (h :: tl))
      | Abstr (Delay (New_scope (Mplus_star ds)))
        when List.for_all ds ~f:is_bind_star_app_head ->
        Conde
          (List.map
             ~f:(function
               | Bind_star (App h :: tl) -> Bind_star (h :: tl)
               | App h -> h
               | x -> x)
             ds)
      | x -> x
    in
    helper
  ;;
end

let%expect_test _ =
  let open Fold_syntax_macro in
  Format.printf
    "%a\n"
    (pp (Inh_info.create ()))
    (upper
     @@ Abstr
          (Delay
             (Fresh
                ( [ "a", Types.newty2 ~level:0 (Types.Tvar None) ]
                , App (U (T_list_nil, T_list_nil)) ))));
  [%expect
    {|
    /* NOTE: fresh without delay */
    freshTypedVars { a : 'a -> (nilLogicList() `===` nilLogicList()) } |}]
;; *)

(* let pp_term_as_kotlin =
  let open Format in
  let rec helper ppf = function

    (* | Tident p -> fprintf ppf "%a" Printtyp.path p *)
    (* TODO: Printtyp.path sometimes fives /n in the end. *)


    | Tother e ->
      fprintf ppf "/* ERROR ? */{|  %a |}" Pprintast.expression (MyUntype.expr e)
  in
  helper
;; *)

type char_representation =
  | Common of char
  | Special of string

let print_ident ppf s =
  let mangle_ident_char = function
    | '%' -> Special "percent"
    | '<' -> Special "less"
    | '#' -> Special "number"
    | '!' -> Special "exclamation"
    | '?' -> Special "question"
    | '~' -> Special "tilde"
    | ':' -> Special "colon"
    | '.' -> Special "dot"
    | '$' -> Special "dollar"
    | '&' -> Special "and"
    | '*' -> Special "asterisk"
    | '+' -> Special "plus"
    | '-' -> Special "minus"
    | '/' -> Special "slash"
    | '=' -> Special "equal"
    | '>' -> Special "greater"
    | '@' -> Special "at"
    | '^' -> Special "hat"
    | '|' -> Special "pipe"
    | '\'' -> Special "prime"
    | c -> Common c
  in
  let rec concat_chars ppf =
    let open Format in
    function
    | [ Special s ] -> fprintf ppf "%s" s
    | [ Common c ] -> fprintf ppf "%c" c
    | x1 :: (x2 :: _ as xs) ->
      (match x1, x2 with
      | Common c, Common _ -> fprintf ppf "%c%a" c concat_chars xs
      | Common c, Special _ -> fprintf ppf "%c_%a" c concat_chars xs
      | Special s, _ -> fprintf ppf "%s_%a" s concat_chars xs)
    | [] -> eprintf "Empty identifier %s %d" __FILE__ __LINE__
  in
  concat_chars ppf @@ List.map ~f:mangle_ident_char @@ List.of_seq @@ String.to_seq s
;;

let rec print_path ppf =
  let open Format in
  function
  | Path.Pident i -> fprintf ppf "%a" print_ident @@ Ident.name i
  | Pdot (p, s) -> fprintf ppf "%a.%a" print_path p print_ident s
  | Papply (p1, p2) -> fprintf ppf "%a(%a)" print_path p1 print_path p2
;;

module Uses_count = struct
  type t =
    | Unused
    | Once
    | Many
end

let check_uses ident ast =
  let exception Manyuses in
  let incr_acc = function
    | Uses_count.Unused -> Uses_count.Once
    | _ -> raise Manyuses
  in
  let acc = ref Uses_count.Unused in
  let rec helper = function
    | Tident p when String.equal (Path.name p) ident -> acc := incr_acc !acc
    | otherwise -> ignore (map_ast helper otherwise)
  in
  match helper ast with
  | _ -> !acc
  | exception Manyuses -> Uses_count.Many
;;

let pp_list ppf =
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") ppf
;;

let pp_ast_as_kotlin inh_info =
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
      pp_list
        (fun ppf (name, typ) ->
          fprintf ppf "@[%s: %a@]" name (pp_typ_as_kotlin inh_info) typ)
        ppf
        xs;
      fprintf ppf " ->@]@ %a@ @[}@]@]" default e
    | Fresh (xs, e) ->
      (* fprintf ppf "/* NOTE: fresh without delay */@ "; *)
      fprintf ppf "@[<hov>@[freshTypedVars {";
      pp_list
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
      fprintf ppf "@[%s(%a)@]" kotlin_func (pp_list default) args
    | Tapp (Tident path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Tapp (f, args) ->
      Format.printf "Application %d\n%!" __LINE__;
      (*  *)
      fprintf ppf "@[%a(%a)@]" default f (pp_list default) args
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
    | T_string _ -> fprintf ppf "/* not implemented */"
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

let%expect_test " " =
  let open Format in
  printf "@[<v 6>@[conde(@]";
  for i = 1 to 10 do
    ignore i;
    printf "@[%s@]@," (String.make 10 (Char.chr (Char.code 'a' + i)))
  done;
  printf ")@]";
  [%expect
    {|
    conde(bbbbbbbbbb
          cccccccccc
          dddddddddd
          eeeeeeeeee
          ffffffffff
          gggggggggg
          hhhhhhhhhh
          iiiiiiiiii
          jjjjjjjjjj
          kkkkkkkkkk
          ) |}]
;;

module S = Set.Make (String)

let collect_type_variables : _ =
  let rec helper acc desc =
    (* Format.printf "%s: %a\n%!" __FUNCTION__ Printtyp.type_expr desc; *)
    Tast_pattern.(
      parse
      @@ choice
           [ typ_var __ |> map1 ~f:(fun x -> S.add x acc)
           ; __ @-> __ |> map2 ~f:(fun l r -> helper (helper acc l) r)
           ; typ_constr drop __ |> map1 ~f:(List.fold_left ~f:helper ~init:acc)
           ])
      Location.none
      desc
      ~on_error:(fun _ ->
        let __ () =
          match Types.get_desc desc with
          | Types.Tvar None -> Printf.eprintf "%d\n" __LINE__
          | _ -> Printf.eprintf "end\n"
        in
        Format.eprintf "Unsupported case: '%a'\n%!" Printtyp.type_expr desc;
        assert false)
      (fun acc -> acc)
  in
  fun texpr -> helper S.empty texpr
;;

let pp_rvb_as_kotlin ?(override = true) inh_info ppf { Rvb.name; args; body } =
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
    (if override then "override " else "")
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

let has_attr = Tast_folder.has_attr

let lookup_doc_attr =
  List.find_map ~f:(function
    | { Parsetree.attr_name = { txt = "ocaml.doc" }; attr_payload = PStr stru; attr_loc }
      ->
      Ppxlib.Ast_pattern.(
        parse (pstr_eval (pexp_constant (pconst_string __ drop drop)) drop ^:: nil))
        attr_loc
        stru
        ~on_error:(fun _ -> None)
        (fun s -> Some s)
    | _ -> None)
;;

let pp_modtype_as_kotlin info name ppf sign =
  let open Format in
  let printfn fmt = Format.kfprintf (fun fmt -> fprintf fmt "@,") ppf fmt in
  let gensym =
    let c = ref 0 in
    fun () ->
      incr c;
      Printf.sprintf "v%d" !c
  in
  fprintf ppf "// %s \n%!" name;
  printfn "@[@[<v 2>@[interface %s {@]" name;
  List.iter sign.Typedtree.sig_items ~f:(fun sitem ->
    printfn "@[@]";
    match sitem.sig_desc with
    | Tsig_value
        { val_name = { txt = name; _ }; val_val = { val_type; _ }; val_attributes }
      when has_attr "klogic_val" val_attributes ->
      printfn "@[val %s : %a@]" name (pp_typ_as_kotlin info) val_type
    | Tsig_value
        { val_name = { txt = name; _ }; val_val = { val_type; _ }; val_attributes; _ } ->
      let args, ret = unparse_arrows val_type in
      let args =
        match args with
        | [ t ] when String.equal (Format.asprintf "%a" Printtyp.type_expr t) "unit" -> []
        | _ -> args
      in
      let tvars =
        (* TODO: Maybe generate varnames? *)
        List.fold_left
          ~f:(fun acc typ -> S.union acc (collect_type_variables typ))
          ~init:S.empty
          args
      in
      let () =
        match lookup_doc_attr val_attributes with
        | None -> ()
        | Some str ->
          String.split_on_char ~sep:'\n' str |> List.iter ~f:(printfn "@[// %s@]")
      in
      printfn "context(RelationalContext)";
      printfn
        "@[fun%s %a("
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
        name;
      List.iteri args ~f:(fun i t ->
        if i <> 0 then fprintf ppf ",@ ";
        fprintf ppf "@[%s: %a@]" (gensym ()) (pp_typ_as_kotlin info) t);
      fprintf ppf "@ ): %a" (pp_typ_as_kotlin info) ret;
      printfn "@]"
    | Tsig_module { md_id = Some id; md_type = { mty_desc = Tmty_ident (path, _) } } ->
      printfn "@[val %s : %a@]" (Ident.name id) Printtyp.path path
    | _ -> printfn "@[//@]");
  printfn "@]@,}@]\n"
;;

let rec pp_functor_as_kotlin ~name ~typ ~arg_name ~arg_typ info ppf body =
  let open Format in
  fprintf ppf "// functor\n%!";
  fprintf ppf "@[val %s : (%s) -> %s = { %s: %s ->@]@ " name arg_typ typ arg_name arg_typ;
  fprintf ppf "@[<v 2>@[object: %s {@]@," typ;
  pp_print_list (pp_item ~toplevel:false info) ppf body;
  fprintf ppf "@]}}\n"

and pp_item ~toplevel info ppf = function
  | Inh_info.RVB rvb -> pp_rvb_as_kotlin ~override:(not toplevel) info ppf rvb
  | Plain_kotlin s -> Format.fprintf ppf "%s" s
  | MT_as_interface (name, sign) -> pp_modtype_as_kotlin info name ppf sign
  | Functor1 { name; typ; arg_name; arg_typ; body } ->
    pp_functor_as_kotlin ~name ~typ ~arg_name ~arg_typ info ppf body
;;
