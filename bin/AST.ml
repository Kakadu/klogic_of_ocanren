open Stdppx
(*
type 'a term =

  | Tother of Typedtree.expression *)

type 'a ast =
  | Pause of 'a
  | St_abstr of 'a
  | St_app of 'a
  | Mplus of 'a * 'a
  | Conde of 'a list
  | Conj_multi of 'a list
  | Infix_conj2 of 'a * 'a
  | New_scope of 'a
  | Bind of 'a * 'a
  | Fresh of (string * Types.type_expr) list * 'a
  | Unify of 'a * 'a
  | Call_rel of Path.t * 'a list
  | Tapp of 'a * 'a list (** Application of terms. Is similar to Call_rel *)
  | T_int of int
  | T_list_init of 'a list
  | T_list_nil
  | T_list_cons of 'a * 'a
  | Tabstr of ((string * Types.type_expr) list * 'a) (** TODO: Types? *)
  | Tident of Path.t (** TODO: Do we need this? *)
  | Tunit
  | Other of Typedtree.expression

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
  Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ") ppf
;;

let map_ast f = function
  | Pause x -> Pause (f x)
  | St_abstr e -> St_abstr (f e)
  | St_app e -> St_app (f e)
  | Fresh (xs, e) -> Fresh (xs, f e)
  | New_scope x -> New_scope (f x)
  | Conde xs -> Conde (List.map ~f xs)
  | Conj_multi xs -> Conj_multi (List.map ~f xs)
  | Infix_conj2 (l, r) -> Infix_conj2 (f l, f r)
  | Mplus (a, b) -> Mplus (f a, f b)
  | Bind (a, b) -> Bind (f a, f b)
  | Tapp (func, args) -> Tapp (f func, List.map ~f args)
  | Call_rel (path, args) -> Call_rel (path, List.map ~f args)
  | T_list_cons (h, tl) -> T_list_cons (f h, f tl)
  | Tabstr (args, body) -> Tabstr (args, f body)
  | T_list_init xs -> T_list_init (List.map ~f xs)
  | (Tunit | Tident _ | Other _ | T_list_nil | T_int _) as rez -> rez
  | Unify (a, b) -> Unify (f a, f b)
;;

let simplify_ast =
  let rec helper = function
    | Infix_conj2 (Infix_conj2 (a, b), Infix_conj2 (c, d)) ->
      helper @@ Conj_multi [ a; b; c; d ]
    | Infix_conj2 (Infix_conj2 (a, b), c) -> helper @@ Conj_multi [ a; b; c ]
    | Infix_conj2 (Conj_multi xs, r) -> helper @@ Conj_multi (xs @ [ r ])
    | Conj_multi xs ->
      Conj_multi
        (List.concat_map xs ~f:(function
          | Conj_multi xs -> xs
          | Infix_conj2 (a, b) -> [ a; b ]
          | x -> [ x ]))
    | other -> map_ast helper other
  in
  helper
;;

module Inh_info = struct
  type item =
    | RVB of Rvb.t
    | Plain_kotlin of string
    | MT_as_interface of string * Typedtree.signature
    | Functor1 of
        { name : string
        ; typ : string
        ; arg_name : string
        ; arg_typ : string
        ; body : item list
        }

  type t =
    { type_mangle_hints : (string, string) Hashtbl.t
    ; expr_mangle_hints : (string, string) Hashtbl.t
    ; mutable rvbs : item list
    ; mutable preamble : string
    ; mutable epilogue : string
    }

  let create () =
    { type_mangle_hints = Hashtbl.create 13
    ; expr_mangle_hints = Hashtbl.create 13
    ; rvbs = []
    ; preamble = ""
    ; epilogue = ""
    }
  ;;

  let extend t item = t.rvbs <- item :: t.rvbs
  let add_rvb t rvb = extend t (RVB rvb)
  let add_modtype t ident types = t.rvbs <- MT_as_interface (ident, types) :: t.rvbs

  let add_functor t other_info ~name ~typ ~arg_name ~arg_typ =
    extend t (Functor1 { name; typ; arg_name; arg_typ; body = other_info.rvbs })
  ;;

  let lookup_typ_exn t typ = Hashtbl.find t.type_mangle_hints typ
  let lookup_expr_exn t typ = Hashtbl.find t.expr_mangle_hints typ

  let add_hints info hints =
    (* log "add %d hints" (List.length hints); *)
    List.iter hints ~f:(fun (key, data) ->
      (* log "adding a type hint %s -> %s%!" key data; *)
      Hashtbl.add_exn info.type_mangle_hints ~key ~data)
  ;;

  let add_expr_hints info hints =
    List.iter hints ~f:(fun (key, data) ->
      Hashtbl.add_exn info.expr_mangle_hints ~key ~data)
  ;;

  let iter_vbs { rvbs; _ } ~f = List.iter (List.rev rvbs) ~f
  let add_preamble t s = t.preamble <- t.preamble ^ s
  let add_epilogue t s = t.epilogue <- t.epilogue ^ s
  let preamble { preamble; _ } = preamble
  let epilogue { epilogue; _ } = epilogue
end

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
    | s -> Format.fprintf ppf "%s" s
    | exception Not_found -> fk ()
  in
  let rec helper ~add ppf (typ : Types.type_expr) =
    (* Format.eprintf "Run helper on %S\n%!" (to_caml_string typ); *)
    (* Format.eprintf "%a\n" Printtyp.raw_type_expr typ; *)
    let sk =
      let string_of_path p =
        match Path.flatten p with
        | `Ok (id, xs) -> String.concat ~sep:"." (Ident.name id :: xs)
        | `Contains_apply -> assert false
      in
      let open Format in
      fun x () ->
        let run x =
          match x with
          | `Logic_list arg -> fprintf ppf "LogicList<%a>" helper_no arg
          | `Logic_option arg -> fprintf ppf "LogicOption<%a>" helper_no arg
          | `Logic_nat -> fprintf ppf "PeanoLogic"
          | `Int_ilogic -> fprintf ppf " LogicInt "
          | `Ilogic_of_poly name -> fprintf ppf "%s" (ocaml_to_kotlin_tvar name)
          | `Ilogic_of_t (path, args) ->
            (* Format.eprintf "Path.name = %S\n%!" (Path.name path); *)
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
                | s -> Format.fprintf ppf "%s" s
                | exception Not_found -> Format.fprintf ppf "/* Error */"))
          | `Constr_with_args (path, args) ->
            let caml_repr = string_of_path path in
            let () =
              match Inh_info.lookup_typ_exn inh_info caml_repr with
              | s -> Format.fprintf ppf "%s" s
              | exception Not_found ->
                Format.fprintf ppf "/* %a */Error" Printtyp.type_expr typ
            in
            (match args with
             | [] -> ()
             | _ ->
               fprintf
                 ppf
                 "<%a>"
                 (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") helper_no)
                 args)
        in
        if add then fprintf ppf "Term<%a>" (fun _ -> run) x else run x
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
    let pinj_option () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Option"; "injected" ]
      ||| path [ "OCanren"; "Std"; "Nat"; "groundi" ]
    in
    let pinj_option_t () =
      let open Tast_pattern in
      path [ "OCanren"; "Std"; "Option"; "ground" ]
      ||| path [ "OCanren"; "Std"; "Option"; "t" ]
    in
    Tast_pattern.(
      parse_conde
        [ choice
            [ typ_constr
                (pilogic ())
                (typ_constr
                   (pinj_list_t ())
                   (__ ^:: typ_constr (pinj_list ()) (drop ^:: nil) ^:: nil)
                 ^:: nil)
            ; typ_constr (pinj_list ()) (__ ^:: nil)
            ]
          |> map1 ~f:(fun x -> `Logic_list x)
        ; typ_constr
            (pilogic ())
            (typ_constr (pinj_nat_t ()) (typ_constr (pinj_nat ()) nil ^:: nil) ^:: nil)
          |> map0 ~f:`Logic_nat
        ; typ_constr (pilogic ()) (typ_constr (pinj_option_t ()) (__ ^:: nil) ^:: nil)
          |> map1 ~f:(fun x -> `Logic_option x)
        ; typ_constr (pilogic ()) (typ_constr (path [ "int" ]) nil ^:: nil)
          |> map0 ~f:`Int_ilogic
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
              Format.fprintf ppf " /*%s*/" (to_caml_string rest))
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

let pp_ast_as_kotlin inh_info =
  let path_is_none path =
    (* Format.eprintf "log[path_is_none]: %a\n%!" Path.print path; *)
    String.equal (Format.asprintf "%a" Path.print path) "OCanren!.Std.none"
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
    (* | Fresh (xs, e) ->
         fprintf ppf "@[<v>";
        List.iter xs ~f:(fun (name, typ) ->
          fprintf
            ppf
            "@[val %s : %a = freshTypedVar();@]@ "
            name
            (pp_typ_as_kotlin inh_info)
            typ);
        fprintf ppf "@[%a@]@]" helper e *)
    | Fresh (xs, Pause e) ->
      fprintf ppf "@[@[<hov 2>freshTypedVars { ";
      pp_comma_list
        (fun ppf (name, typ) ->
          fprintf ppf "@[%s: %a@]" name (pp_typ_as_kotlin inh_info) typ)
        ppf
        xs;
      fprintf ppf " ->@]@ %a@ @[}@]@]" default e
    | Fresh (xs, e) ->
      fprintf ppf "/* NOTE: fresh without delay */@ ";
      fprintf ppf "@[<hov>@[freshTypedVars {";
      pp_comma_list
        (fun ppf (name, typ) ->
          fprintf ppf "@[ %s : %a@]" name (pp_typ_as_kotlin inh_info) typ)
        ppf
        xs;
      fprintf ppf " ->@]@ %a@ @[}@]@]" default e
    | Unify (l, r) when par ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "(%a `===` %a)" default l default r
    (* fprintf ppf "(%a debugUnify %a)" pp_term_as_kotlin l pp_term_as_kotlin r *)
    | Unify (l, r) ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "%a `===` %a" default l default r
    | Call_rel (path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Call_rel (p, args) ->
      let kotlin_func =
        let repr = Format.asprintf "%a" Printtyp.path p in
        match Inh_info.lookup_expr_exn inh_info repr with
        | exception Not_found -> repr
        | s -> s
      in
      fprintf ppf "@[%s(%a)@]" kotlin_func (pp_comma_list default) args
    | Tapp (Tident path, [ Tunit ]) when path_is_none path -> fprintf ppf "None()"
    | Tapp (f, args) ->
      Format.printf "Application %d\n%!" __LINE__;
      (*  *)
      fprintf ppf "@[%a(%a)@]" default f (pp_comma_list default) args
    | Tident p -> fprintf ppf "%s" (Path.name p)
    (* | Conde xs -> fprintf ppf "@[conde(%a)@]" (pp_comma_list helper) xs *)
    | Conde xs ->
      fprintf ppf "@[<v 6>conde(";
      List.iteri xs ~f:(fun i ->
        if i <> 0 then fprintf ppf ",@ ";
        nopar ppf);
      fprintf ppf ")@]"
    | Conj_multi xs ->
      (* fprintf ppf "@[and(%a)@]" (pp_comma_list helper) xs *)
      fprintf ppf "@[<v 4>and(";
      List.iteri xs ~f:(fun i ->
        if i <> 0 then fprintf ppf ",@ ";
        nopar ppf);
      fprintf ppf ")@]"
    | Infix_conj2 (l, r) -> fprintf ppf "@[(%a and %a)@]" default l default r
    | T_int n -> fprintf ppf "%d.toLogic()" n
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "nilLogicList()"
    | T_list_cons (h, tl) -> fprintf ppf "@[(%a + %a)@]" default h default tl
    | Tabstr (names, rhs) ->
      fprintf ppf "@[{ ";
      List.iteri names ~f:(fun i (name, _typ) ->
        if i <> 0 then fprintf ppf ", ";
        fprintf ppf " %s" name);
      fprintf ppf "-> %a }@]" nopar rhs
    | Tunit -> fprintf ppf "/* Unit */"
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
        Format.eprintf "Unsupported case: '%a'\n%!" Printtyp.type_expr desc;
        assert false)
      (fun acc -> acc)
  in
  fun texpr -> helper S.empty texpr
;;

let pp_rvb_as_kotlin inh_info ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
      (fun ppf (name, typ) -> fprintf ppf "%s: %a" name (pp_typ_as_kotlin inh_info) typ)
      ppf
  in
  let tvars =
    List.fold_left
      ~f:(fun acc (_, typ) -> S.union acc (collect_type_variables typ))
      ~init:S.empty
      args
  in
  fprintf
    ppf
    "@[fun %s %s(%a): Goal =@]@,@[%a@]\n%!"
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
    name
    pp_args
    args
    (pp_ast_as_kotlin inh_info)
    body
;;

(* pp_typ_as_kotlin *)
let pp_modtype_as_kotlin info name sign ppf =
  let open Format in
  (* printf "%s %d\n%!" __FILE__ __LINE__; *)
  let printfn fmt = Format.kfprintf (fun fmt -> fprintf fmt "@,") ppf fmt in
  (* let printf fmt = Format.fprintf ppf fmt in *)
  fprintf ppf "// %s \n%!" name;
  printfn "@[<v 2>@[interface %s {@]" name;
  let gensym =
    let c = ref 0 in
    fun () ->
      incr c;
      Printf.sprintf "v%d" !c
  in
  List.iter sign.Typedtree.sig_items ~f:(fun sitem ->
    match sitem.sig_desc with
    | Tsig_value { val_name = { txt = name; _ }; val_val = { val_type; _ }; _ } ->
      let args, ret = unparse_arrows val_type in
      printfn "@[// %s@]" name;
      (* TODO: generate varnames *)
      printfn "@[fun %s(" name;
      List.iteri args ~f:(fun i t ->
        if i <> 0 then fprintf ppf ",@ ";
        fprintf ppf "@[%s: %a@]" (gensym ()) (pp_typ_as_kotlin info) t);
      fprintf ppf "@ ): %a" (pp_typ_as_kotlin info) ret;
      printfn "@]"
    | _ -> printfn "@[//@]");
  printfn "}@]\n"
;;
