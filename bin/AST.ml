open Stdppx

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
  | Fresh of (string * Types.type_expr) list * 'a
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

let pp_term_as_kotlin =
  let open Format in
  let rec helper ppf = function
    | T_int n -> fprintf ppf "%d.toLogic()" n
    | T_list_init ls ->
      fprintf ppf "@[%a@]" (pp_print_list ~pp_sep:pp_print_space helper) ls
    | T_list_nil -> fprintf ppf "nilLogicList()"
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

module Inh_info = struct
  type t =
    { type_mangle_hints : (string, string) Hashtbl.t
    ; mutable rvbs : Rvb.t list
    ; mutable preamble : string
    ; mutable epilogue : string
    }

  let create () =
    { type_mangle_hints = Hashtbl.create 13; rvbs = []; preamble = ""; epilogue = "" }
  ;;

  let add_rvb t rvb = t.rvbs <- rvb :: t.rvbs
  let lookup_typ_exn t typ = Hashtbl.find t.type_mangle_hints typ

  let add_hints info hints =
    (* log "add %d hints" (List.length hints); *)
    List.iter hints ~f:(fun (key, data) ->
      (* log "adding a type hint %s -> %s%!" key data; *)
      Hashtbl.add_exn info.type_mangle_hints ~key ~data)
  ;;

  let iter_vbs { rvbs; _ } ~f = List.iter ~f (List.rev rvbs)
  let add_preamble t s = t.preamble <- t.preamble ^ s
  let add_epilogue t s = t.epilogue <- t.epilogue ^ s
  let preamble { preamble; _ } = preamble
  let epilogue { epilogue; _ } = epilogue
end

let pp_typ_as_kotlin inh_info ppf typ =
  let caml_repr =
    Format.asprintf "%a" Printtyp.type_expr typ |> Str.global_replace (Str.regexp "\n") ""
  in
  (* log "caml_repr = '%s'" caml_repr; *)
  match Inh_info.lookup_typ_exn inh_info caml_repr with
  | s -> Format.fprintf ppf "%s" s
  | exception Not_found -> Format.fprintf ppf "%s" caml_repr
;;

let pp_ast_as_kotlin ?(pretty = false) inh_info =
  let open Format in
  let rec helper ppf = function
    (* | St_abstr (Pause (Mplus )) *)
    | Pause (Fresh (xs, Bind (Bind (St_app a, b), c))) when pretty ->
      fprintf ppf "freshTypedVars { ";
      List.iter xs ~f:(fun (name, typ) ->
        fprintf ppf "@[%s : %a,@]@ " name (pp_typ_as_kotlin inh_info) typ);
      fprintf ppf " -> %a and %a and %a }@]" helper a helper b helper c
    | Bind (Bind (a, b), c) when pretty ->
      fprintf ppf "bind_star %a %a %a " helper a helper b helper c
    | Mplus (e, Pause (Mplus (e2, Pause e3))) ->
      fprintf ppf "conde [ %a; %a; %a ]" helper e helper e2 helper e3
      (* Pretty is above
         Default is below
       *)
    | Pause e -> fprintf ppf "@[pause { %a@ }@]" helper e
    | St_abstr l -> fprintf ppf "@[<v 2>@[{ st: State ->@ %a@ }@]" helper l
    | St_app l -> fprintf ppf "%a(st)" helper l
    | New_scope x -> helper ppf x
    | Mplus (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[mplus@]@,@,@[(%a)@])@]" helper l helper r
    | Bind (l, r) ->
      fprintf ppf "@[<v 2>(@[(%a)@]@,@[bind@]@,@[(%a)@])@]" helper l helper r
    | Fresh (xs, e) ->
      fprintf ppf "@[<v>";
      List.iter xs ~f:(fun (name, typ) ->
        fprintf
          ppf
          "@[val %s : %a = freshTypedVar();@]@ "
          name
          (pp_typ_as_kotlin inh_info)
          typ);
      fprintf ppf "@[%a@]@]" helper e
      (* fprintf
        ppf
        "@[<v 2>@[freshTypedVars { %a ->@]@,@[%a@]@[}@]@]"
        (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf ", ") pp_print_string)
        xs
        helper
        e *)
    | Unify (l, r) ->
      (* TODO: if left argument is an empty list, swap the arguments to make Kotlin typecheck this *)
      fprintf ppf "(%a `===` %a)" pp_term_as_kotlin l pp_term_as_kotlin r
      (* fprintf ppf "(%a debugUnify %a)" pp_term_as_kotlin l pp_term_as_kotlin r *)
    | Call_rel (p, args) ->
      fprintf ppf "@[%a(%a)@]" Printtyp.path p (pp_comma_list pp_term_as_kotlin) args
    | Other e -> fprintf ppf "@[{| Other %a |}@]" Pprintast.expression (MyUntype.expr e)
    | Error -> fprintf ppf "ERROR "
  in
  helper
;;

let pp_rvb_as_kotlin ~pretty inh_info ppf { Rvb.name; args; body } =
  let open Format in
  let pp_args ppf =
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
      (fun ppf (name, typ) -> fprintf ppf "%s: %a" name (pp_typ_as_kotlin inh_info) typ)
      ppf
  in
  Format.fprintf
    ppf
    "@[<v 2>@[fun %s(%a): Goal =@]@ @[%a@]@]\n%!"
    name
    pp_args
    args
    (pp_ast_as_kotlin ~pretty inh_info)
    body
;;
