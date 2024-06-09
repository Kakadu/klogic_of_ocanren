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
  | Fresh of (string * (Types.type_expr[@printer fun fmt _ -> fprintf fmt "?"])) list * 'a
  | Wildcard of string * (Types.type_expr[@printer fun fmt _ -> fprintf fmt "?"]) * 'a
  | Unify of 'a * 'a
  | Diseq of 'a * 'a
  | Call_rel of (Path.t[@printer Path.print]) * 'a list
  | Tapp of 'a * 'a list (** Application of terms. Is similar to Call_rel *)
  | T_int of int
  | T_bool of bool
  | T_string of string
  | T_list_init of 'a list
  | T_list_nil
  | T_list_cons of 'a * 'a
  | Tabstr of
      ((string * (Types.type_expr[@printer fun fmt _ -> fprintf fmt "?"])) list * 'a)
  (** TODO: Types? *)
  | Tident of Path.t [@printer fun fmt _ -> fprintf fmt "?"] (** TODO: Do we need this? *)
  | Tunit
  | Other of
      (Typedtree.expression
      [@printer
        fun fmt e ->
          Format.fprintf fmt "'%a'" Pprintast.expression (Untypeast.untype_expression e)])
[@@deriving show]

let rec pp fmt x = pp_ast pp fmt x

(** Relational value bindings *)
module Rvb = struct
  type t =
    { name : string
    ; args : (string * Types.type_expr) list
    ; body : 'a ast as 'a
    }

  let mk name args body = { name; args; body }
end

let pp_list ppf = Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " ") ppf

let map_ast f = function
  | Pause x -> Pause (f x)
  | St_abstr e -> St_abstr (f e)
  | St_app e -> St_app (f e)
  | Fresh (xs, e) -> Fresh (xs, f e)
  | Wildcard (v, t, e) -> Wildcard (v, t, f e)
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
  | (Tunit | Tident _ | Other _ | T_list_nil | T_int _ | T_bool _ | T_string _) as rez ->
    rez
  | Unify (a, b) -> Unify (f a, f b)
  | Diseq (a, b) -> Diseq (f a, f b)
;;

let has_vars_inside =
  let exception Found in
  let rec helper = function
    | Tident _ -> raise Found
    | Other _ | T_int _ | T_bool _ | Tunit | T_list_nil | T_string _ -> ()
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
      | Tapp (_, _)
      | T_list_init _
      | T_list_cons (_, _)
      | Tabstr _ ) as x -> ignore (map_ast helper x)
    (* | _ -> false *)
  in
  fun t ->
    try
      let _ = helper t in
      false
    with
    | Found -> true
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
          | Infix_conj2 (a, b) -> [ helper a; helper b ]
          | x -> [ helper x ]))
    | other -> map_ast helper other
  in
  fun x ->
    (* print_endline "Call simplify_ast"; *)
    helper x
;;

let%expect_test "simplify AST" =
  let u = Unify (T_int 0, T_int 1) in
  let input =
    Conde [ Conj_multi [ Infix_conj2 (u, u); u ]; Conj_multi [ Infix_conj2 (u, u); u ] ]
  in
  let out = simplify_ast input in
  Format.printf "%a\n%!" pp out;
  [%expect
    {|
    (AST.Conde
       [(AST.Conj_multi
           [(AST.Unify ((AST.T_int 0), (AST.T_int 1)));
             (AST.Unify ((AST.T_int 0), (AST.T_int 1)));
             (AST.Unify ((AST.T_int 0), (AST.T_int 1)))]);
         (AST.Conj_multi
            [(AST.Unify ((AST.T_int 0), (AST.T_int 1)));
              (AST.Unify ((AST.T_int 0), (AST.T_int 1)));
              (AST.Unify ((AST.T_int 0), (AST.T_int 1)))])
         ]) |}];
  let input =
    let rel = Call_rel (Path.Pident (Ident.create_local "r1"), [ u ]) in
    (* let typ =
      Types.Transient_expr.create (Types.Tvar None) ~level:0 ~scope:0 ~id:0
      |> Types.Transient_expr.type_expr
    in *)
    Conj_multi [ Conde [ Infix_conj2 (Infix_conj2 (u, u), rel) ] ]
  in
  let out = simplify_ast input in
  Format.printf "%a\n%!" pp out;
  [%expect
    {|
    (AST.Conj_multi
       [(AST.Conde
           [(AST.Conj_multi
               [(AST.Unify ((AST.T_int 0), (AST.T_int 1)));
                 (AST.Unify ((AST.T_int 0), (AST.T_int 1)));
                 (AST.Call_rel (?, [(AST.Unify ((AST.T_int 0), (AST.T_int 1)))]))
                 ])
             ])
         ])

    |}]
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
    ; mutable preamble : (Trans_config.transl_lang * string) list
    ; mutable epilogue : (Trans_config.transl_lang * string) list
    }

  let create () =
    { type_mangle_hints = Hashtbl.create 13
    ; expr_mangle_hints = Hashtbl.create 13
    ; rvbs = []
    ; preamble = [ Trans_config.Scheme, ""; Trans_config.Kotlin, "" ]
    ; epilogue = [ Trans_config.Scheme, ""; Trans_config.Kotlin, "" ]
    }
  ;;

  let extend t item = t.rvbs <- item :: t.rvbs
  let add_rvb t rvb = extend t (RVB rvb)
  let add_modtype t ident types = t.rvbs <- MT_as_interface (ident, types) :: t.rvbs

  let add_functor t other_info ~name ~typ ~arg_name ~arg_typ =
    extend t (Functor1 { name; typ; arg_name; arg_typ; body = List.rev other_info.rvbs })
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

  let add_preamble kind t s =
    t.preamble
    <- List.map t.preamble ~f:(fun (k, p) ->
         match k, kind with
         | Trans_config.Scheme, Trans_config.Scheme | Kotlin, Kotlin -> k, p ^ s
         | _ -> k, p)
  ;;

  let add_epilogue kind t s =
    (* TODO: avoid copypaste *)
    t.epilogue
    <- List.map t.epilogue ~f:(fun (k, p) ->
         match k, kind with
         | Trans_config.Scheme, Trans_config.Scheme | Kotlin, Kotlin -> k, p ^ s
         | _ -> k, p)
  ;;

  let preamble { preamble; _ } = preamble
  let epilogue { epilogue; _ } = epilogue
  let get_preamble kind t = List.assoc kind (preamble t)
  let get_epilogue kind t = List.assoc kind (epilogue t)
end

module SS = Set.Make (String)
