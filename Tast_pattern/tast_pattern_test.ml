open Ppxlib.Ast_pattern

let plist item =
  let open Ppxlib.Ast_pattern in
  let rec helper acc e =
    match e.Parsetree.pexp_desc with
    | Parsetree.Pexp_construct ({ txt = Lident "[]" }, _) -> List.rev acc
    | Parsetree.Pexp_construct
        ({ txt = Lident "::" }, Some { pexp_desc = Parsetree.Pexp_tuple [ h; tl ] }) ->
      helper (h :: acc) tl
    | _ -> assert false
  in
  of_func (fun ctx loc e k ->
    let items = helper [] e in
    Format.printf "%s %d\n%!" __FILE__ __LINE__;
    List.iteri (fun i e -> Format.printf "%d: %a\n%!" i Pprintast.expression e) items;
    let items = List.map (fun e -> to_func item ctx loc e Fun.id) items in
    k items)
;;

let%expect_test " " =
  let e =
    let open Ppxlib in
    let loc = Location.none in
    [%expr [ 1; 2; 3; 4 ]]
  in
  let open Ppxlib.Ast_pattern in
  let () =
    parse
      (plist __)
      Location.none
      e
      (fun es ->
        print_endline "parsed";
        List.iteri
          (fun i e -> Format.printf "%d: expr <%a>\n%!" i Pprintast.expression e)
          es)
      ~on_error:(fun () -> assert false)
  in
  [%expect
    {|
    Tast_pattern/tast_pattern_test.ml 15
    0: 1
    1: 2
    2: 3
    3: 4
    parsed
    0: expr <1>
    1: expr <2>
    2: expr <3>
    3: expr <4> |}]
;;

let%expect_test " " =
  let e =
    let open Ppxlib in
    let loc = Location.none in
    [%expr [ 1; 2; 3; 4 ]]
  in
  let open Ppxlib.Ast_pattern in
  let () =
    parse
      (plist (eint __))
      Location.none
      e
      (fun es ->
        print_endline "parsed";
        List.iteri (fun i e -> Format.printf "%d: int <%d>\n%!" i e) es)
      ~on_error:(fun () -> assert false)
  in
  [%expect
    {|
    Tast_pattern/tast_pattern_test.ml 15
    0: 1
    1: 2
    2: 3
    3: 4
    parsed
    0: int <1>
    1: int <2>
    2: int <3>
    3: int <4> |}]
;;
(* (* open Tast_pattern *)

let%expect_test " " =

  (* Clflags.include_dirs := List.append (get_std_lib_pathes ()) !Clflags.include_dirs; *)
  let modulename = "MOdule" in
  Env.set_unit_name modulename;
  let te =
    match
      let env = Compmisc.initial_env () in
      Typemod.type_implementation "input" "ml" modulename env e
    with
    | { Typedtree.structure =
          { str_items = [ { str_desc = Typedtree.Tstr_eval (te, _) } ] }
      ; _
      } -> te
    | exception Env.Error e ->
      Env.report_error Format.std_formatter e;
      assert false
    | _ -> assert false
  in
  let open Tast_pattern in
  parse (texp_list __) Location.none te (fun _ -> print_endline "OK");
  [%expect {| |}]
;;
*)
