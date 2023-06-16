open Stdppx

type 'a ast =
  | Pause of 'a
  | Mplus of 'a * 'a
  | Other of Typedtree.expression
  | Error

let translate fallback : (_, Typedtree.expression ast) Tast_folder.t =
  let open struct
    open Tast_pattern

    let pat_pause () : (Typedtree.expression, _ ast -> 'a, 'b) Tast_pattern.t =
      texp_apply1
        (texp_ident (path [ "pause" ]))
        (texp_function (case tpat_unit drop __ ^:: nil))
      |> map1 ~f:(fun x -> Pause x)
    ;;

    let pat_mplus () : (Typedtree.expression, _ -> 'a, 'b) Tast_pattern.t =
      texp_let (value_binding drop drop ^:: nil)
      @@ texp_apply2 (texp_ident (path [ "mplus " ])) __ __
      |> map2 ~f:(fun x y -> Mplus (x, y))
    ;;

    let pat () = pat_pause () ||| pat_mplus ()
  end in
  Printf.printf "%s %d\n" __FILE__ __LINE__;
  (*  *)
  let open Tast_folder in
  { fallback with
    expr =
      (fun self acc expr ->
        let open Typedtree in
        let loc = expr.exp_loc in
        let acc =
          Tast_pattern.parse
            (pat ())
            loc
            ~on_error:(fun _desc () -> Error)
            expr
            (fun ast () ->
              match ast with
              | _ -> ast)
            ()
        in
        fallback.expr self acc expr)
  }
;;

let analyze_cmt source_file stru =
  Out_channel.with_file "asdf.kt" ~f:(fun _ ->
    let folder = translate Tast_folder.default in
    (* let (_ : int) = folder.Tast_folder.stru in *)
    let (), _ = folder.Tast_folder.stru folder () stru in
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
