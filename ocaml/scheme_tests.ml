open OCanren
open Scheme_ast

let s tl = Gterm.seq (Std.list Fun.id tl)
let nil = Std.nil ()
let quineso q = Scheme_interpret.evalo2 q nil (Gresult.val_ q)

let find_quines ~verbose n =
  run q quineso (fun r -> r#reify Gterm.reify)
  |> OCanren.Stream.take ~n
  |> List.iter (fun q ->
    if verbose then Printf.printf "%s\n" (Gterm.show_lterm q) else ())
;;

let%expect_test "fresh symbol" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let symb x = !!(Symb x) in
      fresh tmp (q === symb tmp))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x -> Format.printf "%a\n%!" (GT.fmt Gterm.logic) x);
  [%expect "_.11"]
;;

let%expect_test "lambda" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let open OCanren.Std in
      let seq xs : injected = !!(Seq xs) in
      let symb x = !!(Symb x) in
      let arg = seq (Std.list Fun.id [ symb !!"x" ]) in
      q === seq (symb !!"lambda" % (arg % !<(symb !!"y"))))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x -> Format.printf "%a\n%!" (GT.fmt Gterm.logic) x);
  [%expect {| (lambda (x) y) |}]
;;

let%expect_test "list0" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let seq xs : Gterm.injected = !!(Seq xs) in
      let symb x = !!(Symb x) in
      let list xs = seq (Std.list Fun.id (symb !!"list" :: xs)) in
      q === list [ symb !!"A"; symb !!"B" ])
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x -> Format.printf "%a\n%!" (GT.fmt Gterm.logic) x);
  [%expect "(list A B)"]
;;

let%expect_test "list" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let seq xs : Gterm.injected = !!(Seq xs) in
      let symb x = !!(Symb x) in
      let list xs = seq (Std.list Fun.id (symb !!"list" :: xs)) in
      let app f x = seq (Std.list Fun.id [ f; x ]) in
      fresh tmp (q === list [ tmp; list [ app (symb !!"quote") (symb !!"quote"); tmp ] ]))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x -> Format.printf "%a\n%!" (GT.fmt Gterm.logic) x);
  [%expect {| (list _.11 (list (quote quote) _.11)) |}]
;;

let%expect_test "first quine" =
  find_quines ~verbose:true 1;
  [%expect
    {| ((lambda (_.2464) (list _.2464 (list (quote quote) _.2464))) (quote (lambda (_.2464) (list _.2464 (list (quote quote) _.2464))))) |}];
  OCanren.(run q)
    (fun q -> Scheme_interpret.evalo2 q (Std.nil ()) (Gresult.val_ q))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x ->
    Format.printf "%a\n\n%a\n%!" Gterm.verbose_print x (GT.fmt Gterm.logic) x);
  [%expect
    {|
    (seq ((seq ((symb 'lambda) (seq ((symb '_.2464 [=/= list; =/= quote]) )) (seq ((symb 'list) (symb '_.2464 [=/= list; =/= quote]) (seq ((symb 'list) (seq ((symb 'quote) (symb 'quote) )) (symb '_.2464 [=/= list; =/= quote]) )) )) )) (seq ((symb 'quote) (seq ((symb 'lambda) (seq ((symb '_.2464 [=/= list; =/= quote]) )) (seq ((symb 'list) (symb '_.2464 [=/= list; =/= quote]) (seq ((symb 'list) (seq ((symb 'quote) (symb 'quote) )) (symb '_.2464 [=/= list; =/= quote]) )) )) )) )) ))

    ((lambda (_.2464) (list _.2464 (list (quote quote) _.2464))) (quote (lambda (_.2464) (list _.2464 (list (quote quote) _.2464))))) |}]
;;

let%expect_test " " =
  find_quines ~verbose:true 1;
  [%expect
    {| ((lambda (_.2464) (list _.2464 (list (quote quote) _.2464))) (quote (lambda (_.2464) (list _.2464 (list (quote quote) _.2464))))) |}];
  let open Scheme_ast in
  let open Scheme_ast.Gterm in
  OCanren.(run q)
    (fun q ->
      fresh
        (start half t2467)
        (half
        === seq_
              [ symb !!"lambda"
              ; seq_ [ symb t2467 ]
              ; seq_
                  [ symb !!"list"
                  ; symb t2467
                  ; seq_
                      [ symb !!"list"
                      ; seq_ [ symb !!"quote"; symb !!"quote" ]
                      ; symb t2467
                      ]
                  ]
              ])
        (start === seq_ [ half; quote half ])
        (Scheme_interpret.evalo2 start (Std.nil ()) (Gresult.val_ q)))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x ->
    Format.printf "%a\n\n%a\n%!" Gterm.verbose_print x (GT.fmt Gterm.logic) x);
  [%expect {|
    (seq ((seq ((symb 'lambda) (seq ((symb '_.197 [=/= list; =/= quote]) )) (seq ((symb 'list) (symb '_.197 [=/= list; =/= quote]) (seq ((symb 'list) (seq ((symb 'quote) (symb 'quote) )) (symb '_.197 [=/= list; =/= quote]) )) )) )) (seq ((symb 'quote) (seq ((symb 'lambda) (seq ((symb '_.197 [=/= list; =/= quote]) )) (seq ((symb 'list) (symb '_.197 [=/= list; =/= quote]) (seq ((symb 'list) (seq ((symb 'quote) (symb 'quote) )) (symb '_.197 [=/= list; =/= quote]) )) )) )) )) ))

    ((lambda (_.197) (list _.197 (list (quote quote) _.197))) (quote (lambda (_.197) (list _.197 (list (quote quote) _.197)))))
    |}]
;;
