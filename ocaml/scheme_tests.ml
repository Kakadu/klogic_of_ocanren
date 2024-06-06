open OCanren
open Scheme_ast

let%expect_test "fresh symbol" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let symb x = !!(Symb x) in
      fresh tmp (q === symb tmp))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x -> Format.printf "%a\n%!" (GT.fmt Gterm.logic) x);
  [%expect "_.1"]
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
  [%expect {| (list _.1 (list (quote quote) _.1)) |}]
;;

let%expect_test "first quine" =
  Scheme_interpret.find_quines ~verbose:true 1;
  [%expect {|  |}];
  OCanren.(run q)
    (fun q -> Scheme_interpret.evalo2 q (Std.nil ()) (Gresult.val_ q))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x ->
    Format.printf "%a\n\n%a\n%!" Gterm.verbose_print x (GT.fmt Gterm.logic) x);
  [%expect {|  |}]
;;

let%expect_test " " =
  Scheme_interpret.find_quines ~verbose:true 1;
  [%expect {|  |}];
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
        (start === seq_ [ half; half ])
        (Scheme_interpret.evalo2 q (Std.nil ()) (Gresult.val_ q)))
    (fun rr -> rr#reify Gterm.reify)
  |> Stream.take ~n:1
  |> List.iter (fun x ->
    Format.printf "%a\n\n%a\n%!" Gterm.verbose_print x (GT.fmt Gterm.logic) x);
  [%expect {|  |}]
;;
