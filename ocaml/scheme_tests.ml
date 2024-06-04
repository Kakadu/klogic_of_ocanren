open Scheme_ast

let%expect_test "fresh symbol" =
  let open Gterm in
  OCanren.(run q)
    (fun q ->
      let open OCanren.Std in
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
      let open OCanren.Std in
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
      let open OCanren.Std in
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
