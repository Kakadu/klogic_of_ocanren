open Oleg_numbers

(* let%expect_test _ =
  OCanren.(run q)
    (fun q -> multo (build_num 3) (build_num 5) q)
    (fun rr -> rr#reify prj_exn)
  |> OCanren.Stream.take ~n:2
  |> List.iteri (fun i n -> Printf.printf "  %3d: %d\n" i (to_int n));
  [%expect {| 0: 15 |}]
;;
*)
