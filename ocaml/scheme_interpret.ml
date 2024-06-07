(*
   Quines stuff by Dmitrii Rozplokhas. Adopted from
  https://raw.githubusercontent.com/rozplokhas/OCanren/master/regression/test015.ml
*)

(*  *)
open Printf
open OCanren
open Scheme_ast
(*  *)
(* include Counters.Make () [@skip_from_klogic] *)

let list_combine3 xs ys zs =
  let rec helper acc = function
    | x :: xs, y :: ys, z :: zs -> helper ((x, y, z) :: acc) (xs, ys, zs)
    | [], [], [] -> List.rev acc
    | _ -> failwith "bad argument of list_combine3"
  in
  helper [] (xs, ys, zs)
;;

let list_iter3 f xs ys zs =
  let rec helper = function
    | x :: xs, y :: ys, z :: zs ->
      f (x, y, z);
      helper (xs, ys, zs)
    | [], [], [] -> ()
    | _ -> failwith "bad argument of list_combine3"
  in
  helper (xs, ys, zs)
;;

open Gterm
open Gresult

(* let[@skip_from_klogic] ( === )  : 'a -> 'a -> goal = fun _ _ -> assert false *)
let show_reif_term h t = show_lterm @@ Gterm.reify h t
let show_reif_result h t = show_lresult @@ gresult_reifier h t
let trace_enabled = ref true
let is_trace_enabled () = !trace_enabled
let set_trace x = trace_enabled := x

[@@@ocamlformat.disable]

let[@skip_from_klogic] ( ===! ) = OCanren.( === )

(* let (===!!) = OCanren.(===)  *)
let[@skip_from_klogic] ( ==== ) = OCanren.( === )
let[@skip_from_klogic] ( ====^ ) = OCanren.( === )
let[@skip_from_klogic] ( ===!! ) = OCanren.( === )
let[@skip_from_klogic] ( ==!! ) = OCanren.( === )

(* let[@skip_from_klogic] ( =/= ) = OCanren.( =/= ) *)
let[@skip_from_klogic] ( =//= ) = OCanren.( =/= )

(*
   let demo : string ilogic -> goal =
 fun term ->
  let open OCanren.Std in
  term === !!"list"
;; *)
(*
   let demo : string ilogic -> goal =
 fun term ->
  let open OCanren.Std in
  term === !!"list"
;;

let demo2 : string ilogic -> goal =
 fun term ->
  let open OCanren.Std in
  term =/= !!"list"
;; *)
(* let not_closure : Gresult.injected -> goal =
 fun term ->
  let open OCanren.Std in
  fresh (x body env) (term =/= closure x body env)
;; *)

let rec lookupo2 : _ -> fenv -> Gresult.injected -> goal =
 fun x env t ->
  let open OCanren.Std in
  fresh
    (rest y v)
    (Std.Pair.pair y v % rest === env)
    (conde [ y === x &&& (v === t); y =/= x &&& lookupo2 x rest t ])
;;

let rec not_in_envo2 : _ -> fenv -> goal =
 fun x env ->
  let open OCanren.Std in
  conde
    [ fresh (y v rest) (env === Std.pair y v % rest) (y =/= x) (not_in_envo2 x rest)
    ; nil () === env
    ]
;;

let rec proper_listo2 : (Gterm.injected Std.List.injected as 'i) -> fenv -> 'i -> goal =
 fun es env rs ->
  let open OCanren.Std in
  conde
    [ Std.nil () === es &&& (Std.nil () === rs)
    ; fresh
        (e d te td)
        (es === e % d)
        (rs === te % td)
        (evalo2 e env (val_ te))
        (proper_listo2 d env td)
    ]

and evalo2 : Gterm.injected -> fenv -> Gresult.injected -> goal =
 fun term env r ->
  let open OCanren.Std in
  conde
    [ fresh
        t
        (term === seq (symb !!"quote" % (t % nil ())))
        (r === val_ t)
        (not_in_envo2 !!"quote" env)
    ; fresh
        (es rs)
        (term === seq (symb !!"list" % es))
        (r === val_ (seq rs))
        (not_in_envo2 !!"list" env)
        (proper_listo2 es env rs)
    ; fresh s (term === symb s) (lookupo2 s env r)
    ; fresh
        (func arge arg x body env2)
        (term === seq (func % (arge % nil ())))
        (evalo2 arge env arg)
        (evalo2 func env (closure x body env2))
        (evalo2 body (Std.pair x arg % env2) r)
    ; fresh
        (x body)
        (term === seq (symb !!"lambda" % (seq (symb x % nil ()) % (body % nil ()))))
        (not_in_envo2 !!"lambda" env)
        (r === closure x body env)
    ]
;;

(* let s tl = seq (Std.list Fun.id tl)
let nil = Std.nil ()
let quineso q = evalo2 q nil (val_ q) *)
(* let twineso q p = fresh () (q =/= p) (evalo2 q nil (val_ p)) (evalo2 p nil (val_ q))

let thrineso p q r =
  (* let (=//=) = diseqtrace @@ show_reif_term in *)
  fresh
    ()
    (p =//= q)
    (q =//= r)
    (r =//= p)
    (evalo2 p nil (val_ q))
    (evalo2 q nil (val_ r))
    (evalo2 r nil (val_ p))
;; *)
(*
   let wrap_term rr = rr#reify Gterm.reify |> show_lterm
let wrap_result rr = rr#reify gresult_reifier |> show_lresult

let find_quines ~verbose n =
  run q quineso (fun r -> r#reify Gterm.reify)
  |> OCanren.Stream.take ~n
  |> List.iter (fun q -> if verbose then printf "%s\n" (show_lterm q) else ())
;;

let find_twines ~verbose n =
  run qr twineso (fun q r -> q#reify Gterm.reify, r#reify Gterm.reify)
  |> OCanren.Stream.take ~n
  |> List.iter (fun (q, r) ->
    if verbose then printf "%s,\n%s\n" (show_lterm q) (show_lterm r) else ())
;;

let find_thrines ~verbose n =
  run qrs thrineso (fun r1 r2 r3 ->
    r1#reify Gterm.reify, r2#reify Gterm.reify, r3#reify Gterm.reify)
  |> Stream.take ~n
  |> List.iter (fun (q, r, s) ->
    if verbose
    then printf "%s,\n%s\,\n%s\n" (show_lterm q) (show_lterm r) (show_lterm s)
    else ())
;;

let find100quines = find_quines 100
let find15twines = find_twines 15
let find2thrines = find_thrines 2 *)
