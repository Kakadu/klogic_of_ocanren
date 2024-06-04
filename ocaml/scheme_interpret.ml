(*
   Quines stuff by Dmitrii Rozplokhas. Adopted from
  https://raw.githubusercontent.com/rozplokhas/OCanren/master/regression/test015.ml
*)

open Printf
open OCanren
open Scheme_ast

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
let[@skip_from_klogic] ( =/= ) = OCanren.( =/= )
let[@skip_from_klogic] ( =//= ) = OCanren.( =/= )
(*
   let demo : string ilogic -> goal =
 fun term ->
  let open OCanren.Std in
  term === !!"list"
;; *)

let rec lookupo : _ -> fenv -> Gresult.injected -> goal =
 fun x env t ->
  let open OCanren.Std in
  fresh
    (rest y v)
    (Std.Pair.pair y v % rest === env)
    (conde [ y === x &&& (v === t); y =/= x &&& lookupo x rest t ])
;;

let rec not_in_envo : _ -> fenv -> goal =
 fun x env ->
  let open OCanren.Std in
  conde
    [ fresh (y v rest) (env === Std.pair y v % rest) (y =/= x) (not_in_envo x rest)
    ; nil () === env
    ]
;;

let rec proper_listo : (Gterm.injected Std.List.injected as 'i) -> fenv -> 'i -> goal =
 fun es env rs ->
  let open OCanren.Std in
  conde
    [ Std.nil () ====^ es &&& (Std.nil () ====^ rs)
    ; fresh
        (e d te td)
        (es ====^ e % d)
        (rs ====^ te % td)
        (evalo e env (val_ te))
        (proper_listo d env td)
    ]

and evalo : Gterm.injected -> fenv -> Gresult.injected -> goal =
 fun term env r ->
  let open OCanren.Std in
  conde
    [ fresh
        t
        (term === seq (symb !!"quote" %< t))
        (r === val_ t)
        (not_in_envo !!"quote" env)
    ; fresh
        (es rs)
        (term === seq (symb !!"list" % es))
        (r === val_ (seq rs))
        (not_in_envo !!"list" env)
        (proper_listo es env rs)
    ; fresh s (term === symb s) (lookupo s env r)
    ; fresh
        (func arge arg x body env')
        (term === seq (func %< arge))
        (evalo arge env arg)
        (evalo func env (closure x body env'))
        (evalo body (Std.pair x arg % env') r)
    ; fresh
        (x body)
        (term === seq (symb !!"lambda" % (seq !<(symb x) %< body)))
        (not_in_envo !!"lambda" env)
        (r === closure x body env)
    ]
;;
(*
   let s tl = seq (Std.list Fun.id tl)
let nil = Std.nil ()
let quineso q = evalo q nil (val_ q)
let twineso q p = q =/= p &&& evalo q nil (val_ p) &&& evalo p nil (val_ q)

let thrineso p q r =
  (* let (=//=) = diseqtrace @@ show_reif_term in *)
  fresh
    ()
    (p =//= q)
    (q =//= r)
    (r =//= p)
    (evalo p nil (val_ q))
    (evalo q nil (val_ r))
    (evalo r nil (val_ p))
;;

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
let find2thrines = find_thrines 2
*)
