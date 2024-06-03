type loc = unit

exception Expected of loc * string

let fail loc expected = raise (Expected (loc, expected))

type context =
  { (* [matched] counts how many constructors have been matched. This is used to find what
     pattern matches the most some piece of ast in [Ast_pattern.alt]. In the case where
     all branches fail to match, we report the error from the one that matches the
     most.

     This is only incremented by combinators that can fail. *)
    mutable matched : int
  }

type ('matched_value, 'k, 'k_result) t =
  | T of (context -> loc -> 'matched_value -> 'k -> 'k_result)

let save_context ctx = ctx.matched
let restore_context ctx backup = ctx.matched <- backup
let incr_matched c = c.matched <- c.matched + 1
let __ : 'a 'b. ('a, 'a -> 'b, 'b) t = T (fun _ctx _loc x k -> k x)

let parse : 'a 'b 'c. ('a, 'b, 'c) t -> loc -> ?on_error:(string -> 'c) -> 'a -> 'b -> 'c =
 fun (T f) loc ?on_error x k ->
  try f { matched = 0 } loc x k with
  | Expected (_loc, expected) ->
    (match on_error with
    | None -> failwith (Printf.sprintf "%s expected" expected)
    | Some f -> f expected)
;;

let alt (T f1) (T f2) =
  T
    (fun ctx loc x k ->
      let backup = save_context ctx in
      try f1 ctx loc x k with
      | e1 ->
        let m1 = save_context ctx in
        restore_context ctx backup;
        (try f2 ctx loc x k with
        | e2 ->
          let m2 = save_context ctx in
          if m1 >= m2
          then (
            restore_context ctx m1;
            raise e1)
          else raise e2))
;;

let ( ||| ) = alt

let ( <|> ) (T f1) (T f2) =
  T
    (fun ctx loc x k ->
      try f1 ctx loc x k with
      | Expected _ -> f2 ctx loc x k)
;;

let conde = function
  | [] -> failwith "Bad argument"
  | h :: tl -> List.fold_left ( <|> ) h tl
;;

let map1 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a -> k (f a)))
let map2 (T func) ~f = T (fun ctx loc x k -> func ctx loc x (fun a b -> k (f a b)))

let cst ~to_string ?(equal = Stdlib.( = )) v =
  T
    (fun ctx loc x k ->
      if equal x v
      then (
        incr_matched ctx;
        k)
      else fail loc (to_string v))
;;

let string v = cst ~to_string:(Printf.sprintf "%S") v
