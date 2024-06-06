(** Term representation for Scheme interpreter  *)
open OCanren

module StringLo = struct
  type ground = GT.string [@@deriving gt ~options:{ show; fmt; gmap }]
  type logic = string OCanren.logic

  let logic =
    { GT.gcata = ()
    ; fix = (fun _ _ -> assert false)
    ; plugins =
        object
          method fmt = GT.fmt OCanren.logic (fun ppf -> Format.fprintf ppf "%s")
          method gmap x = [%gmap: GT.string OCanren.logic] () x
        end
    }
  ;;

  type injected = GT.string OCanren.ilogic

  let prj_exn = OCanren.prj_exn
  let reify = OCanren.reify
end

module ListLo = struct
  type 'a ground = 'a Std.List.ground [@@deriving gt ~options:{ gmap; fmt }]
  type 'a logic = 'a Std.List.logic

  let logic =
    { Std.List.logic with
      plugins =
        object
          method fmt fa ppf xs =
            let default ppf xs = (GT.fmt Std.List.logic) fa ppf xs in
            match xs with
            | Var _ -> default ppf xs
            | Value _ ->
              let rec iter ppf xs =
                match xs with
                | Value Std.List.Nil -> ()
                | Value (Std.List.Cons (h, tl)) -> Format.fprintf ppf "%a %a" fa h iter tl
                | Var _ -> Format.fprintf ppf " . %a" default xs
              in
              Format.fprintf ppf "(%a)" iter xs

          method gmap fa xs = [%gmap: 'a Std.List.logic] (GT.lift fa) () xs
        end
    }
  ;;

  type 'a injected = 'a Std.List.groundi

  let prj_exn = Std.List.prj_exn
  let reify = Std.List.reify
end

module Gterm = struct
  [@@@ocaml.warnerror "-32-34"]

  [%%distrib
  type nonrec ('s, 'xs) t =
    | Symb of 's
    | Seq of 'xs
  [@@deriving gt ~options:{ fmt; gmap }]

  type ground = (StringLo.ground, ground ListLo.ground) t]

  let t =
    { t with
      gcata = ()
    ; plugins =
        object
          method gmap = t.plugins#gmap

          method fmt fa fb fmt =
            GT.transform
              t
              (fun fself ->
                object
                  inherit ['a, 'b, _] fmt_t_t fa fb fself
                  method! c_Symb fmt _ str = Format.fprintf fmt "(symb '%a)" fa str
                  method! c_Seq fmt _ xs = Format.fprintf fmt "(seq %a)" fb xs
                end)
              fmt
        end
    }
  ;;

  (* This is a hack to apply custom printers for logic strings and lists *)
  type logic = (StringLo.logic, logic ListLo.logic) t OCanren.logic
  [@@deriving gt ~options:{ fmt; gmap }]

  let verbose_print fmt : logic -> unit = GT.fmt logic fmt

  (* let _ : (Format.formatter -> logic -> unit) -> logic fmt_logic_t = new fmt_logic_t
  let __ () =
  GT.transform ground (fun (_:Format.formatter -> ground -> unit) -> assert false) Format.std_formatter (Symb "!!")

 let __ () =
  GT.transform logic (fun (_:Format.formatter -> logic -> unit) -> assert false) Format.std_formatter
    (Value (Symb (Value  "!!")))
  *)

  class ['extra_logic] fmt_logic_t _fself_logic =
    object
      inherit [Format.formatter, 'extra_logic, unit] logic_t
      constraint 'extra_logic = logic

      inherit
        [(StringLo.logic, logic ListLo.logic) t, 'extra_logic] OCanren.fmt_logic_t
          (fun inh___040_ subj___041_ ->
            GT.fmt
              t
              (fun inh___042_ subj___043_ -> GT.fmt StringLo.logic inh___042_ subj___043_)
              (fun inh___044_ subj___045_ ->
                GT.fmt ListLo.logic _fself_logic inh___044_ subj___045_)
              inh___040_
              subj___041_)
          _fself_logic
    end

  include struct
    open FCPM

    let ( ^:: ) (T f0) (T f1) =
      T
        (fun ctx loc x k ->
          match x with
          | Value (Std.List.Cons (x0, x1)) ->
            incr_matched ctx;
            k |> f0 ctx loc x0 |> f1 ctx loc x1
          | _ -> fail loc "::")
    ;;

    let nil =
      T
        (fun ctx loc x k ->
          match x with
          | Value Std.List.Nil ->
            incr_matched ctx;
            k
          | _ -> fail loc "[]")
    ;;

    let finite_list (T f) : (_ Std.List.logic, _, _) FCPM.t =
      let rec helper ctx acc = function
        | Value (Std.List.Cons (h, tl)) ->
          incr_matched ctx;
          helper ctx (h :: acc) tl
        | Value Std.List.Nil -> List.rev acc
        | Var _ -> fail () "finite_list"
      in
      T (fun ctx loc x k -> k (helper ctx []))
    ;;

    let many (T f) =
      T
        (fun ctx loc l k ->
          let rec aux accu = function
            | [] -> k (List.rev accu)
            | x :: xs -> f ctx loc x (fun x -> aux (x :: accu) xs)
          in
          aux [] l)
    ;;

    (* matches logic list where List constructors are ground *)
    let manyl :
      'a 'b 'c. ('a, 'b -> 'c, 'c) FCPM.t -> ('a Std.List.logic, 'b list -> 'c, 'c) FCPM.t
      =
     fun (T f) ->
      T
        (fun ctx loc l k ->
          let rec aux accu = function
            | Var _ -> fail () "manyl"
            | Value Std.List.Nil ->
              (* Format.printf "manyl returns with %d elements\n%!" (List.length accu); *)
              k (List.rev accu)
            | Value (Std.List.Cons (x, xs)) ->
              f ctx loc x (fun x ->
                (* Format.printf "manyl eaten an element\n%!"; *)
                aux (x :: accu) xs)
          in
          aux [] l)
    ;;

    let unfinished_listl : _ =
     fun (T f) ->
      T
        (fun ctx loc l k ->
          let rec aux accu = function
            | Var _ as rest -> k (List.rev accu, rest)
            | Value Std.List.Nil -> fail () "unfinished_listl"
            | Value (Std.List.Cons (x, xs)) -> f ctx loc x (fun x -> aux (x :: accu) xs)
          in
          aux [] l)
    ;;

    let psymb : _ -> (logic, _, _) FCPM.t =
     fun (FCPM.T f) ->
      FCPM.T
        (fun ctx loc v k ->
          match v with
          | Value (Symb inner) ->
            incr_matched ctx;
            k |> f ctx loc inner
          | _ -> FCPM.fail () "psymb")
    ;;

    let pseq : (logic Std.List.logic, _, _) FCPM.t -> (logic, _, _) FCPM.t =
     fun (FCPM.T f) ->
      FCPM.T
        (fun ctx loc v k ->
          match v with
          | Value (Seq inner) ->
            incr_matched ctx;
            k |> f ctx loc inner
          | _ -> FCPM.fail () "pseq")
    ;;

    let pv : _ -> (_ OCanren.logic, _, _) FCPM.t =
     fun (FCPM.T f) ->
      FCPM.T
        (fun ctx loc v k ->
          match v with
          | Value x ->
            incr_matched ctx;
            k |> f ctx loc x
          | _ -> FCPM.fail () "pValue")
    ;;

    let plambda : _ -> _ -> (_ OCanren.logic, _, _) FCPM.t =
     fun parg pbody ->
      pseq (psymb (pv (string "lambda")) ^:: pseq (parg ^:: nil) ^:: pbody ^:: nil)
    ;;
  end

  let logic =
    let pp ppf =
      GT.transform_gc
        gcata_logic
        (fun fself ->
          object
            inherit [_] fmt_logic_t fself as super

            method! c_Value ppf p x =
              let open FCPM in
              parse
                (conde
                   [ psymb (pv __) |> map1 ~f:(fun s -> `Atom s)
                   ; plambda __ __ |> map2 ~f:(fun arg body -> `Lambda (arg, body))
                   ; pseq (manyl __) |> map1 ~f:(fun xs -> `GSeq xs)
                   ; pseq __ |> map1 ~f:(fun ls -> `Seq ls)
                   ; psymb __ |> map1 ~f:(fun s -> `Any_sym s)
                   ; __ |> map1 ~f:(fun ls -> `Any ls)
                   ])
                ()
                ~on_error:(fun _ ->
                  Format.fprintf ppf "FUCK%!";
                  super#c_Value ppf p x)
                p
                (let open Format in
                 function
                 | `Atom s -> Format.fprintf ppf "%s" s
                 | `Lambda (arg, body) ->
                   Format.fprintf ppf "(lambda (%a) %a)" fself arg fself body
                 | `GSeq [] -> Format.fprintf ppf "()"
                 | `GSeq (h :: tl) ->
                   Format.fprintf ppf "(%a" fself h;
                   List.iter (fprintf ppf " %a" fself) tl;
                   fprintf ppf ")"
                 | `Seq xs -> GT.fmt ListLo.logic fself ppf xs
                 | `Any_sym (Var (idx, _)) -> Format.fprintf ppf "_.%d" idx
                 | `Any_sym (s : StringLo.logic) ->
                   fprintf ppf "Any %a" (GT.fmt StringLo.logic) s
                 | `Any _ -> super#c_Value ppf p x)

            method! c_Var ppf _ idx _ = Format.fprintf ppf "_.%d" idx
          end)
        ppf
    in
    { logic with
      plugins =
        object
          method gmap = logic.plugins#gmap
          method fmt = pp
        end
    }
  ;;

  let pp_as_ocanren ppf =
    GT.transform_gc
      gcata_logic
      (fun fself ->
        object
          inherit [_] fmt_logic_t fself as super

          method! c_Value ppf p x =
            let open FCPM in
            parse
              (conde
                 [ psymb (pv __) |> map1 ~f:(fun s -> `Atom s)
                 ; plambda __ __ |> map2 ~f:(fun arg body -> `Lambda (arg, body))
                 ; pseq (manyl __) |> map1 ~f:(fun xs -> `GSeq xs)
                 ; pseq __ |> map1 ~f:(fun ls -> `Seq ls)
                 ; psymb __ |> map1 ~f:(fun s -> `Any_sym s)
                 ; __ |> map1 ~f:(fun ls -> `Any ls)
                 ])
              ()
              ~on_error:(fun _ ->
                Format.fprintf ppf "FUCK%!";
                super#c_Value ppf p x)
              p
              (let open Format in
               function
               | `Atom s -> Format.fprintf ppf "%s" s
               | `Lambda (arg, body) ->
                 Format.fprintf ppf "(lambda (%a) %a)" fself arg fself body
               | `GSeq [] -> Format.fprintf ppf "()"
               | `GSeq (h :: tl) ->
                 Format.fprintf ppf "(%a" fself h;
                 List.iter (fprintf ppf " %a" fself) tl;
                 fprintf ppf ")"
               | `Seq xs -> GT.fmt ListLo.logic fself ppf xs
               | `Any_sym (Var (idx, _)) -> Format.fprintf ppf "_.%d" idx
               | `Any_sym (s : StringLo.logic) ->
                 fprintf ppf "Any %a" (GT.fmt StringLo.logic) s
               | `Any _ -> super#c_Value ppf p x)

          method! c_Var ppf _ idx _ = Format.fprintf ppf "_.%d" idx
        end)
      ppf
  ;;

  type injected = (GT.string OCanren.ilogic, injected Std.List.groundi) t ilogic

  let show_rterm = Format.asprintf "%a" (GT.fmt ground)
  let show_lterm = Format.asprintf "%a" (GT.fmt logic)

  (** Contructors *)

  let list : injected list -> injected =
   fun xs -> seq (Std.list Fun.id (symb !!"list" :: xs))
  ;;

  let app : injected -> injected -> injected = fun f x -> seq (Std.list Fun.id [ f; x ])
  let quote x = app (symb !!"quote") x
  let seq_ xs : injected = seq (Std.list Fun.id xs)
end

module Gresult = struct
  [%%distrib
  type nonrec ('var, 't, 'xs) t =
    | Closure of 'var * 't * 'xs
    | Val_ of 't
  [@@deriving gt ~options:{ fmt; gmap }]

  type ground =
    ( StringLo.ground
      , Gterm.ground
      , (StringLo.ground, ground) Std.Pair.ground Std.List.ground )
      t]

  let show_string = GT.(show string)
  let show_stringl = GT.(show OCanren.logic) show_string
  let show_rresult r = Format.asprintf "%a" (GT.fmt ground) r
  let show_lresult (r : logic) = Format.asprintf "%a" (GT.fmt logic) r
end

let gresult_reifier = Gresult.reify

module Env = struct
  type logic = (GT.string OCanren.logic, Gresult.logic) Std.Pair.logic Std.List.logic
  [@@deriving gt ~options:{ fmt }]

  type injected =
    (string OCanren.ilogic, Gresult.injected) Std.Pair.injected Std.List.injected

  let reify : (_, logic) Reifier.t =
    Std.List.reify (Std.Pair.reify OCanren.reify gresult_reifier)
  ;;

  let empty : injected = Std.List.nil ()
end

type fenv = Env.injected
