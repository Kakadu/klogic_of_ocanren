type ('inh, 'b, 'syn) action = 'inh -> 'b -> 'syn

open Typedtree

type ('inh, 'syn) t =
  { expr : ('inh, 'syn) t -> ('inh, Typedtree.expression, 'syn) action
  ; stru_item : ('inh, 'syn) t -> ('inh, Typedtree.structure_item, 'syn) action
  ; stru : ('inh, 'syn) t -> ('inh, Typedtree.structure, 'syn) action
  ; value_binding : ('inh, 'syn) t -> ('inh, Typedtree.value_binding, 'syn) action
  }

let default (type a b) ?(join_syn = Fun.id) : (a, b) t =
  { expr =
      (fun self inh e ->
        match e.exp_desc with
        | Texp_apply (f, args) ->
          let syn = self.expr self inh f in
          let syn =
            List.fold_left_map
              (fun acc (lab, arg) ->
                match arg with
                | None -> acc
                | Some arg ->
                  let syn = self.expr self acc arg in
                  join_syn acc syn)
              syn
              args
          in
          syn, { e with exp_desc = Texp_apply (f, args) }
        | _ -> assert false)
  ; stru =
      (fun self acc s ->
        assert false
        (* let acc, str_items = List.fold_left_map (self.stru_item self) acc s.str_items in
        acc, { s with str_items } *))
  ; stru_item =
      (fun self acc s ->
        match s.str_desc with
        | Tstr_value (rec_flag, vbs) ->
          let acc, vbs = List.fold_left_map (self.value_binding self) acc vbs in
          acc, { s with str_desc = Tstr_value (rec_flag, vbs) }
        | _ -> acc, s)
  ; value_binding =
      (fun self acc vb ->
        let acc, vb_expr = self.expr self acc vb.vb_expr in
        acc, { vb with vb_expr })
  }
;;
