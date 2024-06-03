let has_attr name xs =
  try
    let _ =
      List.find
        (function
           | { Parsetree.attr_name = { txt }; _ } -> String.equal txt name)
        xs
    in
    true
  with
  | Not_found -> false
;;

type ('inh, 'b, 'syn) action = 'inh -> 'b -> 'syn * 'b

open Typedtree

type ('inh, 'syn) t =
  { expr : ('inh, 'syn) t -> ('inh, Typedtree.expression, 'syn) action
  ; stru_item : ('inh, 'syn) t -> ('inh, Typedtree.structure_item, 'syn) action
  ; stru : ('inh, 'syn) t -> ('inh, Typedtree.structure, 'syn) action
  ; value_binding : ('inh, 'syn) t -> ('inh, Typedtree.value_binding, 'syn) action
  }

let default (type inh syn) : (inh, syn) t =
  { expr =
      (fun self inh e ->
        match e.exp_desc with
        | Texp_apply (f, args) ->
          let syn, f = self.expr self inh f in
          let args =
            List.map
              (fun (lab, arg) ->
                match arg with
                | None -> lab, None
                | Some arg -> lab, Some (snd (self.expr self inh arg)))
              args
          in
          syn, { e with exp_desc = Texp_apply (f, args) }
        | _ ->
          Printf.ksprintf
            failwith
            "Not implemented in 'folder.expr':\n"
            MyPrinttyped.expr
            e)
  ; stru =
      (fun self inh s ->
        match s.str_items with
        | [] ->
          Format.kasprintf failwith "Not implemented in 'folder.stru': empty structure\n"
        | h :: tl ->
          let syn, h = self.stru_item self inh h in
          let tl = List.map (fun si -> snd @@ self.stru_item self inh si) tl in
          syn, { s with str_items = h :: tl }
        (* Format.eprintf
          "%a\n%!"
          Pprintast.structure_item
          (List.hd @@ MyUntype.untype_structure s);
        Format.kasprintf failwith "Not implemented in 'folder.stru':\n" *)
        (* let acc, str_items = List.fold_left_map (self.stru_item self) acc s.str_items in
        acc, { s with str_items } *))
  ; stru_item =
      (fun self inh s ->
        match s.str_desc with
        (* | Tstr_module { mb_attributes = attrs } when has_attr "skip_from_klogic" attrs ->
          inh, s *)
        | Tstr_value (_, []) -> assert false
        | Tstr_value (rec_flag, vbh :: vbtl) ->
          let syn, vbh = self.value_binding self inh vbh in
          let vbtl = List.map (fun vb -> snd @@ self.value_binding self inh vb) vbtl in
          syn, { s with str_desc = Tstr_value (rec_flag, vbh :: vbtl) }
        | _ ->
          Format.eprintf "%a\n%!" Pprintast.structure_item (MyUntype.untype_stru_item s);
          Printf.ksprintf failwith "Not implemented in 'folder' (%s %d)" __FILE__ __LINE__)
  ; value_binding =
      (fun self acc vb ->
        let acc, vb_expr = self.expr self acc vb.vb_expr in
        acc, { vb with vb_expr })
  }
;;
