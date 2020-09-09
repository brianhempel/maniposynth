open Ocamlformat_lib.Migrate_ast.Parsetree

type t =
  | Constant of constant
  | Unknown
  | Bindings_rets of expression * binding_skel list * t list (* exp is the scope, the outermost expression (usually a let) *)
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | Apply of expression * (Asttypes.arg_label * t) list (* can have 0 arguments, e.g. bare variable usage (var does not have have function type) *)
  | Construct of Longident.t * t option
and binding_skel = value_binding * t

(* for debugging *)
let rec show = function
  | Constant constant -> "Constant " ^ Show_ast.constant constant
  | Unknown           -> "Unknown"
  | Fun (arg_label, default_opt, pat, body_skel)  ->
    let dummy_fun = { Show_ast.dummy_exp with pexp_desc = Pexp_fun (arg_label, default_opt, pat, Show_ast.dummy_exp) } in
    Show_ast.exp dummy_fun ^ show body_skel
  | Apply (_, _) -> "app lololol"
  | Construct (_, _) -> "construct lololol"
  | Bindings_rets (_, bindings_skels, ret_skels) ->
    let binding_strs = List.map show_binding bindings_skels in
    "let " ^ String.concat " and " binding_strs ^ " in (" ^ String.concat " | " (List.map show ret_skels) ^  ")"
and
  show_binding ({ pvb_pat = pat; _ }, skel) = Show_ast.pat pat ^ " = " ^ show skel


let rec skel_of_exp ({ pexp_desc = exp_desc; _ } as exp) =
  let ensure_bindings_rets scope_exp  = function
    | (Bindings_rets _) as skel -> skel
    | other_skel -> Bindings_rets (scope_exp, [], [other_skel])
  in
  let append_bindings_rets scope_exp l_skel r_skel =
    match (ensure_bindings_rets scope_exp l_skel, ensure_bindings_rets scope_exp r_skel) with
    | ( Bindings_rets (_, l_bindings_skels, l_rets)
      , Bindings_rets (_, r_bindings_skels, r_rets)
      ) -> Bindings_rets (scope_exp, l_bindings_skels @ r_bindings_skels, l_rets @ r_rets)
    | _ -> failwith "impossible: ensure_bindings_rets ensures the skeleton is a bindings_rets"
  in
  match exp_desc with
  | Pexp_ident _ -> Apply (exp, [])
  | Pexp_constant constant -> Constant constant
  | Pexp_let (_rec_flag, value_bindings, body_exp) ->
      let bindings_skels = List.map (fun vb -> (vb, skeleton_of_value_binding vb)) value_bindings in
      (* flatten multiple lets together *)
      (match skel_of_exp body_exp with
      | Bindings_rets (_, deeper_bindings_skels, rets) -> 
          Bindings_rets (exp, bindings_skels @ deeper_bindings_skels, rets)
      | body_skel -> Bindings_rets (exp, bindings_skels, [body_skel])
      )
  | Pexp_fun (arg_label, default_opt, pat, body_exp) ->
      (* ensure function body is a Bindings_rets, so there's a blank space in the interface for the user to add bindings *)
      (match skel_of_exp body_exp with
      | Fun _ as body_skel ->
          Fun (arg_label, default_opt, pat, body_skel)
      | body_skel ->
          Fun (arg_label, default_opt, pat, ensure_bindings_rets body_exp body_skel)
      )
  | Pexp_apply (fun_exp, arg_labels_exps) ->
      let arg_labels_skels = List.map (fun (l, e) -> (l, skel_of_exp e)) arg_labels_exps in
      Apply (fun_exp, arg_labels_skels)
  | Pexp_match (_scrutinee_exp, cases) ->
    let branch_skels =
      List.map (fun case -> skel_of_exp case.pc_rhs) cases
    in
    (match branch_skels with
    | first::rest -> List.fold_left (append_bindings_rets exp) first rest
    | []          -> failwith "impossible: match statement should have at least one branch"
    )
  | Pexp_construct (ident_located, exp_opt) ->
    Construct (ident_located.txt, Option.map skel_of_exp exp_opt)
  | _ -> Unknown
and skeleton_of_value_binding { pvb_pat = _; pvb_expr = exp; _ } = skel_of_exp exp

let bindings_skels_of_structure_item ({pstr_desc=structure_item_desc; _} : structure_item) : binding_skel list =
  match structure_item_desc with
  | Pstr_value (_, value_bindings) ->
      List.map (fun vb -> (vb, skeleton_of_value_binding vb)) value_bindings
  | _ -> []

let bindings_skels_of_toplevel_phrase (phrase : toplevel_phrase) : binding_skel list =
  match phrase with
  | Ptop_def structure_items -> List.concat_map bindings_skels_of_structure_item structure_items
  | Ptop_dir _               -> []

type phrases = toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

let bindings_skels_of_parsed_with_comments ({ ast = toplevel_phrases; _ } : phrases) : binding_skel list = 
  List.concat_map bindings_skels_of_toplevel_phrase toplevel_phrases
