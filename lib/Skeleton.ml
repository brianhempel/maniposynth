open Ocamlformat_lib.Migrate_ast.Parsetree

type t =
  | Top_binding of value_binding * t
  | Constant of constant
  | Unknown
  | Labeled of expression (* var *)
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | Apply of expression * (Asttypes.arg_label * t) list
  | Construct of Longident.t * t option
  | Skels of t list

(* for debugging *)
let rec show = function
  | Top_binding (vb, skel) -> show_binding (vb, skel)
  | Constant constant -> "Constant " ^ Show_ast.constant constant
  | Unknown           -> "Unknown"
  | Labeled exp       -> "Labeled(" ^ Show_ast.exp exp ^ ")"
  | Let (bindings_skels, body_skel) ->
    let binding_strs = List.map show_binding bindings_skels in
    "let " ^ String.concat " and " binding_strs ^ " in (" ^ show body_skel ^  ")"
  | Fun (arg_label, default_opt, pat, body_skel)  ->
    let dummy_fun = { Show_ast.dummy_exp with pexp_desc = Pexp_fun (arg_label, default_opt, pat, Show_ast.dummy_exp) } in
    Show_ast.exp dummy_fun ^ show body_skel
  | Apply (_, _) -> "app lololol"
  | Construct (_, _) -> "construct lololol"
  | Skels skels -> String.concat "&" (List.map show skels)
and
  show_binding ({ pvb_pat = pat; _ }, skel) = Show_ast.pat pat ^ " = " ^ show skel


let rec skeleton_of_expression ({ pexp_desc = exp_desc; _ } as exp) =
  match exp_desc with
  | Pexp_ident _ -> Labeled exp
  | Pexp_constant constant -> Constant constant
  | Pexp_let (_rec_flag, value_bindings, body_exp) ->
      let bindings_skeletons = List.map (fun vb -> (vb, skeleton_of_value_binding vb)) value_bindings in
      Let (bindings_skeletons, skeleton_of_expression body_exp)
  | Pexp_fun (arg_label, default_opt, pat, body_exp) ->
      Fun (arg_label, default_opt, pat, skeleton_of_expression body_exp)
  | Pexp_apply (fun_exp, arg_labels_exps) ->
    let arg_labels_skels = List.map (fun (l, e) -> (l, skeleton_of_expression e)) arg_labels_exps in
    Apply (fun_exp, arg_labels_skels)
  | Pexp_match (_scrutinee_exp, cases) ->
    let branch_skels =
      List.map (fun case -> skeleton_of_expression case.pc_rhs) cases
    in
    Skels branch_skels
  | Pexp_construct (ident_located, exp_opt) ->
    Construct (ident_located.txt, Option.map skeleton_of_expression exp_opt)
  | _ -> Unknown
and skeleton_of_value_binding { pvb_pat = _; pvb_expr = exp; _ } = skeleton_of_expression exp

let skeletons_of_structure_item ({pstr_desc=structure_item_desc; _} : structure_item) =
  match structure_item_desc with
  | Pstr_value (_, value_bindings) ->
      List.map (fun vb -> Top_binding (vb, skeleton_of_value_binding vb)) value_bindings
  | _ -> []

let skeletons_of_toplevel_phrase (phrase : toplevel_phrase) =
  match phrase with
  | Ptop_def structure_items -> List.concat_map skeletons_of_structure_item structure_items
  | Ptop_dir _               -> []

type phrases = toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

let skeletons_of_parsed_with_comments ({ ast = toplevel_phrases; _ } : phrases) : t list = 
  List.concat_map skeletons_of_toplevel_phrase toplevel_phrases
