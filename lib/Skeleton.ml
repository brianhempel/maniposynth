open Ocamlformat_lib.Migrate_ast.Parsetree

let unknown_pat : pattern =
  { ppat_desc       = Ppat_var (Location.mknoloc "?")
  ; ppat_loc        = Location.none
  ; ppat_loc_stack  = []
  ; ppat_attributes = []
  }

type t =
  | Constant of constant
  | Unknown
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | App of t * (Asttypes.arg_label * expression option * pattern) * (Asttypes.arg_label * expression * t) * t

let rec show = function
  | Constant constant -> "Constant " ^ Show_ast.constant constant
  | Unknown           -> "Unknown"
  | Let (bindings_skels, body_skel) ->
    let binding_strs = List.map show_binding bindings_skels in
    "let " ^ String.concat " and " binding_strs ^ " in (" ^ show body_skel ^  ")"
  | Fun (arg_label, default_opt, pat, body_skel)  ->
    let dummy_fun = { Show_ast.dummy_exp with pexp_desc = Pexp_fun (arg_label, default_opt, pat, Show_ast.dummy_exp) } in
    Show_ast.exp dummy_fun ^ show body_skel
  | App (_f_skel, _, (_, _, _arg_skel), _ret_skel) -> "app lololol"
and
  show_binding ({ pvb_pat = pat; _ }, skel) = Show_ast.pat pat ^ " = " ^ show skel

type env = (string * (valu * t)) list
and valu =
  | VUnknown
  | VClosure of env * pattern * expression
  | VConstant of constant

let string_of_longident (longident : Longident.t) =
  String.concat "." (Longident.flatten longident)

(* Reduces each skeleton down to its return value. Preserves closure structure but nothing else. *)
let rec ret_skel skel =
  match skel with
  | Constant _ -> skel
  | Unknown    -> skel
  | Let (_, body_skel) ->
      ret_skel body_skel
  | Fun (arg_label, default_opt, pat, body_skel) ->
      Fun (arg_label, default_opt, pat, ret_skel body_skel) 
  | App (_, _, _, result_skel) ->
      ret_skel result_skel

(* TODO: handle recursion for let+fun *)
let rec static_analyze_expression_to_skeleton (env : env) ({ pexp_desc = exp_desc; _ } as exp) =
  let ret_unknown = (VUnknown, Unknown) in
  match exp_desc with
  | Pexp_ident { txt = longident; _ } -> begin
      (match List.assoc_opt (string_of_longident longident) env with
      | Some (valu, skel) -> (valu, skel)
      | None              -> ret_unknown
      )
    end
  | Pexp_constant constant -> (VConstant constant, Constant constant)
  | Pexp_let (_, [{ pvb_pat = { ppat_desc = (Ppat_var { txt = var_str; _ }); _ }; pvb_expr = bound_exp; _ } as value_binding], body_exp) ->
    let (bound_val, bound_skel) = static_analyze_expression_to_skeleton env bound_exp in
    let env = (var_str, (bound_val, ret_skel bound_skel))::env in
    let (ret_val, body_skel) = static_analyze_expression_to_skeleton env body_exp in
    ( ret_val
    , Let ([(value_binding, bound_skel)], body_skel)
    )
  | Pexp_let (_, _, _) -> ret_unknown
  | Pexp_function _ -> ret_unknown
  | Pexp_fun (arg_label, default_opt, ({ ppat_desc = (Ppat_var { txt = var_str; _ }); _ } as pat), body_exp) ->
    let fun_env = (var_str, ret_unknown)::env in
    let (_, body_skel) = static_analyze_expression_to_skeleton fun_env body_exp in
    ( VClosure (env, pat, body_exp)
    , Fun (arg_label, default_opt, pat, body_skel)
    )
  | Pexp_fun (_, _, _, _) -> ret_unknown
  | Pexp_apply (fun_exp, [(arg_label, arg_exp)]) ->
    let (_fun_val, fun_skel) = static_analyze_expression_to_skeleton env fun_exp in
    let (_arg_val, arg_skel) = static_analyze_expression_to_skeleton env arg_exp in
    (match ret_skel fun_skel with
    | Fun (fun_arg_label, default_opt, pat, body_skel) ->
      ( VUnknown
      , App (fun_skel, (fun_arg_label, default_opt, pat), (arg_label, arg_exp, arg_skel), body_skel)
      ) 
    | Constant _ | Unknown -> 
      ( VUnknown
      , App (fun_skel, (Nolabel, None, unknown_pat), (arg_label, arg_exp, arg_skel), Unknown)
      ) 
    | Let _ | App _ -> failwith "impossible"
    )
  | Pexp_apply (fun_exp, arg1::other_args) ->
    let fun_exp_applied_once = { exp with pexp_desc =  Pexp_apply (fun_exp, [arg1]) } in
    let expanded_fun_exp = { exp with pexp_desc =  Pexp_apply (fun_exp_applied_once, other_args) } in
    static_analyze_expression_to_skeleton env expanded_fun_exp
  | Pexp_apply (_fun_exp, []) -> ret_unknown
  | _ -> ret_unknown
  (* | Pexp_match (_, _) -> (??)
  | Pexp_try (_, _) -> (??)
  | Pexp_tuple _ -> (??)
  | Pexp_construct (_, _) -> (??)
  | Pexp_variant (_, _) -> (??)
  | Pexp_record (_, _) -> (??)
  | Pexp_field (_, _) -> (??)
  | Pexp_setfield (_, _, _) -> (??)
  | Pexp_array _ -> (??)
  | Pexp_ifthenelse (_, _, _) -> (??)
  | Pexp_sequence (_, _) -> (??)
  | Pexp_while (_, _) -> (??)
  | Pexp_for (_, _, _, _, _) -> (??)
  | Pexp_constraint (_, _) -> (??)
  | Pexp_coerce (_, _, _) -> (??)
  | Pexp_send (_, _) -> (??)
  | Pexp_new _ -> (??)
  | Pexp_setinstvar (_, _) -> (??)
  | Pexp_override _ -> (??)
  | Pexp_letmodule (_, _, _) -> (??)
  | Pexp_letexception (_, _) -> (??)
  | Pexp_assert _ -> (??)
  | Pexp_lazy _ -> (??)
  | Pexp_poly (_, _) -> (??)
  | Pexp_object _ -> (??)
  | Pexp_newtype (_, _) -> (??)
  | Pexp_pack _ -> (??)
  | Pexp_open (_, _) -> (??)
  | Pexp_letop _ -> (??)
  | Pexp_extension _ -> (??)
  | Pexp_unreachable -> (??) *)

let skeleton_of_expression exp =
  let (_, skel) = static_analyze_expression_to_skeleton [] exp in
  skel
  
let skeleton_of_value_binding { pvb_pat = _; pvb_expr = exp; _ } = skeleton_of_expression exp

let skeleton_of_structure_item ({pstr_desc=structure_item_desc; _} : structure_item) =
  match structure_item_desc with
  | Pstr_value (_, value_bindings) -> List.map skeleton_of_value_binding value_bindings
  | _ -> []

let skeleton_of_toplevel_phrase (phrase : toplevel_phrase) =
  match phrase with
  | Ptop_def structure_items -> List.concat_map skeleton_of_structure_item structure_items
  | Ptop_dir _               -> []

type phrases = toplevel_phrase list Ocamlformat_lib.Parse_with_comments.with_comments

let skeletons_of_parsed_with_comments ({ast=toplevel_phrases; _} : phrases) = 
  List.concat_map skeleton_of_toplevel_phrase toplevel_phrases
(* let parsed_with_comments_to_skeletons _ = [Unknown] *)

(* let exp_to_skeleton _ = Unknown *)
