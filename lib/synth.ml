open Camlboot_interpreter
open Camlboot_interpreter.Data
open Parsetree
open Shared
open Shared.Ast
open Shared.Util

open Stats_model


(* Next things to do to make fast:
  - type var unification with in a filling...so it doesn't compare a list to a number
  - when a hole has type 'a, don't try items with a more specific static type
  - try using assert information to speculate types on holes, from specific to general (e.g. if assert result is (int list), try (int list), ('a list), and 'a)
*)

let terms_tested_count = ref 0
let timeout_secs       = 10.0

type fillings = expression Loc_map.t

(* Apply until fixpoint. *)
let rec apply_fillings fillings prog =
  let changed = ref false in
  let prog' =
    Loc_map.bindings fillings
    |> List.fold_left begin fun prog (loc, exp) ->
      Exp.map_by_loc loc (fun _ -> changed := true; exp) prog
    end prog
  in
  if !changed
  then apply_fillings fillings prog'
  else prog'

let rec apply_fillings_to_exp fillings root_exp =
  let changed = ref false in
  let root_exp' =
    Loc_map.bindings fillings
    |> List.fold_left begin fun root_exp (loc, e') ->
      root_exp
      |> Exp.FromNode.map begin fun e ->
        if e.pexp_loc = loc then
          (changed := true; e')
        else e
      end
    end root_exp
  in
  if !changed
  then apply_fillings_to_exp fillings root_exp'
  else root_exp'


(* Constraints/examples. But "constraint" is an OCaml keyword, so let's call them "req"s *)
type req = Data.env * expression * value

let string_of_req (_env, exp, value) =
  Exp.to_string exp ^ " = " ^ value_to_string value


let dont_care = new_vtrace ExDontCare

let eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no exp =
  Eval.with_fuel 300 begin fun () ->
    try Eval.eval_expr fillings prims env lookup_exp_typed trace_state frame_no exp
    with _ -> new_vtrace Bomb
  end (fun () -> new_vtrace Bomb)

let pattern_bind_fueled fillings prims env lookup_exp_typed trace_state frame_no root_v path p v =
  Eval.with_fuel 50 begin fun () ->
    Eval.pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_v path p v
  end (fun () -> raise Eval.Match_fail)

let eval_module_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no mod_exp =
  Eval.with_fuel 300 begin fun () ->
    Some (Eval.eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no mod_exp)
  end (fun () -> None)

let eval trace_state fillings env exp =
  eval_exp_fueled fillings Primitives.prims env (fun _ -> None) trace_state (-1) exp

let rec try_cases fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val cases =
  let open Eval in
  match cases with (* still not handling cases that mix regular ctors and exception ctors (pattern_bind_checkexn) *)
  | [] -> None
  | case:: rest -> begin try
      let env' = pattern_bind_fueled fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val [] case.pc_lhs scrutinee_val in
      begin match case.pc_guard with
      | None -> ()
      | Some guard when is_true (eval_exp_fueled fillings prims env' lookup_exp_typed trace_state frame_no guard) -> ()
      | _ -> raise Match_fail
      end;
      Some (env', case.pc_rhs)
    with Match_fail -> try_cases fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val rest
    end

(* Fillings might only be used in pat "with" clauses here *)
let req_of_assert_result (assert_result : assert_result) : req =
  (assert_result.env, assert_result.lhs_exp, assert_result.expected)

(*
  If I know that name should have value, and pat looks
  like e.g. (x, name, y), then value is expanded to
  (ExDontCare, value, ExDontCare) so the example can be pushed down the
  binding that corresponds to pat
*)
(* Need env to look up constructor numbers :/ *)
let rec expand_named_example_to_pat env name (value : value) pat : value =
  let recurse = expand_named_example_to_pat env name value in
  match pat.ppat_desc with
  | Ppat_any                                                   -> dont_care
  | Ppat_var { txt = pat_name; _ } when pat_name = name        -> value
  | Ppat_var _                                                 -> dont_care
  | Ppat_alias (_, { txt = pat_name; _ }) when pat_name = name -> value
  | Ppat_alias (p', _)                                         -> recurse p'
  | Ppat_constant _                                            -> dont_care
  | Ppat_interval (_, _)                                       -> dont_care
  | Ppat_tuple ps                                              -> new_vtrace @@ Tuple (ps |>@ recurse)
  | Ppat_construct (_, None)                                   -> dont_care
  | Ppat_construct (lid_loced, Some p')                        -> new_vtrace @@ Constructor (Eval.lident_name lid_loced.txt, Envir.env_get_constr env lid_loced, Some (recurse p'))
  | Ppat_variant (_, _)                                        -> dont_care
  | Ppat_record (fieldpats, _closedflag) ->
    (* Records as examples are open, I guess. closedflag is unhandled. *)
    let ex_fields =
      fieldpats
      |>@ begin fun (lid_loced, fieldpat) -> (Eval.lident_name lid_loced.txt, ref @@ recurse fieldpat) end
      |> SMap.of_list
    in
    new_vtrace @@ Record ex_fields
  | Ppat_array ps                                              -> new_vtrace @@ Array (ps |>@ recurse |> Array.of_list)
  | Ppat_or (p1, p2) ->
    begin match recurse p1 with
    | { v_ = ExDontCare; _ } -> recurse p2
    | ex                     -> ex
    end
  | Ppat_constraint (p', _)                                    -> recurse p'
  | Ppat_type _                                                -> dont_care
  | Ppat_lazy _                                                -> dont_care
  | Ppat_unpack _                                              -> dont_care
  | Ppat_exception _                                           -> dont_care
  | Ppat_extension _                                           -> dont_care
  | Ppat_open (_, p')                                          -> recurse p'



(* Attempt to push the req down to a req(s) on a hole. *)
(* Modification of Camlboot_interpreter.eval *)
(* Because we are not unevaluating yet, not guarenteed to succeed even where we might want it to. *)
let rec push_down_req_ fillings lookup_exp_typed hit_a_function_f ((env, exp, value) as req) : req list =
  let open Eval in
  decr fuel;
  if !fuel <= 0 then raise No_fuel;
  (* print_endline @@ "Pushing down " ^ string_of_req req; *)
  let recurse = push_down_req_ fillings lookup_exp_typed hit_a_function_f in
  let prims, trace_state, frame_no = Primitives.prims, (Trace.new_trace_state ()), -1 in
  let try_cases = try_cases fillings prims env lookup_exp_typed trace_state frame_no in
  (* let perhaps_add_type_opt v =
    if v.type_opt = None then
      match Eval.lookup_type_opt lookup_exp_typed exp.pexp_loc with
      | Some typ when not (Shared.Ast.Type.is_var_type typ) -> add_type_opt (Some typ) v
      | _                                                   -> v
    else
      v
  in *)
  match exp.pexp_desc with
  | Pexp_ident { txt = Longident.Lident "??"; _ } ->
    begin match Loc_map.find_opt exp.pexp_loc fillings with
    | Some filling_exp -> recurse (env, filling_exp, value)
    | None -> [req]
    end
  | Pexp_let (recflag, vbs, e) ->
    let env' = eval_bindings fillings prims env lookup_exp_typed trace_state frame_no recflag vbs in
    let deeper_hole_reqs = recurse (env', e, value) in
    (* If a deeper req constrains a name defined here, transfer that constraint to the bound expression. *)
    deeper_hole_reqs
    |>@@ begin fun ((_, exp, value) as req) ->
      match Exp.ident_lid exp with
      | Some (Longident.Lident name) ->
        begin match vbs |>@? (Vb.names %> List.mem name) with
        | [vb] when Exp.flatten e |> List.exists (Exp.loc %> (=) exp.pexp_loc) -> (* Ensure it's actually an ident inside the body (i.e. we didn't jump out to some function lambda or something) *)
          let req_env = if recflag = Asttypes.Recursive then env' else env in
          let new_ex = expand_named_example_to_pat req_env name value vb.pvb_pat in
          recurse (req_env, vb.pvb_expr, new_ex)
        | _ -> [req]
        end
      | _ -> [req]
    end
  | Pexp_constant _ -> [req]
  | Pexp_ident lid_loced ->
    (* If ident refers to something that carries an env (a func or a holeval) then push the req into that *)
    begin match Envir.env_get_value_or_lvar env lid_loced with
      | Value { v_ = Hole (env_ref, _, e); _ } ->
        recurse (!env_ref, e, value)
      | Value { v_ = Fun (Asttypes.Nolabel, None, pat, body_exp, env_ref); _ } ->
        recurse (!env_ref, Exp.fun_ Nolabel None pat body_exp, value)
      | Value { v_ = Function (cases, env_ref); _ } ->
        recurse (!env_ref, Exp.function_ cases, value)
      | Value _ -> [req]
      | Instance_variable _ -> [req]
      | exception Not_found -> [req]
    end
  | Pexp_function cases ->
    begin match value.v_ with
    | ExCall (arg, expected) ->
      begin match try_cases arg cases with
      | None -> [req]
      | Some (env', branch_exp) -> recurse (env', branch_exp, expected)
      end
    | _ ->
      [req]
    end
  | Pexp_fun (Nolabel, None, arg_pat, body_exp) ->
    begin match value.v_ with
    | ExCall (arg, expected) -> begin try
        let env' = pattern_bind_fueled fillings prims env lookup_exp_typed trace_state frame_no arg [] arg_pat arg in
        hit_a_function_f arg_pat body_exp arg expected;
        recurse (env', body_exp, expected)
      with Match_fail -> [req]
      end
    | _ -> [req]
    end
  | Pexp_fun (_, _, _, _) -> [req]
  | Pexp_apply (fexp, labeled_args) ->
    if List.for_all (fun (label, _) -> label == Asttypes.Nolabel) labeled_args then
      let arg_vals = List.map (fun (_, e) -> eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no e) labeled_args in
      (* Expand example to arg1 -> arg2 -> ex *)
      let expanded_example = List.fold_right (fun arg ex -> new_vtrace @@ ExCall (arg, ex)) arg_vals value in
      (* Push it down the function expression *)
      recurse (env, fexp, expanded_example)
    else
      [req]
  | Pexp_tuple exps ->
    begin match value.v_ with
    | Tuple vs when List.length vs = List.length exps ->
      List.map2 (fun e v -> recurse (env, e, v)) exps vs
      |> List.concat
    | _ -> [req]
    end
  | Pexp_match (e, cases) ->
    let arg = eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no e in
    begin match try_cases arg cases with
    | None -> [req]
    | Some (env', branch_exp) -> recurse (env', branch_exp, value)
    end
  | Pexp_coerce (e, _, _)  -> recurse (env, e, value)
  | Pexp_constraint (e, _) -> recurse (env, e, value)
  | Pexp_sequence (e1, e2) ->
    let _ = eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no e1 in (* Do we even need to do this? *)
    recurse (env, e2, value)
  | Pexp_while (_, _) -> [req]
  | Pexp_for (_, _, _, _, _) -> [req]
  | Pexp_ifthenelse (e1, e2, e3_opt) ->
    let guard_val = eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no e1 in
    begin try if is_true guard_val
    then recurse (env, e2, value)
    else (
      match e3_opt with
      | None -> [req]
      | Some e3 -> recurse (env, e3, value))
    with BombExn -> [req]
    end
  | Pexp_unreachable -> failwith "reached unreachable"
  | Pexp_try (e, cases) ->
    begin try recurse (env, e, value)
    with InternalException exn_val ->
      begin match try_cases exn_val cases with
      | None -> raise (InternalException exn_val)
      | Some (env', branch_exp) -> recurse (env', branch_exp, value)
      end
    end
  | Pexp_construct (_, None) -> [req]
  | Pexp_construct (lid_loced, Some e) ->
    let ctor_name = lident_name lid_loced.txt in
    let d = Envir.env_get_constr env lid_loced in
    begin match value.v_ with
    | Constructor (ex_ctor_name, d_ex, Some ex) when ex_ctor_name = ctor_name && d_ex = d ->
      recurse (env, e, ex)
    | _ -> [req]
    end
  | Pexp_variant (_, None) -> [req]
  | Pexp_variant (cn, Some e) ->
    let hash = Hashtbl.hash cn in
    begin match value.v_ with
    | Constructor (ex_ctor_name, d_ex, Some ex) when ex_ctor_name = cn && d_ex = hash ->
      recurse (env, e, ex)
    | _ -> [req]
    end
  | Pexp_record (fields, e_opt) ->
    begin match value.v_ with
    | Record ex_fields ->
      let literal_field_names = fields |>@ fst |>@ Loc.txt |>@ lident_name in
      let expected_labels = SMap.bindings ex_fields |>@ fst in
      let expected_labels_not_in_literal =
        expected_labels |>@? (fun name -> not (List.mem name literal_field_names)) in
      begin match e_opt, expected_labels_not_in_literal with
      | _, [] ->
        SMap.bindings ex_fields
        |>@@ begin fun (ex_label, expected_ref) ->
          let _, field_exp = fields |> List.find (fst %> Loc.txt %> lident_name %> (=) ex_label) in
          recurse (env, field_exp, !expected_ref)
        end
      | Some base_rec_exp, _ ->
        (* Labels not in literal are pushed to base_rec, others to the fields *)
        let base_ex = new_vtrace @@
          Record (SMap.filter (fun name _ -> List.mem name expected_labels_not_in_literal) ex_fields) in
        let lit_push_downs =
          SMap.bindings ex_fields
          |>@? (fun (name, _) -> List.mem name literal_field_names)
          |>@@ begin fun (ex_label, expected_ref) ->
            let _, field_exp = fields |> List.find (fst %> Loc.txt %> lident_name %> (=) ex_label) in
            recurse (env, field_exp, !expected_ref)
          end in
        let base_rec_push_downs =
          recurse (env, base_rec_exp, base_ex) in
          lit_push_downs @ base_rec_push_downs
      | _ -> [req]
      end
    | _ -> [req]
    end
  | Pexp_field (e, { txt = lident; _ }) ->
    let label = lident_name lident in
    let record_ex = new_vtrace @@ Record (SMap.singleton label (ref value)) in
    recurse (env, e, record_ex)
  | Pexp_setfield (_, _, _) -> [req]
  | Pexp_array exps ->
    begin match value.v_ with
    | Array v_arr when List.length exps = Array.length v_arr ->
      List.map2 (fun e v -> recurse (env, e, v)) exps (Array.to_list v_arr)
      |> List.concat
    | _ -> [req]
    end
  | Pexp_send (_, _) -> [req]
  | Pexp_new _ -> [req]
  | Pexp_setinstvar (_, _) -> [req]
  | Pexp_override _ -> [req]
  | Pexp_letexception ({ pext_name = name; pext_kind = k; _ }, e) ->
    let nenv =
      match k with
      | Pext_decl _ ->
        let d = next_exn_id () in (* :/ :/ :/ *)
        Envir.env_set_constr name.txt d env
      | Pext_rebind path ->
        Envir.env_set_constr name.txt (Envir.env_get_constr env path) env
    in
    recurse (nenv, e, value)
  | Pexp_letmodule (name, me, e) ->
    (* Will this mutate? :/ *)
    begin match eval_module_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no me with
    | Some m ->
      let env' = Envir.env_set_module name.txt m env in
      recurse (env', e, value)
    | None -> [req]
    end
  | Pexp_assert _ -> [req]
  | Pexp_lazy _ -> [req]
  | Pexp_poly (e, _) -> recurse (env, e, value)
  | Pexp_newtype (_, e) -> recurse (env, e, value)
  | Pexp_open (_, lident, e) ->
    let nenv =
      match Envir.env_get_module_data env lident with
      | exception Not_found ->
        (* Module might be a .mli only *)
        env
      | module_data -> Envir.env_extend false env module_data
    in
    recurse (nenv, e, value)
  | Pexp_object _ -> [req]
  | Pexp_pack _ -> [req]
  | Pexp_extension _ -> [req]

let push_down_req fillings _prog ?(lookup_exp_typed = fun _ -> None) ?(hit_a_function_f = fun _ _ _ _ -> ()) req =
  try
    Eval.with_fuel 300
      (fun () -> push_down_req_ fillings lookup_exp_typed hit_a_function_f req)
      (fun () ->
        (* print_endline "out of fuel";
        print_endline (StructItems.to_string (apply_fillings fillings prog)); *)
        [req]
      )
  with _ -> [req]


(* Size is # pat nodes plus # exp nodes *)
let ast_size apply_iterator_to_node =
  let size = ref 0 in
  let iter_exp iter exp =
    incr size;
    dflt_iter.expr iter exp;
    (* Don't count the tuple for multi-arg constructors. (E-guessing counts the terms the same way as multi-arg functions.) *)
    match exp.pexp_desc with
    | Pexp_construct (_, Some { pexp_desc = Pexp_tuple _; _ }) -> decr size
    | _ -> ()
  in
  let iter_pat iter pat =
    incr size;
    dflt_iter.pat iter pat;
    (* Don't count the tuple for multi-arg constructors. *)
    match pat.ppat_desc with
    | Ppat_construct (_, Some { ppat_desc = Ppat_tuple _; _ }) -> decr size
    | _ -> ()
  in
  let iter = { dflt_iter with expr = iter_exp; pat = iter_pat } in
  apply_iterator_to_node iter;
  !size

let exp_size exp      = ast_size (fun iterator -> iterator.expr iterator exp)
let pat_size pat      = ast_size (fun iterator -> iterator.pat iterator pat)
let program_size prog = ast_size (fun iterator -> iterator.structure iterator prog)

exception Found_names of string list

(* Estimate that all names syntactically under a lambda are "non-constant". *)
let nonconstant_names_at_loc target_loc prog =
  let dflt_iter = Ast.dflt_iter in
  let in_func = ref false in
  let names = ref [] in
  let iter_case iter case =
    let higher_names = !names in
    if !in_func then names := Pat.names case.pc_lhs @ !names;
    dflt_iter.case iter case;
    names := higher_names
  in
  let iter_exp iter exp =
    let higher_in_func = !in_func in
    let higher_names   = !names in
    if exp.pexp_loc = target_loc then begin
      (* print_endline (Exp.to_string exp); *)
      (* print_endline (string_of_bool !in_func); *)
      raise (Found_names !names)
    end;
    begin match exp.pexp_desc with
    | Pexp_let (Asttypes.Recursive, vbs, _body) ->
      if !in_func then names := (vbs |>@@ Vb.names) @ !names;
      dflt_iter.expr iter exp
    | Pexp_let (Asttypes.Nonrecursive, vbs, body) ->
      vbs |> List.iter (iter.value_binding iter);
      if !in_func then names := (vbs |>@@ Vb.names) @ !names;
      iter.expr iter body;
    | Pexp_function _cases ->
      in_func := true;
      dflt_iter.expr iter exp
    | Pexp_fun (_, arg_opt, pat, body) ->
      arg_opt |>& iter.expr iter ||& ();
      iter.pat iter pat;
      in_func := true;
      names   := Pat.names pat @ !names;
      iter.expr iter body
    | Pexp_for (pat, e_lo, e_hi, _, body) ->
      iter.pat iter pat;
      iter.expr iter e_lo;
      iter.expr iter e_hi;
      names := Pat.names pat @ !names;
      iter.expr iter body
    | _ -> dflt_iter.expr iter exp
    end;
    names   := higher_names;
    in_func := higher_in_func;
  in
  let iter = { dflt_iter with case = iter_case; expr = iter_exp } in
  try
    iter.structure iter prog;
    print_endline @@ "nonconstant_names_at_loc: didn't find loc " ^ Loc.to_string target_loc;
    SSet.empty
  with Found_names names ->
    (* print_endline @@ "nonconstant_names_at_loc: " ^ String.concat ", " names; *)
    SSet.of_list names


(* let unused_parameter_names_at_loc target_loc prog =
  let dflt_iter = Ast.dflt_iter in
  let names = ref [] in
  (* Not using Ast.Exp.iter because we want to visit children _after_ mutating names. *)
  let iter_exp (iter : Ast_iterator.iterator) exp =
    let higher_names = !names in
    if exp.pexp_loc = target_loc then raise (Found_names !names);
    begin match exp.pexp_desc with
    | Pexp_fun (_, arg_opt, pat, body) ->
      arg_opt |>& iter.expr iter ||& ();
      let unused_names = List.diff (Pat.names pat) (Scope.free_unqualified_names body) in
      names := unused_names @ !names;
      iter.expr iter body
    | _ -> dflt_iter.expr iter exp;
    end;
    names := higher_names;
  in
  let iter = { dflt_iter with expr = iter_exp } in
  try
    iter.structure iter prog;
    print_endline @@ "unused_parameter_names_at_loc: didn't find loc " ^ Loc.to_string target_loc;
    []
  with Found_names names ->
    print_endline @@ "unused_parameter_names_at_loc: " ^ String.concat ", " names;
    names *)


exception Unused_name

(* Only care when in a hole filling OR the function contains a hole. *)
let all_parameter_names_used fillings prog =
  let dflt_iter = Ast.dflt_iter in
  let in_a_filling  = ref false in
  (* Not using Ast.Exp.iter because we want to visit children _after_ mutating names. *)
  let iter_exp (iter : Ast_iterator.iterator) exp =
    begin match exp.pexp_desc with
    | Pexp_fun (_, arg_opt, pat, body) ->
      arg_opt |>& iter.expr iter ||& ();
      let unused_names = List.diff (Pat.names pat) (Scope.free_unqualified_names ~fillings body) in
      if unused_names <> [] && (!in_a_filling || Exp.FromNode.exists Exp.is_hole body) then raise Unused_name;
      iter.expr iter body
    | Pexp_ident { txt = Longident.Lident "??"; _ } ->
      begin match Shared.Loc_map.find_opt exp.pexp_loc fillings with
      | Some filling_exp ->
        let in_a_filling_old = !in_a_filling in
        in_a_filling := true;
        iter.expr iter filling_exp;
        in_a_filling := in_a_filling_old
      | None ->
        dflt_iter.expr iter exp
      end
    | _ -> dflt_iter.expr iter exp;
    end
  in
  let iter = { dflt_iter with expr = iter_exp } in
  try
    iter.structure iter prog;
    true
  with Unused_name ->
    false




type hole_synth_env =
    { tenv                               : Env.t
    ; hole_type                          : Types.type_expr
    ; user_ctors                         : (Longident.t * Types.constructor_description * lprob) list
    ; nonconstant_names                  : SSet.t
    ; local_idents                       : (expression * Types.type_expr * lprob) list
    ; check_if_constant                  : expression -> bool
    ; cant_be_constant                   : bool
    ; single_asserted_exp                : (expression * lprob) option
    ; mutable nonconstant_idents_at_type : (Types.type_expr * (expression * Types.type_expr * lprob) list (* Sorted, most probable first *)) list
    ; mutable idents_at_type             : (Types.type_expr * (expression * Types.type_expr * lprob) list (* Sorted, most probable first *)) list
    ; mutable functions_producing_type   : (Types.type_expr * (expression  * int * Types.type_expr * lprob) list (* Sorted, most probable first, arg count, type unified with goal type *)) list
    ; mutable ctors_producing_type       : (Types.type_expr * (Longident.t * int * Types.type_expr * lprob) list (* Sorted, most probable first, arg count type unified with goal type *)) list
    }
let is_req_satisified_by trace_state fillings (env, exp, expected) =
  (* begin try Loc_map.bindings fillings |>@ snd |>@ Exp.to_string |> List.iter print_endline
  with _ -> Loc_map.bindings fillings |>@ snd |>@ (Formatter_to_stringifier.f (Printast.expression 0)) |> List.iter print_endline
  end; *)
  (* print_endline @@ string_of_req (env, exp, expected); *)
  let evaled = eval trace_state fillings env exp in
  (* print_endline @@ Formatter_to_stringifier.f pp_print_value evaled; *)
  Assert_comparison.values_equal_for_assert evaled expected

let reqs_satisfied_and_all_filled_expressions_hit_during_execution fillings reqs =
  let fillings =
    (* Freshen non-holes. *)
    fillings
    |> Loc_map.map @@ Exp.FromNode.map begin fun exp ->
      if Exp.is_hole exp
      then exp
      else { exp with pexp_loc = Loc.fresh () }
    end
  in
  let trace_state = Trace.new_trace_state () in
  reqs |> List.for_all (is_req_satisified_by trace_state fillings)
  && begin
    (* print_endline (Loc_map.to_string Exp.to_string fillings); *)
    (* Ensure all expressions exercised during execution (we didn't insert junk branches etc.) *)
    fillings
    |> Loc_map.values
    |>@@ Exp.flatten
    |>@ Exp.loc
    (* |>@ (fun loc -> print_endline @@ Loc.to_string loc; loc) *)
    |> List.for_all (fun loc -> Trace.entries_for_loc loc trace_state.trace <> [])
  end

(* let names_in_env = env1.values |> SMap.bindings |>@& (fun (name, v) -> match v with (_, Value _) -> Some name | _ -> None) in *)
(* prog should already have fillings applied to it *)

let build_cache_list typ idents =
  idents
  |>@& begin fun (exp, ident_t, lprob) ->
    Type.unify_opt ident_t typ
    |>& (fun t' -> (exp, t', lprob))
  end
  |> List.sort_by (fun (_, _, lprob) -> -.lprob)

let local_idents_at_loc loc tenv prog : (expression * Types.type_expr * lprob) list =
  let local_names = Scope.names_at_loc loc prog in
  let local_name_count = List.length local_names in
  (* local_names *)
  (* |>@& begin fun name -> (name, Typing.type_of_name name tenv)) *)
  Stats_model.local_idents |>@& begin fun (nth, lprob) ->
    if nth >= local_name_count then None else
    let name = List.nth local_names nth in
    Some
      ( Exp.simple_var name
      , Typing.type_of_name name tenv
      , lprob
      )
  end

let rec drop_n_args_from_arrow n typ =
  if n <= 0 then typ else
  begin match (Type.regular typ).desc with
  | Types.Tarrow (Asttypes.Nolabel, _, t_r, _) -> drop_n_args_from_arrow (n - 1) t_r
  | _                                          -> failwith "huuuuuuh?"
  end



exception Not_constant

let is_constant nonconstant_names : expression -> bool =
  let iterator =
    Exp.iterator begin function
      | { pexp_desc = Pexp_ident {txt = Longident.Lident name; _ }; _ }
        when SSet.mem name nonconstant_names ->
        raise Not_constant
      | _ -> ()
    end
  in
  begin function exp ->
    try
      iterator.expr iterator exp;
      true
    with Not_constant -> false
  end

  (* not (exp |> Exp.flatten |>@& Exp.simple_name |> List.exists (fun name -> SSet.mem name hole_synth_env.nonconstant_names)) *)

(* arg_count_remaining and arg_i are separate, to support partial applications. *)
(* May be able to cache here (don't forget about lprob!) *)
let rec args_seq ~cant_be_constant hole_synth_env func_type arg_count_remaining arg_i min_lprob : (expression list * Types.type_expr * lprob) list =
  if arg_count_remaining <= 0 then (if cant_be_constant then [] else [([], func_type, lprob_1)]) else
  if min_lprob > max_single_term_lprob then [] else
  match Type.flatten_arrows func_type with
  | (_::_::_) as flat_type ->
    let arg_t = List.nth flat_type arg_i in
    let reserve_lprob = max_single_term_lprob *. (float_of_int @@ arg_count_remaining - 1) in
    let term_cant_be_constant = cant_be_constant && arg_count_remaining = 1 in
    terms_at_type ~cant_be_constant:term_cant_be_constant hole_synth_env arg_t (div_lprobs min_lprob reserve_lprob)
    |>@@ begin fun (arg, arg_t', lprob) ->
      let func_type' = Type.copy func_type in
      match Type.unify_mutating_opt (List.nth (Type.flatten_arrows func_type') arg_i) (Type.copy arg_t') with
      | None   -> []
      | Some _ ->
        let remainder_cant_be_constant =
          cant_be_constant && hole_synth_env.check_if_constant arg
        in
        args_seq ~cant_be_constant:remainder_cant_be_constant hole_synth_env func_type' (arg_count_remaining-1) (arg_i+1) (div_lprobs min_lprob lprob)
        |>@ (fun (args_r, func_type'', later_lprob) -> (arg::args_r, func_type'', mult_lprobs later_lprob lprob))
    end
  | _ -> failwith "this shouldn't happen"


(* and ctor_terms ~cant_be_constant hole_synth_env typ min_lprob (lid, { Types.cstr_res; cstr_args; cstr_arity; _ }, lprob) =
  (* print_endline @@ cstr_name ^ " " ^ string_of_float lprob; *)
  if min_lprob > lprob then [] else
  let ctor_type_as_arrows = Type.unflatten_arrows (cstr_args @ [cstr_res]) in
  (* print_endline @@ (Type.to_string typ); *)
  (* print_endline @@ (Type.to_string ctor_type_as_arrows); *)
  (* print_endline @@ (Typing.can_produce_typ ctor_type_as_arrows typ <> None |> string_of_bool); *)
  (* ignore (exit 0); *)
  (* print_endline @@ Longident.to_string lid ^ "\t" ^ Type.to_string ctor_type_as_arrows; *)
  match Typing.can_produce_typ ctor_type_as_arrows typ with
  | Some (arg_count, ctor_type_as_arrows_unified_with_goal_ret_t) ->
    if arg_count <> cstr_arity then [] else begin (* Ctors must always be fully applied *)
      (* print_endline @@ Longident.to_string lid ^ "\t\t" ^ Type.to_string ctor_type_as_arrows_unified_with_goal_ret_t; *)
      (* This wil properly exclude 0 arg ctors when we can't be constant *)
      args_seq ~cant_be_constant hole_synth_env ctor_type_as_arrows_unified_with_goal_ret_t arg_count 0 (div_lprobs min_lprob lprob)
      |>@ begin fun (arg_terms, ctor_type_as_arrows', args_lprob) ->
        let out_type = drop_n_args_from_arrow arg_count ctor_type_as_arrows' in
        let ctor_arg =
          match arg_count with
          | 0 -> None
          | 1 -> Some (List.hd arg_terms)
          | _ -> Some (Exp.tuple arg_terms)
        in
        (* print_endline @@ Exp.to_string (Exp.construct (Location.mknoloc lid) ctor_arg); *)
        ( Exp.construct (Location.mknoloc lid) ctor_arg
        , out_type
        , mult_lprobs args_lprob lprob
        )
      end
    end
  | None ->
    [] *)

(* and stdlib_ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else

    stdlib_ctors |>@ Tup3.map_thd (mult_lprobs stdlib_ctor_lprob)
    (* | Some std *)
  |>@@ ctor_terms ~cant_be_constant hole_synth_env typ min_lprob *)

(* and nonstdlib_ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  hole_synth_env.user_ctors |>@ Tup3.map_thd (mult_lprobs nonstdlib_ctor_lprob) |>@@ ctor_terms ~cant_be_constant hole_synth_env typ min_lprob *)

and ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  begin match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.ctors_producing_type with
  | None ->
    let ctors_producing_type =
      begin
        (pervasives_ctors          |>@ Tup3.map_thd (mult_lprobs stdlib_ctor_lprob)) @
        (hole_synth_env.user_ctors |>@ Tup3.map_thd (mult_lprobs nonstdlib_ctor_lprob))
      end
      |>@& begin fun (lid, { Types.cstr_res; cstr_args; cstr_arity; _ }, lprob) ->
        (* print_endline @@ cstr_name ^ " " ^ string_of_float lprob; *)
        let ctor_type_as_arrows = Type.unflatten_arrows (cstr_args @ [cstr_res]) in
        (* print_endline @@ (Type.to_string typ); *)
        (* print_endline @@ (Type.to_string ctor_type_as_arrows); *)
        (* print_endline @@ (Typing.can_produce_typ ctor_type_as_arrows typ <> None |> string_of_bool); *)
        (* ignore (exit 0); *)
        (* print_endline @@ Longident.to_string lid ^ "\t" ^ Type.to_string ctor_type_as_arrows; *)
        match Typing.can_produce_typ ctor_type_as_arrows typ with
        | Some (arg_count, ctor_type_as_arrows_unified_with_goal_ret_t) when arg_count = cstr_arity -> (* Ctors must always be fully applied *)
          Some (lid, arg_count, ctor_type_as_arrows_unified_with_goal_ret_t, lprob)
        | _ ->
          None
      end
      |> List.sort_by (fun (_, _, _, lprob) -> -.lprob)
    in
    hole_synth_env.ctors_producing_type <- (typ, ctors_producing_type) :: hole_synth_env.ctors_producing_type;
    ctors_producing_type
  | Some ctors_producing_type ->
    ctors_producing_type
  end
  |> List.take_while (fun (_, _, _, lprob) -> lprob >= min_lprob)
  |>@@ begin fun (lid, arg_count, ctor_type_as_arrows_unified_with_goal_ret_t, lprob) ->
    args_seq ~cant_be_constant hole_synth_env ctor_type_as_arrows_unified_with_goal_ret_t arg_count 0 (div_lprobs min_lprob lprob)
    |>@ begin fun (arg_terms, ctor_type_as_arrows', args_lprob) ->
      let out_type = drop_n_args_from_arrow arg_count ctor_type_as_arrows' in
      let ctor_arg =
        match arg_count with
        | 0 -> None
        | 1 -> Some (List.hd arg_terms)
        | _ -> Some (Exp.tuple arg_terms)
      in
      (* print_endline @@ Exp.to_string (Exp.construct (Location.mknoloc lid) ctor_arg); *)
      ( Exp.construct (Location.mknoloc lid) ctor_arg
      , out_type
      , mult_lprobs args_lprob lprob
      )
    end
  end

and all_consts_ordered =
  List.concat
    [ const_strs_1_char_or_less
    ; const_ints
    ; const_chars
    ; const_floats
    ]
  |> List.sort_by (fun (_, _, lprob) -> -.lprob)

and consts_at_type _hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  List.take_while (fun (_, _, lprob) -> lprob >= min_lprob) @@
  if Type.is_var_type typ then
    all_consts_ordered
  else
    if Type.is_string_type typ then const_strs_1_char_or_less else
    if Type.is_int_type    typ then const_ints   else
    if Type.is_char_type   typ then const_chars  else
    if Type.is_float_type  typ then const_floats else
    []

(* Apps are never constant—they require a non-constant arg *)
and apps_at_type hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  begin match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.functions_producing_type with
  | None ->
    let funcs_producing_type =
      (hole_synth_env.local_idents @ pervasives_pure_idents_only)
      |>@& begin fun (fexp, func_type, lprob) ->
        (* if min_lprob > lprob then None else *)
        if not (Type.is_arrow_type func_type) then None else
        match Typing.can_produce_typ func_type typ with
        | Some (0, _) | None -> None (* functions must be at least partially applied *)
        | Some (arg_count, func_type_unified_with_goal_ret_t) ->
          Some (fexp, arg_count, func_type_unified_with_goal_ret_t, lprob)
      end
      |> List.sort_by (fun (_, _, _, lprob) -> -.lprob)
    in
    hole_synth_env.functions_producing_type <- (typ, funcs_producing_type) :: hole_synth_env.functions_producing_type;
    funcs_producing_type
  | Some funcs ->
    funcs
  end
  |> List.take_while (fun (_, _, _, lprob) -> lprob >= min_lprob)
  |>@@ begin fun (fexp, arg_count, func_type_unified_with_goal_ret_t, lprob) ->
    args_seq ~cant_be_constant:true hole_synth_env func_type_unified_with_goal_ret_t arg_count 0 (div_lprobs min_lprob lprob)
    |>@ begin fun (arg_terms, func_type', args_lprob) ->
      let out_type = drop_n_args_from_arrow arg_count func_type' in
      (* print_endline @@ Exp.to_string (Exp.construct (Location.mknoloc lid) ctor_arg); *)
      ( Exp.apply fexp (arg_terms |>@ fun arg -> (Asttypes.Nolabel, arg))
      , out_type
      , mult_lprobs args_lprob lprob
      )
    end
  end

  (* (hole_synth_env.local_idents @ stdlib_idents) *)
  (* (hole_synth_env.local_idents @ pervasives_pure_idents_only)
  |>@@ begin fun (fexp, func_type, lprob) ->
    if min_lprob > lprob then [] else
    if not (Type.is_arrow_type func_type) then [] else
    match Typing.can_produce_typ func_type typ with
    | Some (0, _) -> [] (* functions must be at least partially applied *)
    | Some (arg_count, func_type_unified_with_goal_ret_t) ->
      args_seq ~cant_be_constant:true hole_synth_env func_type_unified_with_goal_ret_t arg_count 0 (div_lprobs min_lprob lprob)
      |>@ begin fun (arg_terms, func_type', args_lprob) ->
        let out_type = drop_n_args_from_arrow arg_count func_type' in
        (* print_endline @@ Exp.to_string (Exp.construct (Location.mknoloc lid) ctor_arg); *)
        ( Exp.apply fexp (arg_terms |>@ fun arg -> (Asttypes.Nolabel, arg))
        , out_type
        , mult_lprobs args_lprob lprob
        )
      end
    | None ->
      []
  end *)

and ites_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > max_single_term_lprob *. 3.0 then [] else
  let else_terms =
    terms_at_type ~cant_be_constant:false hole_synth_env typ (div_lprobs min_lprob (max_single_term_lprob *. 2.0))
  in
  else_terms
  |>@@ begin fun (else_term, else_t, else_lprob) ->
    let then_terms =
      terms_at_type ~cant_be_constant:(cant_be_constant && hole_synth_env.check_if_constant else_term) hole_synth_env else_t (div_lprobs min_lprob (mult_lprobs else_lprob max_single_term_lprob))
    in
    then_terms
    |>@@ begin fun (then_term, then_t, then_lprob) ->
      let conditional_terms =
        terms_at_type ~cant_be_constant:true hole_synth_env Predef.type_bool (div_lprobs min_lprob (mult_lprobs else_lprob then_lprob))
      in
      conditional_terms
      |>@@ begin fun (cond_term, _, cond_lprob) ->
        [(Exp.ifthenelse cond_term then_term (Some else_term), then_t, mult_lprobs cond_lprob (mult_lprobs else_lprob then_lprob))]
      end
    end
  end


and idents_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  (* (hole_synth_env.local_idents @ stdlib_idents) *)
  begin if cant_be_constant then
    begin match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.nonconstant_idents_at_type with
    | None ->
      let idents =
        hole_synth_env.local_idents
        |>@? (fun (e, _, _) -> SSet.mem (Exp.simple_name e ||& "") hole_synth_env.nonconstant_names)
        |> build_cache_list typ
      in
      hole_synth_env.nonconstant_idents_at_type <- (typ, idents)::hole_synth_env.nonconstant_idents_at_type;
      idents
    | Some idents -> idents
    end
  else
    begin match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.idents_at_type with
    | None ->
      let idents = build_cache_list typ (hole_synth_env.local_idents @ pervasives_pure_idents_only) in
      hole_synth_env.idents_at_type <- (typ, idents)::hole_synth_env.idents_at_type;
      idents
    | Some idents -> idents
    end
  end
  |> List.take_while (fun (_, _, lprob) -> lprob >= min_lprob)
  (* |>@& begin fun (exp, ident_t, lprob) ->
    if lprob < min_lprob then None else
    Type.unify_opt ident_t typ
    |>& (fun t' -> (exp, t', lprob))
  end *)

and terms_at_type ~cant_be_constant ?if_constant_must_be hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > max_single_term_lprob then [] else
  let terms1 =
    let cant_be_constant = cant_be_constant || if_constant_must_be <> None in
    List.concat
      [ ctors_at_type  ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ctor_lprob)  |>@ Tup3.map_thd (mult_lprobs ctor_lprob)
      ; apps_at_type                     hole_synth_env typ (div_lprobs min_lprob app_lprob)   |>@ Tup3.map_thd (mult_lprobs app_lprob)
      ; ites_at_type   ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ite_lprob)   |>@ Tup3.map_thd (mult_lprobs ite_lprob)
      ; idents_at_type ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ident_lprob) |>@ Tup3.map_thd (mult_lprobs ident_lprob)
      ]
  in
  let terms2 =
    if cant_be_constant then [] else
    begin match if_constant_must_be with
    | None ->
      consts_at_type hole_synth_env typ (div_lprobs min_lprob const_lprob) |>@ Tup3.map_thd (mult_lprobs const_lprob)
    | Some (only_allowed_constant_exp, lprob) when lprob >= min_lprob ->
      (* Don't need to check type because, if present, this exp comes directly from pushing a req down to a hole. *)
      [(only_allowed_constant_exp, typ, lprob)]
    | _ ->
      []
    end
  in
  (* print_endline @@ "terms at " ^ Type.to_string typ ^ " lprob > " ^ string_of_float min_lprob; *)
  (* print_endline (terms |>@ Tup3.fst |>@ Exp.to_string |> String.concat "  "); *)
  terms2 @ terms1

let hole_fillings_seq ~cant_be_constant (fillings, lprob) min_lprob hole_loc static_hole_type hole_synth_env _reqs_on_hole _prog : (bool * fillings * lprob) Seq.t =
  let term_min_lprob = div_lprobs min_lprob lprob in
  (* let terms_seq = *)
    (* let nonconstant_names = SSet.empty in *)
    (* print_endline (Loc.to_string hole_loc);
    print_endline (string_of_int (List.length reqs_on_hole));
    print_endline (String.concat "\n" (reqs_on_hole |>@ string_of_req)); *)
    (* let nonconstant_names = nonconstant_names_at_loc hole_loc prog in *)
  (* let hole_synth_env = new_hole_synth_env tenv in *)
    (* Seq.append
      (constants_at_type_seq hole_synth_env static_hole_type term_max_lprob term_min_lprob)
      (nonconstants_at_type_seq size_limit hole_synth_env static_hole_type term_max_lprob term_min_lprob) *)
  (* in *)
  (* print_endline "hi"; *)
  (* print_endline (Loc.to_string hole_loc); *)
  let if_constant_must_be = hole_synth_env.single_asserted_exp in
  terms_at_type ~cant_be_constant ?if_constant_must_be hole_synth_env static_hole_type term_min_lprob
  |>@ begin fun (term, _term_t, term_lprob) ->
    (* print_endline (string_of_int !terms_tested_count ^ "\t" ^ Exp.to_string term ^ "\t" ^ Type.to_string term_t ^ "\t" ^ Type.to_string static_hole_type); *)
    (* Printast.expression 0 Format.std_formatter term; *)
    let fillings = Loc_map.add hole_loc term fillings in
    (hole_synth_env.check_if_constant term, fillings, mult_lprobs term_lprob lprob)
    (* if reqs_on_hole |> List.for_all (is_req_satisified_by fillings) then
      Some (fillings, mult_lprobs term_lprob lprob)
    else
      None *)
  end
  |> List.to_seq


let hole_locs prog fillings = apply_fillings fillings prog |> Exp.all |>@? Exp.is_hole |>@ Exp.loc


(* Return a list of programs with arg and return types concretized to each assert. *)
let apply_fillings_and_degeneralize_functions fillings lookup_exp_typed prog reqs : program list =
  reqs
  |>@ begin fun req ->
    let pats_to_annotate = ref [] in
    let exps_to_annotate = ref [] in
    let hit_a_function_f arg_pat f_body arg_val expected_output =
      begin match arg_val.type_opt with
      | Some val_type ->
        pats_to_annotate := (arg_pat.ppat_loc, val_type) :: !pats_to_annotate;
      | None -> ()
      end;
      match expected_output.v_, expected_output.type_opt with
      | ExCall _, _      -> ()
      | _, Some out_type -> exps_to_annotate := (f_body.pexp_loc, out_type) :: !exps_to_annotate
      | _                -> ()
    in
    ignore @@ push_down_req fillings prog ~lookup_exp_typed ~hit_a_function_f req;
    prog
    |> Exp.map begin fun e ->
      match List.assoc_opt e.pexp_loc !exps_to_annotate with
      | Some typ -> Exp.constraint_ e (Type.to_core_type typ)
      | None     -> e
    end
    |> Pat.map begin fun p ->
      match List.assoc_opt p.ppat_loc !pats_to_annotate with
      | Some typ -> Pat.constraint_ p (Type.to_core_type typ)
      | None     -> p
    end
    |> apply_fillings fillings
    |> Exp.replace_by Exp.is_assert Exp.unit (* Asserts on diff types can prematurely produce type-incorrect programs. *)
  end
  |> List.dedup_by StructItems.to_string

let count_type_var_annotations prog =
  let n = ref 0 in
  let iter_core_type iterator core_type =
    dflt_iter.typ iterator core_type;
    match core_type.ptyp_desc with
    | Ptyp_var _ -> incr n;
    | _          -> ()
  in
  let iterator = { dflt_iter with typ = iter_core_type } in
  iterator.structure iterator prog;
  !n

  (* prog
  |> Exp.iter begin function
    | { pexp_desc = Pexp_constraint (_, core_type); _} as e -> print_endline (Exp.to_string e); n := !n + (core_type |> Type.from_core_type ~env:typed_prog.Typedtree.str_final_env |> Type.flatten |> List.count Type.is_var_type)
    | _ -> ()
  end;
  prog
  |> Pat.iter begin function
    | { ppat_desc = Ppat_constraint (_, core_type); _} -> n := !n + (core_type |> Type.from_core_type ~env:typed_prog.Typedtree.str_final_env |> Type.flatten |> List.count Type.is_var_type)
    | _ -> ()
  end;
  !n *)


let e_guess (fillings, lprob) max_lprob min_lprob lookup_exp_typed prog reqs file_name : (fillings * lprob) Seq.t =
  (* Printast.structure 0 Format.std_formatter prog; *)
  let hole_locs = hole_locs prog fillings in
  let progs = apply_fillings_and_degeneralize_functions fillings lookup_exp_typed prog reqs in
  print_endline @@ string_of_int (List.length progs) ^ " programs";
  let prog_and_typed_progs =
    let progs' =
      progs
      |>@ begin fun prog ->
        print_endline @@ "Typing " ^ StructItems.to_string prog ^ string_of_float min_lprob;
        let (typed_prog, _, _) =
          try Typing.typedtree_sig_env_of_parsed prog file_name
          with _ ->
            print_endline @@ "Could not type program:\n" ^ StructItems.to_string prog;
            ({ Typedtree.str_items = []; str_type = []; str_final_env = Typing.initial_env }, [], Env.empty)
        in
        (prog, typed_prog)
      end
    in
    (* Only keep progs with a minium number of type vars in the added annotations. *)
    let min_type_var_annotations_count = progs' |>@ fst %> count_type_var_annotations |> List.fold_left min max_int in
    progs'
    |>@? (fst %> count_type_var_annotations %> (=) min_type_var_annotations_count)
  in
  (* ignore @@ exit 0; *)
  print_endline @@ string_of_int (List.length prog_and_typed_progs) ^ " programs will be used";
  let reqs' = reqs |>@@ push_down_req fillings prog in
  let hole_locs_progs_and_synth_envs : (Location.t * (program * hole_synth_env) Seq.t) list =
    hole_locs
    |>@ begin fun hole_loc ->
      let progs_and_synth_envs =
        prog_and_typed_progs |>@@ begin fun (prog, typed_prog) ->
          match Typing.find_exp_by_loc hole_loc typed_prog with
          | None -> []
          | Some hole_typed_node ->
            let reqs_on_hole = reqs' |>@? (fun (_, exp, _) -> Exp.loc exp = hole_loc) in
            let unique_asserted_exps =
              reqs_on_hole |>@ (fun (_, _, value) -> Assert_comparison.exp_of_value value) |> List.dedup_by Exp.to_string
            in
            (* print_endline @@ "Names at hole: " ^ String.concat "   " (hole_synth_env.local_idents |>@ fun (exp, typ, lprob) -> Exp.to_string exp ^ " : " ^ Type.to_string typ ^ " " ^ string_of_float lprob); *)
            let nonconstant_names      = nonconstant_names_at_loc hole_loc prog in
            let user_ctors =
              let initial_ctor_descs = Env.fold_constructors List.cons None(* not looking in a nested module *) Typing.initial_env [] in
              let user_ctor_descs =
                Env.fold_constructors List.cons None(* not looking in a nested module *) typed_prog.str_final_env []
                |>@? begin fun ctor_desc -> not (List.memq ctor_desc initial_ctor_descs) end
              in
              user_ctor_descs |>@ begin fun ({ Types.cstr_name; _ } as ctor_desc) ->
                (Longident.Lident cstr_name, ctor_desc, lprob_by_counts 1 (List.length user_ctor_descs))
              end
            in
            print_endline @@ string_of_int (List.length user_ctors) ^ " user ctors";
            print_endline @@ "Nonconstant names at hole: " ^ (SSet.elements nonconstant_names |> String.concat ", ");
            [ ( prog
              , { tenv                          = hole_typed_node.exp_env
                ; hole_type                     = hole_typed_node.exp_type
                ; user_ctors                    = user_ctors
                ; nonconstant_names             = nonconstant_names
                ; local_idents                  = local_idents_at_loc hole_loc hole_typed_node.exp_env prog
                ; check_if_constant             = is_constant nonconstant_names
                ; cant_be_constant              = List.length unique_asserted_exps >= 2
                ; single_asserted_exp           = (match unique_asserted_exps with | [e] -> Some (e, max_single_constant_term_lprob *. float_of_int (exp_size e)) | _ -> None)
                ; nonconstant_idents_at_type    = []
                ; idents_at_type                = []
                ; functions_producing_type      = []
                ; ctors_producing_type          = []
                }
              )
            ]
        end
      in
      (hole_loc, List.to_seq progs_and_synth_envs)
    end
  in
  (* print_endline (hole_locs |>@ Loc.to_string |> String.concat ",\n"); *)
  let rec fillings_seq (fillings, lprob) min_lprob hole_locs_progs_and_synth_envs : (bool * fillings * lprob) Seq.t =
    match hole_locs_progs_and_synth_envs with
    | [] -> Seq.return (false, fillings, lprob)
    | (hole_loc, prog_and_synth_envs)::rest ->
      fillings_seq (fillings, lprob) (div_lprobs min_lprob max_single_term_lprob (* reserve some probability for this hole! *)) rest
      |> Seq.flat_map begin fun (any_constant_holes, fillings, lprob) ->
        (* print_endline "retyping prog"; *)
        (* progs *)
        (* ignore (exit 0); *)
        prog_and_synth_envs
        |> Seq.flat_map begin fun (prog, hole_synth_env) ->
            (* At most one hole can be constant. *)
            hole_fillings_seq ~cant_be_constant:any_constant_holes (fillings, lprob) min_lprob hole_loc hole_synth_env.hole_type hole_synth_env [] prog
          end
        |> Seq.map (Tup3.map_fst (fun hole_is_constant -> hole_is_constant || any_constant_holes))
      end
  in
  fillings_seq (fillings, lprob) min_lprob hole_locs_progs_and_synth_envs
  |> Seq.filter (fun (_, _, lprob) -> lprob <= max_lprob)
  |> Seq.map (fun (_, fillings, lprob) -> (fillings, lprob))

(* Use hole requirements+types to sketch out possible solutions *)
(* e.g introduce lambda or pattern match *)
(* If lambda is rhs of a lone binding, make the binding recursive. *)
let refine prog (fillings, lprob) reqs file_name next =
  let reqs'           = reqs |>@@ push_down_req fillings prog in
  let hole_locs       = hole_locs prog fillings in
  let is_ex_call      = function { v_ = ExCall _; _ } -> true | _ -> false in
  let is_ex_dont_care = function { v_ = ExDontCare; _ } -> true | _ -> false in
  (* reqs |> List.iter (string_of_req %> print_endline); *)
  (* hole_locs |> List.iter (Loc.to_string %> print_endline); *)
  (* reqs' |> List.iter (string_of_req %> print_endline); *)
  let prog = apply_fillings fillings prog in
  let (typed_prog, _, tenv) =
    try Typing.typedtree_sig_env_of_parsed prog file_name
    with _ -> ({ Typedtree.str_items = []; str_type = []; str_final_env = Env.empty }, [], Env.empty)
  in
  let avoid_names = StructItems.deep_names prog in
  hole_locs
  |>@@ begin fun hole_loc ->
    match Typing.find_exp_by_loc hole_loc typed_prog with None -> [] | Some hole_typed_node ->
    let reqs_on_hole = reqs' |>@? (fun (_, exp, expected) -> Exp.loc exp = hole_loc && not (is_ex_dont_care expected)) in
    (* reqs_on_hole |> List.iter (string_of_req %> print_endline); *)
    if reqs_on_hole = [] then [] else
    let intro_lambda_seqs =
      if reqs_on_hole |> List.for_all (fun (_, _, expected) -> is_ex_call expected) then
        let base_name =
          match List.hd reqs_on_hole with
          | (_, _, { v_ = ExCall (v, _); _} ) -> Name.base_name_from_val v
          | _ -> "var"
        in
        let sketch = Exp.from_string @@ "fun " ^ Name.gen ~base_name prog ^ " -> (??)" in
        [ next (fillings |> Loc_map.add hole_loc (Exp.freshen_locs sketch), mult_lprobs fun_lprob lprob) ]
      else
        []
    in
    let destruct_seqs =
      let nonconstant_names = nonconstant_names_at_loc hole_loc prog in
      local_idents_at_loc hole_loc hole_typed_node.exp_env prog
      |>@& (fun (e, _t, scrutinee_lprob) -> Exp.simple_name e |>& fun name -> (name, scrutinee_lprob))
      |>@? (fun (name, _) -> SSet.mem name nonconstant_names)
      |>@@ begin fun (scrutinee_name, scrutinee_lprob) ->
        let ctor_type_path_opts_at_name =
          (* Ensure the name is always a ctor... *)
          reqs_on_hole
          |>@ begin fun (env, _, _) ->
            match Envir.env_get_value_or_lvar env (Longident.lident scrutinee_name) with
            | Value { v_ = Constructor (ctor_name, _, _); _} ->
              begin match Env.lookup_constructor (Longident.Lident ctor_name) tenv with
              | { cstr_res = { desc = Types.Tconstr (type_path, _, _); _ } ; _ } -> Some type_path
              | _ -> None
              | exception Not_found -> None
            end
            | _ -> None
            | exception Not_found -> None
          end
        in
        match Option.project ctor_type_path_opts_at_name |>& List.dedup with
        | Some [type_path] ->
          let cases = Case_gen.gen_ctor_cases ~avoid_names type_path tenv in
          let sketch = Exp.match_ (Exp.var scrutinee_name) cases in
          [ next (fillings |> Loc_map.add hole_loc (Exp.freshen_locs sketch), mult_lprobs scrutinee_lprob (mult_lprobs match_lprob lprob)) ]
        | _ -> []
      end
    in
    intro_lambda_seqs @ destruct_seqs
  end
  |> Seq.concat


let abort_lprob = log(min_float) (* If using 64bit floats directly (rather than lprobs), enter denormalized IEEE numbers after this (which is close to rounding off to zero). We never get close to this. *)

let rec fill_holes ?(max_lprob = max_single_term_lprob +. 0.01) start_sec lookup_exp_typed rejected_exp_hashes prog reqs file_name : fillings option =
  let start_hole_locs = hole_locs prog Loc_map.empty in
  if  start_hole_locs = [] then (print_endline "no holes"; Some Loc_map.empty) else
  if max_lprob <= abort_lprob then (print_endline "aborting"; None) else
  let min_lprob = max (mult_lprobs max_lprob (lprob 0.05)) abort_lprob in
  print_endline @@ "============== MIN LOGPROB " ^ string_of_float min_lprob ^ " =====================================";
  let e_guess (fillings, lprob) =
    e_guess (fillings, lprob) max_lprob min_lprob lookup_exp_typed prog reqs file_name
  in
  let top_level_sis_with_holes = prog |>@? (fun si -> Exp.exists Exp.is_hole [si]) in
  Seq.concat
    [ e_guess (Loc_map.empty, lprob_1)
    ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob))
    (* ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob))) *)
    (* ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob)))) *)
    ]
  (* Some reqs may not be pushed down to holes, so we need to verify them too. *)
  |> Seq.filter begin function (fillings, _lprob) ->
    (* if !terms_tested_count mod 10_000 = 0 then print_endline (string_of_int !terms_tested_count ^ "\t" ^ Exp.to_string term); *)
    if !terms_tested_count mod 1_000 = 0 then begin
      let terms_per_sec = int_of_float @@ float_of_int !terms_tested_count /. (Unix.gettimeofday () -. start_sec) in
      print_endline (string_of_int !terms_tested_count ^ "\t" ^ string_of_int terms_per_sec ^ " terms/sec\t" ^ StructItems.to_string (apply_fillings fillings top_level_sis_with_holes));
      (* print_endline @@ Loc_map.to_string Exp.to_string fillings; *)
    end;
    incr terms_tested_count;
    let not_rejected =
      fillings
      |> Loc_map.for_all begin fun hole_loc filling_exp ->
        let hole_rejected_hashes = Loc_map.all_at_key hole_loc rejected_exp_hashes in
        if hole_rejected_hashes = [] then true else
        let hole_exp_str = Exp.to_string (apply_fillings_to_exp fillings filling_exp) in
        (* print_endline hole_exp_str; *)
        (* if String.includes "[3;2;1]" hole_exp_str then (); *)
        not (List.mem (Hashtbl.hash hole_exp_str) hole_rejected_hashes)
      end
    in
    (* START HERE okay that bug fixed, now for nonlinearity...somehow! *)
    let all_params_used = all_parameter_names_used fillings top_level_sis_with_holes in
    (* ignore (exit 0); *)
    (* let code = StructItems.to_string (apply_fillings fillings prog) in *)
    (* print_endline code; *)
    (* if String.includes "succ (length" code && String.includes "-> 0" code then begin
      print_endline (string_of_int !terms_tested_count ^ "\t" ^ code);
      reqs |> List.for_all (is_req_satisified_by fillings)
    end else
      false *)
    (* reqs |> List.iter (fun req -> print_endline @@ string_of_req req ^ " is satisfied: " ^ string_of_bool (is_req_satisified_by fillings req)); *)

    all_params_used && not_rejected && reqs_satisfied_and_all_filled_expressions_hit_during_execution fillings reqs
  end
  |> Seq.filter begin fun (fillings, _) ->
    (* One final typecheck...apparently x :: x isn't valid... *)
    try ignore @@ Typing.typedtree_sig_env_of_parsed (apply_fillings fillings prog) file_name; true
    with _ -> false
  end
  (* Return first valid filling. *)
  |> begin fun seq ->
    match seq () with
    | Seq.Cons (fillings_lprob, rest) ->
      (* We have one candidate, but it might not be the most probable of the batch, so grab the rest. *)
      let candidates = fillings_lprob :: List.of_seq rest in
      candidates |> List.sort_by snd |> List.last_opt |>& fst
    | Seq.Nil ->
      if Unix.gettimeofday () -. start_sec > timeout_secs then
        (print_endline "Synth timeout"; None)
      else
        fill_holes ~max_lprob:min_lprob start_sec lookup_exp_typed rejected_exp_hashes prog reqs file_name (* Keep trying, with lower prob threshold. *)
  end

let make_bindings_with_holes_recursive prog =
  prog
  |> VbGroups.map begin function
      | (Nonrecursive, [vb]) ->
        let rhs_free = Scope.free_unqualified_names vb.pvb_expr in
        begin match Pat.single_name vb.pvb_pat with
        | Some name when List.mem "??" rhs_free && not (List.mem name rhs_free) ->
          (Recursive, [vb])
        | _ ->
          (Nonrecursive, [vb])
        end
      | vb_group -> vb_group
  end

let remove_unnecessary_rec_flags prog =
  prog
  |> VbGroups.map begin function
      | (Recursive, [vb]) ->
        let rhs_free = Scope.free_unqualified_names vb.pvb_expr in
        begin match Pat.single_name vb.pvb_pat with
        | Some name when not (List.mem name rhs_free) ->
          (Nonrecursive, [vb])
        | _ ->
          (Recursive, [vb])
        end
      | vb_group -> vb_group
  end

let best_result prog _trace assert_results file_name =
  terms_tested_count := 0;
  let start_sec = Unix.gettimeofday () in
  let reqs = assert_results |>@ req_of_assert_result in
  (* print_string "Req "; *)
  (* reqs |> List.iter (string_of_req %> print_endline); *)
  print_endline @@ "Typing " ^ StructItems.to_string prog;
  let (typed_struct, _, _) =
    try Typing.typedtree_sig_env_of_parsed prog file_name
    with _ -> ({ Typedtree.str_items = []; str_type = []; str_final_env = Env.empty }, [], Env.empty)
  in
  let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
  let starting_hole_locs = hole_locs prog Loc_map.empty in
  let rejected_exp_hashes = ref Loc_map.empty in
  begin
    prog
    |> Exp.iter begin fun e ->
      rejected_exp_hashes := Loc_map.add_all_to_key e.pexp_loc (Attr.findall_exp "not" e.pexp_attributes |>@& Exp.int) !rejected_exp_hashes
    end
  end;
  match fill_holes start_sec type_lookups.lookup_exp !rejected_exp_hashes prog reqs file_name with
  | exception _ -> print_endline "synth exception"; Printexc.print_backtrace stdout; None
  | None -> print_endline "synth failed"; None
  | Some fillings' ->
    print_endline @@ "synth success. " ^ string_of_float (Unix.gettimeofday () -. start_sec) ^ "s";
    (* Preserve original attrs on hole, and add "accept_or_reject" tag. *)
    let fillings'' =
      fillings'
      |> Loc_map.mapi begin fun loc e' ->
        if List.mem loc starting_hole_locs
        then
          let orig = Exp.find loc prog in
          { e' with pexp_attributes = Attr.set_tag "accept_or_reject" orig.pexp_attributes }
        else e'
      end
    in
    Some (apply_fillings fillings'' prog)


let try_async path =
  if Unix.fork () = 0 then () else (* Don't hold up the request. *)
    let synth_happening_path = Filename.concat executable_dir (nativize_path "assets/still_synthesizing.html") in
    (* print_endline synth_happening_path; *)
    write_file "" synth_happening_path;

  (* Start synthesis and the synth process killer. *)
  (* match Unix.fork () with *)
  (* | 0 -> *)
    (* Uncomment the following if you want performance profiling *)
    (* sample_this_process "synth_profile.txt"; *)
    let parsed = Interp.parse path in
    let parsed = make_bindings_with_holes_recursive parsed in
    (* let parsed_with_comments = Parse_unparse.parse_file path in
    let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
    let callables = Read_execution_env.callables_of_file path in
    let trace = Tracing.run_with_tracing path in
    let html_str = View.html_str callables trace bindings_skels in *)
    let lookup_exp_typed = Typing.exp_typed_lookup_of_parsed_with_error_recovery parsed path in
    let (trace, assert_results) =
      Eval.with_gather_asserts begin fun () ->
        Interp.run_parsed ~fuel_per_top_level_binding:10_000 lookup_exp_typed parsed path
      end in
    begin match best_result parsed trace assert_results path |>& remove_unnecessary_rec_flags with
    | Some result ->
      Undo_redo.perhaps_initialize_undo_history path;
      if parsed <> result then begin
        Pretty_code.output_code result path; (* This was overwriting synth results! :o *)
        Undo_redo.perhaps_log_revision path
      end;
    | _ -> ()
    | exception _e -> print_endline "asdfasdf";
    end;
    (* |> List.iteri begin fun i result ->
      let out_path = String.replace ".ml" ("-synth" ^ string_of_int i ^ ".ml") path in
      let out_chan = open_out out_path in (* create or truncate file, return channel *)
      let out_str = Shared.Formatter_to_stringifier.f Pprintast.structure result in
      print_endline out_str;
      output_string out_chan out_str;
      close_out out_chan;
    end; *)
    (* print_endline "normal exit"; *)
    Sys.remove synth_happening_path;
    exit 0
  (* | pid -> *)
    (* Start process killer *)
    (* Kill synthesis after 5 seconds. *)
    (* Unix.sleep 60;
    begin match Unix.waitpid [WNOHANG] pid with
    | (0, _) ->
      Unix.kill pid 9;
      print_endline "Synth timeout"
    | _ -> ()
    end *)
