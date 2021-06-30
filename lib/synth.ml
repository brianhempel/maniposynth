open Camlboot_interpreter
open Camlboot_interpreter.Data
open Parsetree
open Shared
open Shared.Ast
open Shared.Util

(* type constraint = Envir.env * Parsetree.expression * value *)

type fillings = expression Loc_map.t

(* Does not recursively apply fillings. That might result in an infinite loop. *)
let apply_fillings fillings prog =
  Loc_map.bindings fillings
  |> List.fold_left (fun prog (loc, exp) -> Exp.replace loc exp prog) prog


(* Constraints/examples. But "constraint" is an OCaml keyword, so let's call them "req"s *)
type req = Data.env * expression * value

let dont_care = new_vtrace ExDontCare

let rec try_cases fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val cases =
  let open Eval in
  match cases with (* still not handling cases that mix regular ctors and exception ctors (pattern_bind_checkexn) *)
  | [] -> None
  | case:: rest -> begin try
      let env' = pattern_bind fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val [] case.pc_lhs scrutinee_val in
      begin match case.pc_guard with
      | None -> ()
      | Some guard when is_true (eval_expr fillings prims env' lookup_exp_typed trace_state frame_no guard) -> ()
      | _ -> raise Match_fail
      end;
      Some (env', case.pc_rhs)
    with Match_fail -> try_cases fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val rest
    end

(* Fillings might only be used in pat "with" clauses here *)
let assert_result_to_req fillings assert_result : req option =
  let prims, lookup_exp_typed, trace_state, frame_no = Primitives.prims, (fun _ -> failwith "why are we looking up types in a pattern bind"), Trace.new_trace_state, -1 in
  match assert_result.f.v_ with
  | Fun (Asttypes.Nolabel, None, pat, body_exp, env_ref) ->
    let arg = assert_result.arg in
    let env' = Eval.pattern_bind fillings prims !env_ref lookup_exp_typed trace_state frame_no arg [] pat arg in
    Some (env', body_exp, assert_result.expected)
  | Function (cases, env_ref) ->
    let arg = assert_result.arg in
    begin match try_cases fillings prims !env_ref lookup_exp_typed trace_state frame_no arg cases with
    | None ->
      print_endline "Bad assert result; couldn't match arg to a function case";
      None
    | Some (env', branch_exp) -> Some (env', branch_exp, assert_result.expected)
    end
  | _ ->
    print_endline "Bad assert result; function should be a simple function";
    None

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
      |> List.to_seq
      |> Data.SMap.of_seq
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



(* val push_down_req : fillings -> req -> hole_req list *)

(* Attempt to push the req down to a req(s) on a hole. *)
(* Modification of Camlboot_interpreter.eval *)
(* Because we are not unevaluating yet, not guarenteed to succeed even where we might want it to. *)
let rec push_down_req fillings ((env, exp, value) as req) : req list =
  let open Eval in
  let prims, lookup_exp_typed, trace_state, frame_no = Primitives.prims, (fun _ -> None), Trace.new_trace_state, -1 in
  let try_cases = try_cases fillings prims env lookup_exp_typed trace_state frame_no in
  match exp.pexp_desc with
  | Pexp_ident { txt = Longident.Lident "??"; _ } ->
    begin match Loc_map.find_opt exp.pexp_loc fillings with
    | Some filling_exp -> push_down_req fillings (env, filling_exp, value)
    | None -> [req]
    end
  | Pexp_let (recflag, vbs, e) ->
    let env' = eval_bindings fillings prims env lookup_exp_typed trace_state frame_no recflag vbs in
    let deeper_hole_reqs = push_down_req fillings (env', e, value) in
    (* If a deeper req constrains a name defined here, transfer that constraint to the bound expression. *)
    deeper_hole_reqs
    |>@@ begin fun ((_, exp, value) as req) ->
      match Exp.ident_lid exp with
      | Some (Longident.Lident name) ->
        begin match vbs |>@? (Vb.names %> List.mem name) with
        | [vb] ->
          let req_env = if recflag = Asttypes.Recursive then env' else env in
          let new_ex = expand_named_example_to_pat req_env name value vb.pvb_pat in
          push_down_req fillings (req_env, vb.pvb_expr, new_ex)
        | _ -> [req]
        end
      | _ -> [req]
    end
  | Pexp_constant _ -> [req]
  | Pexp_ident _ -> [req]
  | Pexp_function cases ->
    begin match value.v_ with
    | ExCall (arg, expected) ->
      begin match try_cases arg cases with
      | None -> [req]
      | Some (env', branch_exp) -> push_down_req fillings (env', branch_exp, expected)
      end
    | _ ->
      [req]
    end
  | Pexp_fun (Nolabel, None, arg_pat, body_exp) ->
    begin match value.v_ with
    | ExCall (arg, expected) -> begin try
        let env' = pattern_bind fillings prims env lookup_exp_typed trace_state frame_no arg [] arg_pat arg in
        push_down_req fillings (env', body_exp, expected)
      with Match_fail -> [req]
      end
    | _ -> [req]
    end
  | Pexp_fun (_, _, _, _) -> [req]
  | Pexp_apply (fexp, labeled_args) ->
    if List.for_all (fun (label, _) -> label == Asttypes.Nolabel) labeled_args then
      let arg_vals = List.map (fun (_, e) -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e) labeled_args in
      (* Expand example to arg1 -> arg2 -> ex *)
      let expanded_example = List.fold_right (fun arg ex -> new_vtrace @@ ExCall (arg, ex)) arg_vals value in
      (* Push it down the function expression *)
      push_down_req fillings (env, fexp, expanded_example)
    else
      [req]
  | Pexp_tuple exps ->
    begin match value.v_ with
    | Tuple vs when List.length vs = List.length exps ->
      List.map2 (fun e v -> push_down_req fillings (env, e, v)) exps vs
      |> List.concat
    | _ -> [req]
    end
  | Pexp_match (e, cases) ->
    let arg = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
    begin match try_cases arg cases with
    | None -> [req]
    | Some (env', branch_exp) -> push_down_req fillings (env', branch_exp, value)
    end
  | Pexp_coerce (e, _, _)  -> push_down_req fillings (env, e, value)
  | Pexp_constraint (e, _) -> push_down_req fillings (env, e, value)
  | Pexp_sequence (e1, e2) ->
    let _ = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1 in (* Do we even need to do this? *)
    push_down_req fillings (env, e2, value)
  | Pexp_while (_, _) -> [req]
  | Pexp_for (_, _, _, _, _) -> [req]
  | Pexp_ifthenelse (e1, e2, e3_opt) ->
    let guard_val = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1 in
    begin try if is_true guard_val
    then push_down_req fillings (env, e2, value)
    else (
      match e3_opt with
      | None -> [req]
      | Some e3 -> push_down_req fillings (env, e3, value))
    with BombExn -> [req]
    end
  | Pexp_unreachable -> failwith "reached unreachable"
  | Pexp_try (e, cases) ->
    begin try push_down_req fillings (env, e, value)
    with InternalException exn_val ->
      begin match try_cases exn_val cases with
      | None -> raise (InternalException exn_val)
      | Some (env', branch_exp) -> push_down_req fillings (env', branch_exp, value)
      end
    end
  | Pexp_construct (_, None) -> [req]
  | Pexp_construct (lid_loced, Some e) ->
    let ctor_name = lident_name lid_loced.txt in
    let d = Envir.env_get_constr env lid_loced in
    begin match value.v_ with
    | Constructor (ex_ctor_name, d_ex, Some ex) when ex_ctor_name = ctor_name && d_ex = d ->
      push_down_req fillings (env, e, ex)
    | _ -> [req]
    end
  | Pexp_variant (_, None) -> [req]
  | Pexp_variant (cn, Some e) ->
    let hash = Hashtbl.hash cn in
    begin match value.v_ with
    | Constructor (ex_ctor_name, d_ex, Some ex) when ex_ctor_name = cn && d_ex = hash ->
      push_down_req fillings (env, e, ex)
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
          push_down_req fillings (env, field_exp, !expected_ref)
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
            push_down_req fillings (env, field_exp, !expected_ref)
          end in
        let base_rec_push_downs =
          push_down_req fillings (env, base_rec_exp, base_ex) in
          lit_push_downs @ base_rec_push_downs
      | _ -> [req]
      end
    | _ -> [req]
    end
  | Pexp_field (e, { txt = lident; _ }) ->
    let label = lident_name lident in
    let record_ex = new_vtrace @@ Record (SMap.singleton label (ref value)) in
    push_down_req fillings (env, e, record_ex)
  | Pexp_setfield (_, _, _) -> [req]
  | Pexp_array exps ->
    begin match value.v_ with
    | Array v_arr when List.length exps = Array.length v_arr ->
      List.map2 (fun e v -> push_down_req fillings (env, e, v)) exps (Array.to_list v_arr)
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
    push_down_req fillings (nenv, e, value)
  | Pexp_letmodule (name, me, e) ->
    (* Will this mutate? :/ *)
    let m = eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me in
    let env' = Envir.env_set_module name.txt m env in
    push_down_req fillings (env', e, value)
  | Pexp_assert _ -> [req]
  | Pexp_lazy _ -> [req]
  | Pexp_poly (e, _) -> push_down_req fillings (env, e, value)
  | Pexp_newtype (_, e) -> push_down_req fillings (env, e, value)
  | Pexp_open (_, lident, e) ->
    let nenv =
      match Envir.env_get_module_data env lident with
      | exception Not_found ->
        (* Module might be a .mli only *)
        env
      | module_data -> Envir.env_extend false env module_data
    in
    push_down_req fillings (nenv, e, value)
  | Pexp_object _ -> [req]
  | Pexp_pack _ -> [req]
  | Pexp_extension _ -> [req]


exception ReqsSatisfied of fillings

let terms_of_size _names_in_env n =
  match n with
  | 1 ->
    List.init 11 (fun x -> Exp.int_lit (x - 5)) (* -5 to 5 *)
    |> List.to_seq
  | _ -> Seq.empty


(* Preconditions: hole_reqs should (a) be non-empty and (b) be all on the same hole *)
let guess size fillings (hole_reqs : req list) =
  let (env1, { pexp_loc = hole_loc; _ }, _) = List.hd hole_reqs in
  let names_in_env = env1.values |> SMap.bindings |>@& (fun (name, v) -> match v with (_, Value _) -> Some name | _ -> None) in
  let eval fillings env exp =
    try Eval.eval_expr fillings Primitives.prims env (fun _ -> None) Trace.new_trace_state (-1) exp
    with _ -> new_vtrace Bomb in
  try
    terms_of_size names_in_env size
    |> Seq.iter begin fun term ->
      let fillings' = Loc_map.add hole_loc term fillings in
      if hole_reqs |> List.for_all (fun (env, exp, expected) -> Assert_comparison.values_equal_for_assert (eval fillings' env exp) expected)
      then raise (ReqsSatisfied fillings')
    end;
    None
  with ReqsSatisfied fillings' -> Some fillings'


let fill_holes parsed fillings reqs : expression Loc_map.t =
  let is_hole { pexp_desc; _ } = match pexp_desc with Pexp_ident { txt = Longident.Lident "??"; _ } -> true | _ -> false in
  let hole_locs =
    (Exp.all parsed @ (Loc_map.bindings fillings |>@ snd |>@@ Exp.flatten))
    |>@? is_hole |>@ Exp.loc |> List.dedup in
  let try_fill_hole fillings hole_loc =
    let reqs_on_hole = reqs |>@? (fun (_, exp, _) -> Exp.loc exp = hole_loc) in
    if reqs_on_hole = [] then fillings else
    let rec guess_up_to_size max_size size =
      begin match guess size fillings reqs with
      | Some fillings' -> fillings'
      | None           -> if size < max_size then guess_up_to_size max_size (size + 1) else fillings
      end in
    guess_up_to_size 1 1
  in
  List.fold_left try_fill_hole fillings hole_locs


let results ?(fillings = Loc_map.empty) parsed _trace assert_results _lookup_exp_typed =
  let reqs =
    assert_results
    |>@& assert_result_to_req fillings in
  let go fillings = fill_holes parsed fillings reqs in
  let fillings' = fillings |> go |> go |> go |> go |> go |> go |> go |> go |> go |> go in
  (* Fill holes until fixpoint or bored. *)
  parsed
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> apply_fillings fillings'
  |> fun x -> [x]

