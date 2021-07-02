open Camlboot_interpreter
open Camlboot_interpreter.Data
open Parsetree
open Shared
open Shared.Ast
open Shared.Util


module SSet = Set.Make(String)

type fillings = expression Loc_map.t

(* Does not recursively apply fillings. That might result in an infinite loop. *)
let apply_fillings fillings prog =
  Loc_map.bindings fillings
  |> List.fold_left (fun prog (loc, exp) -> Exp.replace loc exp prog) prog


(* Constraints/examples. But "constraint" is an OCaml keyword, so let's call them "req"s *)
type req = Data.env * expression * value

let string_of_req (_env, exp, value) =
  Exp.to_string exp ^ " = " ^ Formatter_to_stringifier.f pp_print_value value


let dont_care = new_vtrace ExDontCare

let eval_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no exp =
  Eval.with_fuel 100 begin fun () ->
    try Eval.eval_expr fillings prims env lookup_exp_typed trace_state frame_no exp
    with _ -> new_vtrace Bomb
  end (fun () -> new_vtrace Bomb)

let pattern_bind_fueled fillings prims env lookup_exp_typed trace_state frame_no root_v path p v =
  Eval.with_fuel 100 begin fun () ->
    Eval.pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_v path p v
  end (fun () -> raise Eval.Match_fail)

let eval_module_exp_fueled fillings prims env lookup_exp_typed trace_state frame_no mod_exp =
  Eval.with_fuel 100 begin fun () ->
    Some (Eval.eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no mod_exp)
  end (fun () -> None)

let eval fillings env exp =
  eval_exp_fueled fillings Primitives.prims env (fun _ -> None) Trace.new_trace_state (-1) exp

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
let assert_result_to_req assert_result : req option =
  let fillings, prims, lookup_exp_typed, trace_state, frame_no = Loc_map.empty, Primitives.prims, (fun _ -> None), Trace.new_trace_state, -1 in
  match assert_result.f.v_ with
  | Fun (Asttypes.Nolabel, None, pat, body_exp, env_ref) ->
    let arg = assert_result.arg in
    let env' = pattern_bind_fueled fillings prims !env_ref lookup_exp_typed trace_state frame_no arg [] pat arg in
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
let rec push_down_req lookup_exp_typed fillings ((env, exp, value) as req) : req list =
  let open Eval in
  let recurse = push_down_req lookup_exp_typed fillings in
  let prims, lookup_exp_typed, trace_state, frame_no = Primitives.prims, (fun _ -> None), Trace.new_trace_state, -1 in
  let try_cases = try_cases fillings prims env lookup_exp_typed trace_state frame_no in
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
        | [vb] ->
          let req_env = if recflag = Asttypes.Recursive then env' else env in
          let new_ex = expand_named_example_to_pat req_env name value vb.pvb_pat in
          recurse (req_env, vb.pvb_expr, new_ex)
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
      | Some (env', branch_exp) -> recurse (env', branch_exp, expected)
      end
    | _ ->
      [req]
    end
  | Pexp_fun (Nolabel, None, arg_pat, body_exp) ->
    begin match value.v_ with
    | ExCall (arg, expected) -> begin try
        let env' = pattern_bind_fueled fillings prims env lookup_exp_typed trace_state frame_no arg [] arg_pat arg in
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
    if target_loc = target_loc then raise (Found_names !names);
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
    print_endline @@ "nonconstant_names_at_loc: " ^ String.concat ", " names;
    SSet.of_seq (List.to_seq names)


exception ReqsSatisfied of (expression -> Typedtree.expression option) * fillings

let terms_of_size _names_in_env n =
  match n with
  | 1 ->
    List.init 11 (fun x -> Exp.int_lit (x - 5)) (* -5 to 5 *)
    |> List.to_seq
  | _ -> Seq.empty


let is_req_satisified_by fillings (env, exp, expected) =
  (* begin try Loc_map.bindings fillings |>@ snd |>@ Exp.to_string |> List.iter print_endline
  with _ -> Loc_map.bindings fillings |>@ snd |>@ (Formatter_to_stringifier.f (Printast.expression 0)) |> List.iter print_endline
  end; *)
  Assert_comparison.values_equal_for_assert (eval fillings env exp) expected


(* Still need to search env for constructors *)


let is_tconstr_with_path target_path typ =
  match typ.Types.desc with
  | Types.Tconstr (path, _, _) -> path = target_path
  | _ -> false

let is_unit_type = is_tconstr_with_path Predef.path_unit
let rec is_var_type typ = match typ.Types.desc with
  | Types.Tvar _
  | Types.Tunivar _ -> true
  | Types.Tlink t
  | Types.Tsubst t -> is_var_type t
  | _ -> false
let rec is_arrow_type typ = match typ.Types.desc with
  | Types.Tarrow _ -> true
  | Types.Tlink t
  | Types.Tsubst t -> is_arrow_type t
  | _ -> false



let ints_seq = List.to_seq @@ List.init 21 (fun x -> Exp.int_lit (x - 10)) (* -10 to 10 *)
let strings_seq = List.to_seq @@ [Exp.string_lit ""]

let is_channel typ =
  match typ.Types.desc with
  | Types.Tconstr (Path.Pdot (_, "in_channel",  _), [], _) -> true
  | Types.Tconstr (Path.Pdot (_, "out_channel", _), [], _) -> true
  | _ -> false

(* Estimate which functions are imperative. *)
let is_imperative typ =
  let flat = Type.flatten_arrows typ in
  let ret_t = List.last flat in
  is_unit_type ret_t ||
  (is_unit_type (List.hd flat) && List.length flat = 2) ||
  List.exists is_channel flat ||
  match ret_t.desc with
  | Types.Tvar (Some name) ->
    Type.flatten typ |> List.exists (function { Types.desc = Types.Tvar (Some name2); _ } -> name = name2 | _ -> false)
  | _ -> false

let unimplemented_prim_names = SSet.of_seq (List.to_seq ["**"; "abs_float"; "acos"; "asin"; "atan"; "atan2"; "ceil"; "copysign"; "cos"; "cosh"; "exp"; "expm1"; "floor"; "hypot"; "ldexp"; "mod_float"; "sin"; "sinh"; "~-."; "sqrt"; "log"; "log10"; "log1p"; "tan"; "tanh"])
let dont_bother_names = SSet.of_seq (List.to_seq ["__POS__"; "__POS_OF__"; "__MODULE__"; "__LOC__"; "__LOC_OF__"; "__LINE__"; "__LINE_OF__"; "__FILE__"])

let constants_at_type_seq nonconstant_names tenv typ =
  let lits_seq =
    match (Type.regular typ).desc with
    | Types.Tvar _                                              -> Seq.append ints_seq strings_seq
    | Types.Tconstr (path, _, _) when path = Predef.path_bool   -> Seq.empty (* the true and false constructors should be in the type env...once we handle constructors *)
    | Types.Tconstr (path, _, _) when path = Predef.path_int    -> ints_seq
    | Types.Tconstr (path, _, _) when path = Predef.path_string -> strings_seq
    | Types.Tconstr (_,    _, _)                                -> Seq.empty

    | Types.Ttuple _ -> Seq.empty
    | Types.Tfield (_, _, _, _) -> Seq.empty
    | Types.Tarrow (_, _, _, _) -> Seq.empty

    | Types.Tobject (_, _)
    | Types.Tnil
    | Types.Tvariant _
    | Types.Tunivar _
    | Types.Tpoly (_, _)
    | Types.Tpackage (_, _, _) -> Seq.empty

    | Types.Tlink _
    | Types.Tsubst _ -> assert false (* Type.regular already traversed these *)
  in
  let idents_at_type_seq () = (* May be a way to cache this for deeper lookups *)
    let target_is_var = is_var_type typ in
    let f name _path desc out =
      if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
      if SSet.mem name unimplemented_prim_names then out else (* Interpreter doesn't implement some primitives *)
      if SSet.mem name dont_bother_names then out else
      if SSet.mem name nonconstant_names then out else
      if target_is_var && is_arrow_type desc.Types.val_type then out else (* Don't use unapplied functions at type 'a *)
      if Type.does_unify desc.Types.val_type typ
      then Exp.simple_var name :: out
      else out
    in
    Env.fold_values f None(* not looking in a nested module *) tenv []
    |> List.to_seq
  in
  (* Try to avoid unnecessary type unification if we don't get that far in the sequence. *)
  Seq.append_lazy lits_seq idents_at_type_seq



let rec nonconstants_at_type_seq depth_limit nonconstant_names (tenv : Env.t) (typ : Types.type_expr) =
  if depth_limit <= 0 then Seq.empty else
  let idents_at_type_seq = (* May be a way to cache this for deeper lookups *)
    let target_is_var = is_var_type typ in
    let f name _path desc out =
      if not (SSet.mem name nonconstant_names) then out else
      if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
      if SSet.mem name unimplemented_prim_names then out else (* Interpreter doesn't implement some primitives *)
      if SSet.mem name dont_bother_names then out else
      if target_is_var && is_arrow_type desc.Types.val_type then out else (* Don't use unapplied functions at type 'a *)
      if Type.does_unify desc.Types.val_type typ
      then Exp.simple_var name :: out
      else out
    in
    Env.fold_values f None(* not looking in a nested module *) tenv []
    |> List.to_seq
  in
  let applys_seq () =
    (* START HERE producing a wild mess of failures *)
    (* Returns list of arg types needed. *)
    let rec can_produce_typ ret_t =
      let ret_t = Type.regular ret_t in
      if Type.does_unify ret_t typ && (* no partial applications at type 'a *) not (is_var_type typ && is_arrow_type ret_t) then
        Some []
      else
        match ret_t.desc with
        | Types.Tarrow (Asttypes.Nolabel, arg_t, ret_t, _) -> can_produce_typ ret_t |>& List.cons arg_t
        | _ -> None
    in
    let f name _path desc out =
      if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
      if SSet.mem name unimplemented_prim_names then out else (* Interpreter doesn't implement some primitives *)
      if SSet.mem name dont_bother_names then out else
      match (Type.regular desc.Types.val_type).desc with
      | Types.Tarrow (Asttypes.Nolabel, arg_t, ret_t, _) ->
        begin match can_produce_typ ret_t |>& List.cons arg_t with
        | Some arg_types_needed -> (name, arg_types_needed) :: out
        | None -> out
        end
      | _ -> out
    in
    Env.fold_values f None(* not looking in a nested module *) tenv []
    |> List.to_seq
    |> Seq.flat_map begin fun (name, arg_types_needed) ->
      (* print_endline name; *)
      (* print_endline @@ String.concat ", " (arg_types_needed |>@ Type.to_string); *)
      match arg_types_needed with
      | [] -> assert false
      | [t1] ->
        nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t1
        |> Seq.map (fun arg -> Exp.apply (Exp.simple_var name) [(Asttypes.Nolabel, arg)])
      | [t1; t2] ->
        let nonconstants_at_t1 = nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t1 in
        let nonconstants_at_t2 = nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t2 in
        let constants_at_t1    = constants_at_type_seq                    nonconstant_names tenv t1 in
        let constants_at_t2    = constants_at_type_seq                    nonconstant_names tenv t2 in
        [ [nonconstants_at_t1; nonconstants_at_t2]
        ; [nonconstants_at_t1; constants_at_t2]
        ; [constants_at_t1;    nonconstants_at_t2]
        ]
        |> List.to_seq
        |> Seq.flat_map begin fun combo ->
          Seq.cart_prod combo
          |> Seq.map (fun args -> Exp.apply (Exp.simple_var name) (args |>@ fun arg -> (Asttypes.Nolabel, arg)))
        end
      | [t1; t2; t3] ->
        let nonconstants_at_t1 = nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t1 in
        let nonconstants_at_t2 = nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t2 in
        let nonconstants_at_t3 = nonconstants_at_type_seq (depth_limit-1) nonconstant_names tenv t3 in
        let constants_at_t1    = constants_at_type_seq                    nonconstant_names tenv t1 in
        let constants_at_t2    = constants_at_type_seq                    nonconstant_names tenv t2 in
        let constants_at_t3    = constants_at_type_seq                    nonconstant_names tenv t3 in
        [ [nonconstants_at_t1; nonconstants_at_t2; nonconstants_at_t3]
        ; [constants_at_t1;    nonconstants_at_t2; nonconstants_at_t3]
        ; [nonconstants_at_t1; constants_at_t2;    nonconstants_at_t3]
        ; [nonconstants_at_t1; nonconstants_at_t2; constants_at_t3]
        ; [constants_at_t1;    constants_at_t2;    nonconstants_at_t3]
        ; [constants_at_t1;    nonconstants_at_t2; constants_at_t3]
        ; [nonconstants_at_t1; constants_at_t2;    constants_at_t3]
        ]
        |> List.to_seq
        |> Seq.flat_map begin fun combo ->
          Seq.cart_prod combo
          |> Seq.map (fun args -> Exp.apply (Exp.simple_var name) (args |>@ fun arg -> (Asttypes.Nolabel, arg)))
        end
      | _ -> Seq.empty (* Don't guess applies with more than 3 args. *)
    end
  in
  (* Try to avoid unnecessary type unification if we don't get that far in the sequence. *)
  Seq.append_lazy idents_at_type_seq applys_seq

let terms_tested_count = ref 0

(* let names_in_env = env1.values |> SMap.bindings |>@& (fun (name, v) -> match v with (_, Value _) -> Some name | _ -> None) in *)
let hole_fillings_seq lookup_exp_typed fillings hole_loc reqs_on_hole prog : ((Loc.t -> Typedtree.expression option) * fillings) Seq.t =
  let terms_seq =
    (* let nonconstant_names = SSet.empty in *)
    let nonconstant_names = nonconstant_names_at_loc hole_loc (apply_fillings fillings prog) in
    match Eval.lookup_type_opt lookup_exp_typed hole_loc with
    | Some typ ->
      let tenv = Eval.lookup_type_env lookup_exp_typed hole_loc in
      Seq.append (constants_at_type_seq nonconstant_names tenv typ) (nonconstants_at_type_seq 3 nonconstant_names tenv typ)
    | _ -> Seq.empty
  in
  terms_seq
  |> Seq.filter begin fun term ->
    (* Printast.expression 0 Format.std_formatter term; *)
    let fillings = Loc_map.add hole_loc term fillings in
    incr terms_tested_count;
    if !terms_tested_count mod 10_000 = 0 then print_endline (string_of_int !terms_tested_count ^ "\t" ^ Exp.to_string term);
    reqs_on_hole |> List.for_all (is_req_satisified_by fillings)
  end
  |> Seq.filter_map begin fun term ->
    (* Mess to keep track of types in the new term. *)
    (* Also, we don't (yet) keep track of type vars between terms, so there can be some incompatibilites caught here. (incompatibiliies between holes will not be caught until execution failure later) *)
    (* print_endline @@ "Typing " ^ Exp.to_string term; *)
    let term = Exp.freshen_locs term in
    let fillings = Loc_map.add hole_loc term fillings in
    try
      let locmap = term |> Typing.loc_to_type_of_expression (Eval.lookup_type_env lookup_exp_typed hole_loc) in
      let lookup_exp_typed =
        begin fun loc ->
        match Loc_map.all_at_loc loc locmap with
        | []       -> lookup_exp_typed loc (* default to exising lookup in the rest of the file *)
        | [tt_exp] -> Some tt_exp
        | _        -> print_endline @@ "multiple typedtree nodes at loc " ^ Loc.to_string loc; None
        end
      in
      Some (lookup_exp_typed, fillings)
    with _ ->
      (* print_endline @@ "typing failure in hole_fillings_seq: " ^ (try Exp.to_string term with _ -> Formatter_to_stringifier.f (Printast.expression 0) term); *)
      (* failwith "yolo"; *)
      None
  end


let fill_holes parsed lookup_exp_typed fillings reqs prog =
  let is_hole { pexp_desc; _ } = match pexp_desc with Pexp_ident { txt = Longident.Lident "??"; _ } -> true | _ -> false in
  let hole_locs =
    (Exp.all parsed @ (Loc_map.bindings fillings |>@ snd |>@@ Exp.flatten))
    |>@? is_hole |>@ Exp.loc |> List.dedup in
  let rec fillings_seq lookup_exp_typed fillings hole_locs : ((Loc.t -> Typedtree.expression option) * fillings) Seq.t =
    match hole_locs with
    | [] -> Seq.return (lookup_exp_typed, fillings)
    | hole_loc::rest ->
      fillings_seq lookup_exp_typed fillings rest
      |> Seq.flat_map begin function (lookup_exp_typed, fillings) ->
        let reqs' = reqs |>@@ push_down_req lookup_exp_typed fillings in
        let reqs_on_hole = reqs' |>@? (fun (_, exp, _) -> Exp.loc exp = hole_loc) in
        hole_fillings_seq lookup_exp_typed fillings hole_loc reqs_on_hole prog
      end
  in
  fillings_seq lookup_exp_typed fillings hole_locs
  (* Some reqs may not be pushed down to holes, so we need to verify them too. *)
  |> Seq.filter begin function (_lookup_exp_typed, fillings) ->
    reqs |> List.for_all (is_req_satisified_by fillings)
  end
  (* Return first valid filling. *)
  |> begin fun seq ->
    match seq () with
    | Seq.Nil -> None
    | Seq.Cons ((lookup_exp_typed, fillings), _) -> Some (lookup_exp_typed, fillings)
  end

  (* let try_fill_hole (lookup_exp_typed, fillings) hole_loc =
    (* reqs_on_hole |> List.iter (string_of_req %> print_endline); *)
    if reqs_on_hole = [] then (lookup_exp_typed, fillings) else
    let rec guess_up_to_size max_size size =
      begin match guess lookup_exp_typed fillings size reqs_on_hole with
      | Some (lookup_exp_typed', fillings') -> (lookup_exp_typed', fillings')
      | None           -> if size < max_size then guess_up_to_size max_size (size + 1) else (lookup_exp_typed, fillings)
      end in
    guess_up_to_size 1 1
  in
  List.fold_left try_fill_hole (lookup_exp_typed, fillings) hole_locs *)


let results ?(fillings = Loc_map.empty) parsed _trace assert_results lookup_exp_typed =
  let reqs =
    assert_results
    |>@& assert_result_to_req in
  (* print_string "Req "; *)
  (* reqs |> List.iter (string_of_req %> print_endline); *)
  match fill_holes parsed lookup_exp_typed fillings reqs parsed with
  | exception _ -> print_endline "synth exception"; Printexc.print_backtrace stdout; []
  | None -> print_endline "synth failed"; [parsed]
  | Some (_, fillings') ->
    print_endline "synth success";
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


