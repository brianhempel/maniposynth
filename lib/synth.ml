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
  let prims, trace_state, frame_no = Primitives.prims, Trace.new_trace_state, -1 in
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

let exp_size exp =
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
  iter.expr iter exp;
  !size

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

type hole_synth_env =
    { tenv              : Env.t
    ; hole_type         : Types.type_expr
    ; user_ctors        : (Longident.t * Types.constructor_description * lprob) list
    ; nonconstant_names : SSet.t
    ; local_idents      : (expression * Types.type_expr * lprob) list
    }
(* type hole_synth_env =
    { nonconstant_names                : SSet.t
    ; tenv                             : Env.t
    ; mutable constants_at_t           : (Types.type_expr * (expression * Types.type_expr) Seq.t) list
    ; mutable nonconstants_at_t        : (Types.type_expr * (expression * Types.type_expr) Seq.t) list
    ; mutable funcs_that_can_produce_t : (Types.type_expr * (Types.type_expr (* func type, already unified with the ret type *) * (int (* number of arguments needed *) * string list ref (* function names at that type *))) Seq.t) list
    } *)

(* let new_hole_synth_env nonconstant_names tenv =
  (* print_endline "------------------------------ new synth env ------------------------------"; *)
  { nonconstant_names        = nonconstant_names
  ; tenv                     = tenv
  ; constants_at_t           = []
  ; nonconstants_at_t        = []
  ; funcs_that_can_produce_t = []
  } *)

let is_req_satisified_by fillings (env, exp, expected) =
  (* begin try Loc_map.bindings fillings |>@ snd |>@ Exp.to_string |> List.iter print_endline
  with _ -> Loc_map.bindings fillings |>@ snd |>@ (Formatter_to_stringifier.f (Printast.expression 0)) |> List.iter print_endline
  end; *)
  (* print_endline @@ string_of_req (env, exp, expected); *)
  let evaled = eval fillings env exp in
  (* print_endline @@ Formatter_to_stringifier.f pp_print_value evaled; *)
  Assert_comparison.values_equal_for_assert evaled expected


(* Still need to search env for constructors *)


(* Based on the corpus in synth_stats_model *)
(* let corpus_ints_90th_percentile = [0; 1; 2; 8; -1; 3; 4; 5; 10; 7; 16; 17; 255] *)
(* let ints = corpus_ints_90th_percentile |>@ (fun int -> (Exp.int_lit int, Predef.type_int)) *)
(* let ints = [(Exp.int_lit 0, Predef.type_int); (Exp.int_lit 1, Predef.type_int)] *)
(* let strings = [(Exp.string_lit "", Predef.type_string)] *)

let is_channel typ =
  match (Type.regular typ).Types.desc with
  | Types.Tconstr (Path.Pdot (_, "in_channel",  _), [], _) -> true
  | Types.Tconstr (Path.Pdot (_, "out_channel", _), [], _) -> true
  | _ -> false

(* Estimate which functions are imperative. *)
let is_imperative typ =
  let flat = Type.flatten_arrows typ in
  let ret_t = List.last flat in
  Type.is_unit_type ret_t ||
  (Type.is_unit_type (List.hd flat) && List.length flat = 2) ||
  List.exists is_channel flat ||
  (* If output is a type var, make sure one of the inputs is the same *)
  match (Type.regular ret_t).desc with
  | Types.Tvar (Some name) ->
    Type.flatten typ |> List.exists (function { Types.desc = Types.Tvar (Some name2); _ } -> name = name2 | _ -> false)
  | _ -> false

let unimplemented_prim_names = SSet.of_list ["**"; "abs_float"; "acos"; "asin"; "atan"; "atan2"; "ceil"; "copysign"; "cos"; "cosh"; "exp"; "expm1"; "floor"; "hypot"; "ldexp"; "mod_float"; "sin"; "sinh"; "~-."; "sqrt"; "log"; "log10"; "log1p"; "tan"; "tanh"; "frexp"; "classify_float"; "modf"]
let dont_bother_names = SSet.of_list ["__POS__"; "__POS_OF__"; "__MODULE__"; "__LOC__"; "__LOC_OF__"; "__LINE__"; "__LINE_OF__"; "__FILE__"; "??"; "~+"; ">"; ">="] (* Don't bother with > and >= because will already guess < and <= *)
(* Based on the corpus in synth_stats_model *)
let corpus_pervasives_names_99_percentile = SSet.of_list ["!"; "="; ":="; "raise"; "ref"; "&&"; "+"; "not"; "-"; "<>"; "||"; "^"; "exp"; "@"; "<"; ">"; ">="; "*"; "incr"; "<="; "=="; "fst"; "compare"; "ignore"; "snd"; "string_of_int"; "output_string"; "~-"; "close_in"; "/"; "lsl"; "max"; "exit"; "|>"; "prerr_endline"; "max_int"; "min"; "output_char"; "min_int"; "!="; "print_string"; "land"; "mod"; "input_value"; "asr"; "decr"; "float_of_string"; "stdout"; "open_in_bin"; "really_input_string"; "@@"; "failwith"; "float_of_int"; "log"; "lor"; "output_value"; "succ"; "close_out"; "pred"; "prerr_string"; "+."; "stderr"; "lxor"; "*."; "-."; "/."; "int_of_string"]
let uncommon_names = SSet.diff Name.pervasives_value_names corpus_pervasives_names_99_percentile
let names_to_skip = SSet.union_all [unimplemented_prim_names; dont_bother_names; uncommon_names]






(* let constants_at_type_seq hole_synth_env typ =
  match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.constants_at_t with
  | Some seq -> seq
  | None ->
    (*
    print_endline @@ "Recomputing constants at " ^ Type.to_string typ(*  ^ "\n" ^ Type.to_string_raw typ ^ "\n" *);
    *)
    (* ignore (List.assoc_by_opt (Type.equal_ignoring_id_and_scope ~show:true typ) hole_synth_env.constants_at_t); *)
    (* print_endline (fst (List.split hole_synth_env.constants_at_t) |>@ Type.to_string_raw |> String.concat ", "); *)
    let lits =
      match (Type.regular typ).desc with
      | Types.Tvar _                                              -> ints @ strings
      | Types.Tconstr (path, _, _) when path = Predef.path_bool   -> [] (* the true and false constructors should be in the type env...once we handle constructors *)
      | Types.Tconstr (path, _, _) when path = Predef.path_int    -> ints
      | Types.Tconstr (path, _, _) when path = Predef.path_string -> strings
      | Types.Tconstr (_,    _, _)                                -> []

      | Types.Ttuple _ -> []
      | Types.Tfield (_, _, _, _) -> []
      | Types.Tarrow (_, _, _, _) -> []

      | Types.Tobject (_, _)
      | Types.Tnil
      | Types.Tvariant _
      | Types.Tunivar _
      | Types.Tpoly (_, _)
      | Types.Tpackage (_, _, _) -> []

      | Types.Tlink _
      | Types.Tsubst _ -> assert false (* Type.regular already traversed these *)
    in
    let idents_at_type =
      let f name _path desc out =
        let target_is_var = Type.is_var_type typ in
        if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
        if SSet.mem name names_to_skip then out else
        if SSet.mem name hole_synth_env.nonconstant_names then out else
        if target_is_var && Type.is_arrow_type desc.Types.val_type then out else (* Don't use unapplied functions at type 'a *)
        match Type.unify_opt desc.Types.val_type typ with
        | Some type' -> (Exp.simple_var name, type') :: out
        | None -> out
      in
      Env.fold_values f None(* not looking in a nested module *) hole_synth_env.tenv []
    in
    let ctors_at_type =
      let f {Types.cstr_name; cstr_arity; cstr_res; _} out =
        if cstr_arity <> 0 then out else (* For constants, we only want arg-less ctors (because OCaml doesn't even allow partial application of ctors). *)
        if Type.is_exn_type cstr_res then out else (* Exclude exceptions. *)
        match Type.unify_opt cstr_res typ with
        | Some type' -> (Exp.construct (Longident.lident cstr_name) None, type') :: out
        | None -> out
      in
      Env.fold_constructors f None(* not looking in a nested module *) hole_synth_env.tenv []
    in
    let seq = List.to_seq (lits @ idents_at_type @ ctors_at_type) in
    hole_synth_env.constants_at_t <- hole_synth_env.constants_at_t @ [(typ, seq)];
    seq *)

(* let rec nonconstants_at_type_seq size_limit hole_synth_env (typ : Types.type_expr) =
  if size_limit <= 0 || SSet.is_empty hole_synth_env.nonconstant_names then Seq.empty else
  let idents_at_type_seq =
    match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.nonconstants_at_t with
    | Some seq -> seq
    | None ->
      (* print_endline @@ "Recomputing nonconstants at " ^ Type.to_string typ; *)
      let target_is_var = Type.is_var_type typ in
      let f name _path desc out =
        if not (SSet.mem name hole_synth_env.nonconstant_names) then out else
        if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
        if SSet.mem name names_to_skip then out else
        if target_is_var && Type.is_arrow_type desc.Types.val_type then out else (* Don't use unapplied functions at type 'a *)
        match Type.unify_opt desc.Types.val_type typ with
        | Some type' -> (Exp.simple_var name, type') :: out
        | None -> out
      in
      let seq =
        Env.fold_values f None(* not looking in a nested module *) hole_synth_env.tenv []
        (* |> (fun names -> print_endline @@ String.concat " " (names |>@ Exp.to_string); names) *)
        |> List.to_seq
      in
      hole_synth_env.nonconstants_at_t <- hole_synth_env.nonconstants_at_t @ [(typ, seq)];
      seq
  in
  let applys_seq () =
    if size_limit <= 2 then Seq.empty else
    let func_types_seq =
      match List.assoc_by_opt (Type.equal_ignoring_id_and_scope typ) hole_synth_env.funcs_that_can_produce_t with
      | Some func_types -> func_types
      | None ->
        (* print_endline @@ "Recomputing possible funcs/ctors at " ^ Type.to_string typ; *)
        let rec can_produce_typ t = (* Returns number of args and func type unified with the desired return type. Need to explicitly remember number of args in case desired return type is an arrow. *)
          let t = Type.regular t in
          let try_right () =
            begin match t.desc with
            | Types.Tarrow (Asttypes.Nolabel, _, t_r, _) ->
              can_produce_typ t_r
              |>&& begin fun (arg_count, t_r') ->
                Type.(unify_mutating_opt (copy t) (arrow (new_var ()) t_r'))
                |>& (fun t' -> (arg_count + 1, t'))
              end
            | _ -> None
            end
          in
          begin match Type.unify_opt t typ with
          | Some t ->
            if not (Type.is_var_type typ && Type.is_arrow_type t) (* no partial applications at type 'a *)
            then Some (0, t)
            else try_right ()
          | None -> try_right ()
          end
        in
        let values_folder name _path desc out =
          if is_imperative desc.Types.val_type then out else (* Don't use imperative functions *)
          if SSet.mem name names_to_skip then out else
          let name_type = Type.regular desc.Types.val_type in
          match name_type.desc with
          | Types.Tarrow (Asttypes.Nolabel, _arg_t, t_r, _) ->
            begin match can_produce_typ t_r with
            | Some (arg_count, t_r_unified_with_goal_ret_t) ->
              Type.(unify_mutating_opt (copy name_type) (arrow (new_var ()) t_r_unified_with_goal_ret_t))
              |>& (fun name_type' -> (* print_endline (name ^ " : " ^ Type.to_string name_type' ^ " for " ^ Type.to_string typ); *) (name, arg_count + 1, name_type') :: out )
              ||& out
            | _ -> out
            end
          | _ -> out
        in
        let ctors_folder {Types.cstr_name; cstr_arity; cstr_args; cstr_res; _} out =
          if cstr_arity = 0 then out else
          if Type.is_exn_type cstr_res then out else (* Exclude exceptions. *)
          (* Pretend ctors are arrows to reuse logic above (and below) *)
          let ctor_type_as_arrows = Type.unflatten_arrows (cstr_args @ [cstr_res]) in
          (* print_endline @@ cstr_name ^ " : " ^ Type.to_string ctor_type_as_arrows ^ " vs " ^ Type.to_string_raw typ; *)
          begin match can_produce_typ ctor_type_as_arrows with
          | Some (arg_count, ctor_type_as_arrows_unified_with_goal_ret_t) ->
            (* print_endline cstr_name; *)
            if arg_count <> cstr_arity then out else (* Ctors must always be fully applied *)
            (cstr_name, cstr_arity, ctor_type_as_arrows_unified_with_goal_ret_t) :: out
          | None -> out
          end
        in
        let func_types_seq =
          let list_of_name_args_func_type1 : (string * int * Types.type_expr) list =
            Env.fold_values values_folder None(* not looking in a nested module *) hole_synth_env.tenv [] in
          let list_of_name_args_func_type2 : (string * int * Types.type_expr) list =
            Env.fold_constructors ctors_folder None(* not looking in a nested module *) hole_synth_env.tenv [] in
          let gather (name, arg_count, func_type) out : (Types.type_expr * (int * string list ref)) list =
            match List.assoc_by_opt (Type.equal_ignoring_id_and_scope func_type) out with
            | None -> (func_type, (arg_count, ref [name])) :: out
            | Some (_, names_ref) -> names_ref := name :: !names_ref; out
          in
          List.fold_right gather (list_of_name_args_func_type1 @ list_of_name_args_func_type2) []
          |> List.to_seq
        in
        hole_synth_env.funcs_that_can_produce_t <- hole_synth_env.funcs_that_can_produce_t @ [(typ, func_types_seq)];
        func_types_seq
    in
    func_types_seq
    |> Seq.flat_map begin fun (func_type, (arg_count, names_ref)) ->
      if 2 + arg_count > size_limit then Seq.empty else
      let rec args_seq size_limit arg_count arg_i_to_unify non_constant_used func_type =
        if arg_count <= 0 then Seq.return ([], func_type) else
        if size_limit <= 0 then (failwith "shouldn't happen. term size math is precise elsewhere") else
        match Type.flatten_arrows func_type with
        | (_::_::_) as flat_type ->
          let arg_t = List.nth flat_type arg_i_to_unify in
          let seq1 =
            nonconstants_at_type_seq (size_limit-arg_count+1) hole_synth_env arg_t
            |> Seq.flat_map begin fun (arg, arg_t') ->
              let arg_size = exp_size arg in
              let func_type' = Type.unflatten_arrows @@ List.replace_nth arg_i_to_unify arg_t' flat_type in
              begin match Type.unify_opt func_type func_type' with
              | Some func_type'' ->
                args_seq (size_limit-arg_size) (arg_count-1) (arg_i_to_unify+1) true func_type''
                |> Seq.map (fun (args_r, func_type''') -> (arg::args_r, func_type'''))
              | None -> Seq.empty
              end
            end
          in
          let seq2 () =
            if arg_count = 1 && not non_constant_used then Seq.empty else
            constants_at_type_seq hole_synth_env arg_t
            |> Seq.flat_map begin fun (arg, arg_t') ->
              let func_type' = Type.unflatten_arrows @@ List.replace_nth arg_i_to_unify arg_t' flat_type in
              begin match Type.unify_opt func_type func_type' with
              | Some func_type'' ->
                args_seq (size_limit-1) (arg_count-1) (arg_i_to_unify+1) non_constant_used func_type''
                |> Seq.map (fun (args_r, func_type''') -> (arg::args_r, func_type'''))
              | None -> Seq.empty
              end
            end
          in
          Seq.append_lazy seq1 seq2
        | _ -> failwith "this shouldn't happen"
      in
      args_seq (size_limit-2) arg_count 0 false func_type
      |> Seq.flat_map begin fun (args, func_type) ->
        (* print_endline name;
        print_endline @@ Type.to_string func_type; *)
        let rec drop_n_args_from_arrow n typ =
          if n <= 0 then typ else
          begin match (Type.regular typ).desc with
          | Types.Tarrow (Asttypes.Nolabel, _, t_r, _) -> drop_n_args_from_arrow (n - 1) t_r
          | _                                          -> failwith "huuuuuuh?"
          end
        in
        let out_type = drop_n_args_from_arrow arg_count func_type in
        let arg_exps = args |>@ fun arg -> (Asttypes.Nolabel, arg) in
        let ctor_arg =
          if arg_count = 1
          then Some (List.hd args)
          else Some (Exp.tuple args)
        in
        let is_ctor_name name =
          let first_char = String.get name 0 in
          Char.is_capital first_char || name = "::"
        in
        !names_ref
        |>@ begin fun name ->
          if is_ctor_name name then
            (Exp.construct (Longident.lident name) ctor_arg, out_type)
          else
            (Exp.apply (Exp.simple_var name) arg_exps, out_type)
        end
        |> List.to_seq
      end
    end
  in
  (* Try to avoid unnecessary type unification if we don't get that far in the sequence. *)
  Seq.append_lazy idents_at_type_seq applys_seq
  (* idents_at_type_seq *)
 *)


(* let names_in_env = env1.values |> SMap.bindings |>@& (fun (name, v) -> match v with (_, Value _) -> Some name | _ -> None) in *)
(* prog should already have fillings applied to it *)

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

let is_constant hole_synth_env exp =
  not (exp |> Exp.flatten |>@& Exp.simple_name |> List.exists (fun name -> SSet.mem name hole_synth_env.nonconstant_names))

(* arg_count_remaining and arg_i are separate, to support partial applications. *)
(* May be able to cache here (don't forget about lprob!) *)
let rec args_seq ~cant_be_constant hole_synth_env func_type arg_count_remaining arg_i min_lprob : (expression list * Types.type_expr * lprob) list =
  if arg_count_remaining <= 0 then (if cant_be_constant then [] else [([], func_type, lprob_1)]) else
  if min_lprob > lprob_1 then [] else
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
          cant_be_constant && is_constant hole_synth_env arg
        in
        args_seq ~cant_be_constant:remainder_cant_be_constant hole_synth_env func_type' (arg_count_remaining-1) (arg_i+1) (div_lprobs min_lprob lprob)
        |>@ (fun (args_r, func_type'', later_lprob) -> (arg::args_r, func_type'', mult_lprobs later_lprob lprob))
    end
  | _ -> failwith "this shouldn't happen"


and ctor_terms ~cant_be_constant hole_synth_env typ min_lprob (lid, { Types.cstr_res; cstr_args; cstr_arity; _ }, lprob) =
  (* print_endline @@ cstr_name ^ " " ^ string_of_float lprob; *)
  if min_lprob > lprob then [] else
  let ctor_type_as_arrows = Type.unflatten_arrows (cstr_args @ [cstr_res]) in
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
    []

and stdlib_ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  stdlib_ctors |>@@ ctor_terms ~cant_be_constant hole_synth_env typ min_lprob

and nonstdlib_ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  hole_synth_env.user_ctors |>@@ ctor_terms ~cant_be_constant hole_synth_env typ min_lprob

and ctors_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  List.concat
    [ stdlib_ctors_at_type     ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob stdlib_ctor_lprob)    |>@ Tup3.map_thd (mult_lprobs stdlib_ctor_lprob)
    ; nonstdlib_ctors_at_type  ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob nonstdlib_ctor_lprob) |>@ Tup3.map_thd (mult_lprobs nonstdlib_ctor_lprob)
    ]

and consts_at_type _hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  if Type.is_var_type typ then
    List.concat
      [ const_strs_1_char_or_less
      ; const_ints
      ; const_chars
      ; const_floats
      ]
  else
    if Type.is_string_type typ then const_strs_1_char_or_less else
    if Type.is_int_type    typ then const_ints   else
    if Type.is_char_type   typ then const_chars  else
    if Type.is_float_type  typ then const_floats else
    []

(* Apps are never constant—they require a non-constant arg *)
and apps_at_type hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  (* (hole_synth_env.local_idents @ stdlib_idents) *)
  (hole_synth_env.local_idents @ pervasives_pure_idents_only)
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
  end

and ites_at_type ~cant_be_constant _hole_synth_env _typ _min_lprob : (expression * Types.type_expr * lprob) list =
  let _ = cant_be_constant in []
  (* if min_lprob > lprob_1 then [] else *)


and idents_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  (* (hole_synth_env.local_idents @ stdlib_idents) *)
  begin if cant_be_constant then
    hole_synth_env.local_idents
    |>@? (fun (e, _, _) -> SSet.mem (Exp.simple_name e ||& "") hole_synth_env.nonconstant_names)
  else
    hole_synth_env.local_idents @ pervasives_pure_idents_only
  end
  |>@& begin fun (exp, ident_t, lprob) ->
    if lprob < min_lprob then None else
    Type.unify_opt ident_t typ
    |>& (fun t' -> (exp, t', lprob))
  end

and terms_at_type ~cant_be_constant hole_synth_env typ min_lprob : (expression * Types.type_expr * lprob) list =
  if min_lprob > lprob_1 then [] else
  let terms =
    if cant_be_constant then
      List.concat
        [ ctors_at_type  ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ctor_lprob)  |>@ Tup3.map_thd (mult_lprobs ctor_lprob)
        ; apps_at_type                     hole_synth_env typ (div_lprobs min_lprob app_lprob)   |>@ Tup3.map_thd (mult_lprobs app_lprob)
        ; ites_at_type   ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ite_lprob)   |>@ Tup3.map_thd (mult_lprobs ite_lprob)
        ; idents_at_type ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ident_lprob) |>@ Tup3.map_thd (mult_lprobs ident_lprob)
        ]
    else
      List.concat
        [ ctors_at_type  ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ctor_lprob)  |>@ Tup3.map_thd (mult_lprobs ctor_lprob)
        ; consts_at_type                   hole_synth_env typ (div_lprobs min_lprob const_lprob) |>@ Tup3.map_thd (mult_lprobs const_lprob)
        ; apps_at_type                     hole_synth_env typ (div_lprobs min_lprob app_lprob)   |>@ Tup3.map_thd (mult_lprobs app_lprob)
        ; ites_at_type   ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ite_lprob)   |>@ Tup3.map_thd (mult_lprobs ite_lprob)
        ; idents_at_type ~cant_be_constant hole_synth_env typ (div_lprobs min_lprob ident_lprob) |>@ Tup3.map_thd (mult_lprobs ident_lprob)
        ]
  in
  (* print_endline @@ "terms at " ^ Type.to_string typ ^ " lprob > " ^ string_of_float min_lprob; *)
  (* print_endline (terms |>@ Tup3.fst |>@ Exp.to_string |> String.concat "  "); *)
  terms

let hole_fillings_seq ~cant_be_constant (fillings, lprob) min_lprob hole_loc static_hole_type hole_synth_env _reqs_on_hole _prog : (fillings * lprob) Seq.t =
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
  terms_at_type ~cant_be_constant hole_synth_env static_hole_type term_min_lprob
  |>@ begin fun (term, _term_t, term_lprob) ->
    (* print_endline (string_of_int !terms_tested_count ^ "\t" ^ Exp.to_string term ^ "\t" ^ Type.to_string term_t ^ "\t" ^ Type.to_string static_hole_type); *)
    (* Printast.expression 0 Format.std_formatter term; *)
    let fillings = Loc_map.add hole_loc term fillings in
    (fillings, mult_lprobs term_lprob lprob)
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





let e_guess (fillings, lprob) max_lprob min_lprob lookup_exp_typed prog reqs file_name user_ctors : fillings Seq.t =
  (* Printast.structure 0 Format.std_formatter prog; *)
  let hole_locs = hole_locs prog fillings in
  let progs = apply_fillings_and_degeneralize_functions fillings lookup_exp_typed prog reqs in
  let prog_and_typed_progs =
    progs
    |>@ begin fun prog ->
      print_endline @@ "Typing " ^ StructItems.to_string prog ^ string_of_float min_lprob;
      let (typed_prog, _, _) =
        try Typing.typedtree_sig_env_of_parsed prog file_name
        with _ -> ({ Typedtree.str_items = []; str_type = []; str_final_env = Env.empty }, [], Env.empty)
                    (* print_endline @@ "Could not type program:\n" ^ StructItems.to_string prog; *)
      in
      (prog, typed_prog)
    end
  in
  let hole_locs_progs_and_synth_envs : (Location.t * (program * hole_synth_env) Seq.t) list =
    hole_locs
    |>@ begin fun hole_loc ->
      let progs_and_synth_envs =
        prog_and_typed_progs |>@@ begin fun (prog, typed_prog) ->
          match Typing.find_exp_by_loc hole_loc typed_prog with
          | None -> []
          | Some hole_typed_node ->
            (* let reqs' = reqs |>@@ push_down_req fillings in
            let reqs_on_hole = reqs' |>@? (fun (_, exp, _) -> Exp.loc exp = hole_loc) in *)
            (* print_endline @@ "Names at hole: " ^ String.concat "   " (hole_synth_env.local_idents |>@ fun (exp, typ, lprob) -> Exp.to_string exp ^ " : " ^ Type.to_string typ ^ " " ^ string_of_float lprob); *)
            [ ( prog
              , { tenv              = hole_typed_node.exp_env
                ; hole_type         = hole_typed_node.exp_type
                ; user_ctors        = user_ctors
                ; nonconstant_names = nonconstant_names_at_loc hole_loc prog
                ; local_idents      = local_idents_at_loc hole_loc hole_typed_node.exp_env prog
                }
              )
            ]
        end
      in
      (hole_loc, List.to_seq progs_and_synth_envs)
    end
  in
  (* print_endline (hole_locs |>@ Loc.to_string |> String.concat ",\n"); *)
  let rec fillings_seq (fillings, lprob) min_lprob hole_locs_progs_and_synth_envs : (fillings * lprob) Seq.t =
    match hole_locs_progs_and_synth_envs with
    | [] -> Seq.return (fillings, lprob)
    | (hole_loc, prog_and_synth_envs)::rest ->
      fillings_seq (fillings, lprob) (div_lprobs min_lprob max_single_term_lprob (* reserve some probability for this hole! *)) rest
      |> Seq.flat_map begin fun (fillings, lprob) ->
        (* print_endline "retyping prog"; *)
        (* progs *)
        prog_and_synth_envs
        |> Seq.flat_map begin fun (prog, hole_synth_env) ->
            hole_fillings_seq ~cant_be_constant:false (fillings, lprob) min_lprob hole_loc hole_synth_env.hole_type hole_synth_env [] prog
          end
      end
  in
  fillings_seq (fillings, lprob) min_lprob hole_locs_progs_and_synth_envs
  |> Seq.filter (fun (_, lprob) -> lprob <= max_lprob)
  |> Seq.map fst

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



let rec fill_holes ?(max_lprob = lprob_1) ?(abort_lprob = -10000.0) lookup_exp_typed prog reqs file_name user_ctors : fillings option =
  if max_lprob < abort_lprob then (print_endline "aborting"; None) else
  let min_lprob = mult_lprobs max_lprob (lprob 0.02) in
  print_endline @@ "============== MIN LOGPROB " ^ string_of_float min_lprob ^ " =====================================";
  let e_guess (fillings, lprob) =
    e_guess (fillings, lprob) max_lprob min_lprob lookup_exp_typed prog reqs file_name user_ctors
  in
  Seq.concat
    [ e_guess (Loc_map.empty, lprob_1)
    ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob))
    ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob)))
    ; refine prog (Loc_map.empty, lprob_1) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> refine prog (fillings, lprob) reqs file_name
        (fun (fillings, lprob) -> e_guess (fillings, lprob))))
    ]
  (* Some reqs may not be pushed down to holes, so we need to verify them too. *)
  |> Seq.filter begin function fillings ->
    (* if !terms_tested_count mod 10_000 = 0 then print_endline (string_of_int !terms_tested_count ^ "\t" ^ Exp.to_string term); *)
    if !terms_tested_count mod 1_000 = 0 then begin
      print_endline (string_of_int !terms_tested_count ^ "\t" ^ StructItems.to_string (apply_fillings fillings prog));
      (* print_endline @@ Loc_map.to_string Exp.to_string fillings; *)
    end;
    incr terms_tested_count;
    (* ignore (exit 0); *)

    (* let code = StructItems.to_string (apply_fillings fillings prog) in *)
    (* print_endline code; *)
    (* if String.includes "succ (length" code && String.includes "-> 0" code then begin
      print_endline (string_of_int !terms_tested_count ^ "\t" ^ code);
      reqs |> List.for_all (is_req_satisified_by fillings)
    end else
      false *)
    (* reqs |> List.iter (fun req -> print_endline @@ string_of_req req ^ " is satisfied: " ^ string_of_bool (is_req_satisified_by fillings req)); *)
    reqs |> List.for_all (is_req_satisified_by fillings)
  end
  (* Return first valid filling. *)
  |> begin fun seq ->
    match seq () with
    | Seq.Cons (fillings, _) -> Some fillings
    | Seq.Nil                -> fill_holes ~max_lprob:min_lprob lookup_exp_typed prog reqs file_name user_ctors (* Keep trying, with lower prob threshold. *)
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

let results prog _trace assert_results file_name =
  terms_tested_count := 0;
  let start_sec = Unix.time () in
  let reqs = assert_results |>@ req_of_assert_result in
  (* print_string "Req "; *)
  (* reqs |> List.iter (string_of_req %> print_endline); *)
  print_endline @@ "Typing " ^ StructItems.to_string prog;
  let (typed_struct, _, final_tenv) =
    try Typing.typedtree_sig_env_of_parsed prog file_name
    with _ -> ({ Typedtree.str_items = []; str_type = []; str_final_env = Env.empty }, [], Env.empty)
  in
  let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
  let user_ctors =
    let initial_ctor_descs = Env.fold_constructors List.cons None(* not looking in a nested module *) Typing.initial_env [] in
    let user_ctor_descs =
      Env.fold_constructors List.cons None(* not looking in a nested module *) final_tenv []
      |>@? begin fun ctor_desc -> not (List.memq ctor_desc initial_ctor_descs) end
    in
    user_ctor_descs |>@ begin fun ({ Types.cstr_name; _ } as ctor_desc) ->
      (Longident.Lident cstr_name, ctor_desc, lprob_by_counts 1 (List.length user_ctor_descs))
    end
  in
  print_endline @@ string_of_int (List.length user_ctors) ^ " user ctors";
  match fill_holes type_lookups.lookup_exp prog reqs file_name user_ctors with
  | exception _ -> print_endline "synth exception"; Printexc.print_backtrace stdout; []
  | None -> print_endline "synth failed"; [prog]
  | Some fillings' ->
    print_endline @@ "synth success. " ^ string_of_float (Unix.time () -. start_sec) ^ "s";
    prog
    |> apply_fillings fillings'
    |> fun x -> [x]

let try_async path =
  if Unix.fork () = 0 then () else (* Don't hold up the request. *)
  (* Start synthesis and the synth process killer. *)
  match Unix.fork () with
  | 0 ->
    (* Uncomment the following if you want performance profiling *)
    (* begin
      let pid = Unix.getpid () in
      print_endline (string_of_int pid);
      let _ = Unix.create_process "sample" [|"sample"; string_of_int pid; "-mayDie"; "-file"; "synth_profile.txt"|] Unix.stdin Unix.stdout Unix.stderr in
      ()
    end *)
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
    begin match results parsed trace assert_results path |>@ remove_unnecessary_rec_flags with
    | result::_ ->
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
    print_endline "normal exit";
    exit 0
  | pid ->
    (* Start process killer *)
    (* Kill synthesis after 5 seconds. *)
    Unix.sleep 60;
    begin match Unix.waitpid [WNOHANG] pid with
    | (0, _) ->
      Unix.kill pid 9;
      print_endline "Synth timeout"
    | _ -> ()
    end
