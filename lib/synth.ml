open Camlboot_interpreter
open Camlboot_interpreter.Data
open Parsetree
open Shared
open Shared.Ast
open Shared.Util

(* type constraint = Envir.env * Parsetree.expression * value *)

type fillings = expression Loc_map.t



(* Constraints. But "constraint" is an OCaml keyword, so let's call them "req"s *)
type req      = Data.env * expression * value
type hole_req = Data.env * Location.t * value


let dont_care = new_vtrace ExDontCare

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
let rec push_down_req fillings ((env, exp, value) as req) =
  let open Eval in
  let prims, lookup_exp_typed, trace_state, frame_no = Primitives.prims, (fun _ -> None), Trace.new_trace_state, -1 in
  let rec try_cases scrutinee_val = function
    | [] -> None
    | case:: rest -> begin try
        let env' = pattern_bind fillings prims env lookup_exp_typed trace_state frame_no scrutinee_val [] case.pc_lhs scrutinee_val in
        begin match case.pc_guard with
        | None -> ()
        | Some guard when is_true (eval_expr fillings prims env' lookup_exp_typed trace_state frame_no guard) -> ()
        | _ -> raise Match_fail
        end;
        Some (env', case.pc_rhs)
      with Match_fail -> try_cases scrutinee_val rest
      end in
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
  | Pexp_fun (Nolabel, None, arg_pat, fun_exp) ->
    begin match value.v_ with
    | ExCall (arg, expected) -> begin try
        let env' = pattern_bind fillings prims env lookup_exp_typed trace_state frame_no arg [] arg_pat arg in
        push_down_req fillings (env', fun_exp, expected)
      with Match_fail -> [req]
      end
    | _ -> [req]
    end
  | Pexp_fun (_, _, _, _) -> [req]
  | Pexp_apply (f, l) ->
    (* START HERE *)
    ret @@
    (match eval_expr fillings prims env lookup_exp_typed trace_state frame_no f with
    | { v_ = Fexpr fexpr; _ } ->
      handle_fexpr_apply fillings prims env lookup_exp_typed trace_state frame_no expr.pexp_loc fexpr l
    | func_value ->
      let args = List.map (fun (lab, e) -> (lab, eval_expr fillings prims env lookup_exp_typed trace_state frame_no e)) l in
      apply fillings prims lookup_exp_typed trace_state func_value args)
  | Pexp_tuple l ->
    let args = List.map (eval_expr fillings prims env lookup_exp_typed trace_state frame_no) l in
    intro @@ new_vtrace @@ Tuple args
  | Pexp_match (e, cl) -> ret @@ eval_match fillings prims env lookup_exp_typed trace_state frame_no cl (eval_expr_exn fillings prims env lookup_exp_typed trace_state frame_no e)
  | Pexp_coerce (e, _, _) -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e
  | Pexp_constraint (e, _) -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e
  | Pexp_sequence (e1, e2) ->
    let _ = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1 in
    eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2
  | Pexp_while (e1, e2) ->
    while is_true (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1) do
      ignore (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2)
    done;
    unit
  | Pexp_for (p, e1, e2, flag, e3) ->
    let v1 = Runtime_base.unwrap_int (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1) in
    let v2 = Runtime_base.unwrap_int (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2) in
    if flag = Upto
    then
      for x = v1 to v2 do
        let vx = Runtime_base.wrap_int x in
        ignore (eval_expr fillings prims (pattern_bind fillings prims env lookup_exp_typed trace_state frame_no vx [] p vx) lookup_exp_typed trace_state frame_no e3)
      done
    else
      for x = v1 downto v2 do
        let vx = Runtime_base.wrap_int x in
        ignore (eval_expr fillings prims (pattern_bind fillings prims env lookup_exp_typed trace_state frame_no vx [] p vx) lookup_exp_typed trace_state frame_no e3)
      done;
    unit
  | Pexp_ifthenelse (e1, e2, e3) -> ret @@
    if is_true (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1)
    then eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2
    else (
      match e3 with
      | None -> unit
      | Some e3 -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e3)
  | Pexp_unreachable -> failwith "reached unreachable"
  | Pexp_try (e, cs) -> ret @@
    (try eval_expr fillings prims env lookup_exp_typed trace_state frame_no e
     with InternalException v ->
       (try eval_match fillings prims env lookup_exp_typed trace_state frame_no cs (Ok v)
        with Match_fail -> raise (InternalException v)))
  | Pexp_construct (c, e) ->
    let cn = lident_name c.txt in
    let d = env_get_constr env c in
    let (vv, ctor_type_opt) =
      match e with
      | None -> (None, lookup_type_opt lookup_exp_typed expr)
      | Some e ->
        let arg_val = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
        ( Some arg_val
        , type_ctor (lookup_type_env lookup_exp_typed expr) c (Some arg_val)
        )
    in
    add_type_opt ctor_type_opt @@ intro @@ new_vtrace @@ Constructor (cn, d, vv)
  | Pexp_variant (cn, e) ->
    let ee =
      match e with
      | None -> None
      | Some e -> Some (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e)
    in
    intro @@ new_vtrace @@ Constructor (cn, Hashtbl.hash cn, ee)
  | Pexp_record (r, e) ->
    let base =
      match e with
      | None -> SMap.empty
      | Some e ->
        (match eval_expr fillings prims env lookup_exp_typed trace_state frame_no e with
        | { v_ = Record r; _ } -> r
        | _ -> mismatch expr.pexp_loc; assert false)
    in
    intro @@ new_vtrace @@ Record
      (List.fold_left
         (fun rc ({ txt = lident; _ }, ee) ->
           SMap.add (lident_name lident) (ref (eval_expr fillings prims env lookup_exp_typed trace_state frame_no ee)) rc)
         base
         r)
  | Pexp_field (e, { txt = lident; _ }) ->
    (match eval_expr fillings prims env lookup_exp_typed trace_state frame_no e with
    | { v_ = Record r; _ } as v ->
      pat_match v [Field (lident_name lident)] @@
      !(SMap.find (lident_name lident) r)
    | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_setfield (e1, { txt = lident; _ }, e2) ->
    let v1 = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1 in
    let v2 = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2 in
    (match v1.v_ with
    | Record r ->
      SMap.find (lident_name lident) r := v2;
      unit
    | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_array l -> intro @@ new_vtrace @@ Array (Array.of_list (List.map (eval_expr fillings prims env lookup_exp_typed trace_state frame_no) l))
  | Pexp_send (obj_expr, meth) -> ret @@
     let obj = eval_expr fillings prims env lookup_exp_typed trace_state frame_no obj_expr in
     (match obj.v_ with
      | Object obj -> eval_obj_send fillings expr.pexp_loc prims lookup_exp_typed trace_state frame_no obj meth
      | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_new lid -> intro @@
     let (class_expr, class_env) = env_get_class env lid in
     eval_obj_new fillings prims !class_env lookup_exp_typed trace_state frame_no class_expr
  | Pexp_setinstvar (x, e) ->
     let v = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
     let x = { x with Location.txt = Longident.Lident x.txt } in
     begin match env_get_value_or_lvar env x with
       | Value _ -> mismatch expr.pexp_loc; assert false
       | Instance_variable (obj, name) ->
          let var = SMap.find name obj.variables in
          var := v;
     end;
     Runtime_base.wrap_unit ()
  | Pexp_override fields ->
     begin match env.current_object with
       | None -> mismatch expr.pexp_loc; assert false
       | Some obj ->
          let new_obj = eval_obj_override fillings prims env lookup_exp_typed trace_state frame_no obj fields in
          intro @@ new_vtrace @@ Object new_obj
     end
  | Pexp_letexception ({ pext_name = name; pext_kind = k; _ }, e) ->
    let nenv =
      match k with
      | Pext_decl _ ->
        let d = next_exn_id () in
        env_set_constr name.txt d env
      | Pext_rebind path ->
        env_set_constr name.txt (env_get_constr env path) env
    in
    eval_expr fillings prims nenv lookup_exp_typed trace_state frame_no e
  | Pexp_letmodule (name, me, e) ->
    let m = eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me in
    eval_expr fillings prims (env_set_module name.txt m env) lookup_exp_typed trace_state frame_no e
  | Pexp_assert e ->
    begin match !asserts_mode with
    | Throw_exception ->
      if is_true (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e)
      then unit
      else (
        (*failwith "assert failure"*)
        let loc = expr.pexp_loc in
        let Lexing.{ pos_fname; pos_lnum; pos_cnum; _ } =
          loc.Location.loc_start
        in
        raise
          (InternalException
            (Runtime_base.assert_failure_exn pos_fname pos_lnum pos_cnum)))
    | Gather assert_results ->
      let open Shared.Ast_match in
      begin try
        let match_       = match_exp_ f_x_equals_y_pattern e in
        let fexp         = SMap.find "f" match_.exps in
        let argexp       = SMap.find "x" match_.exps in
        let expected_exp = SMap.find "y" match_.exps in
        begin match eval_expr fillings prims env lookup_exp_typed trace_state frame_no fexp with
        | { v_ = Fexpr fexpr; _ } ->
          handle_fexpr_apply fillings prims env lookup_exp_typed trace_state frame_no expr.pexp_loc fexpr [(Nolabel, argexp)]
        | fval ->
          let argval = (try eval_expr fillings prims env lookup_exp_typed trace_state frame_no argexp with _ -> intro_bomb ()) in
          let actual = (try apply fillings prims lookup_exp_typed trace_state fval [(Nolabel, argval)] with _ -> intro_bomb ()) in
          let expected = (try eval_expr fillings prims env lookup_exp_typed trace_state frame_no expected_exp with _ -> intro_bomb ()) in
          let passed =
            begin match (try Some (value_compare actual expected) with _ -> None) with
            | Some 0 -> true
            | _      -> false
            end in
          assert_results :=
            { f            = fval
            ; arg          = argval
            ; expected     = expected
            ; actual       = actual
            ; passed       = passed
            ; expected_exp = expected_exp
            } :: !assert_results;
          unit
        end
      with Match_fail ->
        print_endline "TODO: handle asserts that are not f x = y";
        unit
      end
    end
  | Pexp_lazy e -> intro @@ new_vtrace @@ Lz (ref (fun () -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e))
  | Pexp_poly (e, _ty) -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e
  | Pexp_newtype (_, e) -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e
  | Pexp_open (_, lident, e) ->
    let nenv =
      match env_get_module_data env lident with
      | exception Not_found ->
        (* Module might be a .mli only *)
        env
      | module_data -> env_extend false env module_data
    in
    eval_expr fillings prims nenv lookup_exp_typed trace_state frame_no e
  | Pexp_object _ -> unsupported expr.pexp_loc; assert false
  | Pexp_pack me -> intro @@ new_vtrace @@ ModVal (eval_module_expr prims env lookup_exp_typed trace_state frame_no me)
  | Pexp_extension _ -> unsupported expr.pexp_loc; assert false
