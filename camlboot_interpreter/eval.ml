open Asttypes
open Parsetree

open Conf
open Data
open Envir

exception Match_fail

type asserts_mode =
  | Throw_exception
  | Gather of assert_result list ref

let asserts_mode = ref Throw_exception

(* Use Gather mode when you want to gather the assert results OR you don't want failed asserts to crash execution. *)
let with_gather_asserts f =
  let old_mode = !asserts_mode in
  let assert_results = ref [] in
  asserts_mode := Gather assert_results;
  let out = f () in
  asserts_mode := old_mode;
  (out, !assert_results)

let with_throwing_asserts f =
  let old_mode = !asserts_mode in
  asserts_mode := Throw_exception;
  let out = f () in
  asserts_mode := old_mode;
  out

let add_assert_result assert_result assert_results =
  assert_results := assert_result :: !assert_results

(* Only equality asserts. Assumes user code is lhs and expectation is rhs. *)
let parse_assert exp =
  match Shared.Ast.Exp.simple_apply_parts exp with
  | Some ("=", [lhs; rhs]) -> Some (lhs, rhs)
  | _                      -> None


exception No_fuel
let fuel = ref max_int
let with_fuel count f out_of_fuel_f = (* Resets fuel to prior after return/failure. *)
  let prior_fuel = !fuel in
  fuel := count;
  let out = try f () with No_fuel -> out_of_fuel_f () | e -> fuel := prior_fuel; raise e in
  fuel := prior_fuel;
  out
let alloc_fuel count f out_of_fuel_f = (* Subtracts fuel after return/failure. *)
  let saved_fuel = max 0 (!fuel - count) in
  fuel := !fuel - saved_fuel;
  let reset_fuel () = fuel := !fuel + saved_fuel in
  let out = try f () with No_fuel -> out_of_fuel_f () | e -> reset_fuel (); raise e in
  reset_fuel ();
  out

module Option = struct
  (* Selections from https://ocaml.org/api/Option.html *)
  let map f = function Some x -> Some (f x) | None -> None
  let join = function Some (Some x) -> Some x | _ -> None
  let to_list = function Some x -> [x] | None -> []

  let rec project = function
    | []             -> Some []
    | None   :: _    -> None
    | Some x :: rest -> project rest |> map (List.cons x)
end

let rec lident_name = function
  | Longident.Lident s -> s
  | Longident.Ldot (_, s) -> s
  | Longident.Lapply (_l1, l2) -> lident_name l2

let rec expr_label_shape = function
  | Pexp_fun (label, default, _, e) ->
    (label, default) :: expr_label_shape e.pexp_desc
  | Pexp_function _ -> [ (Nolabel, None) ]
  | _ -> []

let fun_label_shape = function
  | Fun (lab, default, _, e, _) ->
    (lab, default) :: expr_label_shape e.pexp_desc
  | Function _ -> [ (Nolabel, None) ]
  | Prim _ -> [ (Nolabel, None) ]
  | _ -> []

let mismatch loc =
  Format.eprintf "%a: mismatch@."
    Location.print_loc loc

let unsupported loc =
  Format.eprintf "%a: unsupported@."
    Location.print_loc loc

let rec take n li = match n, li with
    | 0, _ -> []
    | _, [] -> invalid_arg "List.take"
    | n, x::xs -> x :: take (n - 1) xs

let lookup_type_opt lookup_exp_typed loc =
  match lookup_exp_typed loc with
  | Some typed_exp -> Some (Shared.Ast.Type.copy typed_exp.Typedtree.exp_type) (* Ensure the lookup map is not mutated! *)
  | None           -> None

let lookup_type_env lookup_exp_typed loc =
  match lookup_exp_typed loc with
  | Some typed_exp -> typed_exp.Typedtree.exp_env
  | None           -> Env.empty

(* let infer_local_type exp = (Typecore.type_exp Env.empty exp).exp_type *)

(* Based OCaml's Typecore.type_construct *)
let type_ctor env ctor_lid arg_val_opt =
  match Typetexp.find_all_constructors env ctor_lid.loc ctor_lid.txt with
  | [(ctor, _)] ->
    let (arg_types, ctor_type) = Ctype.instance_constructor ctor in
    let arg_val_type_opts =
      match arg_val_opt with
      | Some arg_val ->
        begin match arg_val.v_ with
        | Tuple arg_vals -> List.map (fun v -> v.type_opt) arg_vals
        | _ -> [arg_val.type_opt]
        end
      | None ->
        []
    in
    begin match Option.project arg_val_type_opts with
    | Some arg_val_types ->
      begin try
        (* Not 100% sure, but Env may only be needed for unification in the case of GADTS. *)
        List.iter2 (Ctype.unify Env.empty) arg_types arg_val_types
      with
      | Invalid_argument err -> print_endline @@ "val args not the same length as type ctor args " ^ err
      | _                    -> print_endline @@ "unification failure"
      end
    | None -> ()
    end;
    Some ctor_type
  | _ -> None

let perhaps_add_type_opt lookup_exp_typed expr v =
  (* Try to recover types for values introduced in library code *)
  if v.type_opt = None then
    match lookup_type_opt lookup_exp_typed expr.pexp_loc with
    | Some typ when not (Shared.Ast.Type.is_var_type typ) -> add_type_opt (Some typ) v
    | _                                                   -> v
  else
    v

let rec apply fillings prims lookup_exp_typed trace_state (vf : value) args =
  (* All the pattern binds can raise BombExn *)
  try begin
  trace_state.Trace.frame_no <- trace_state.Trace.frame_no + 1;
  let frame_no = trace_state.frame_no in
  let vf, extral, extram =
    match vf.v_ with
    | Fun_with_extra_args (vf, extral, extram) -> (vf, extral, extram)
    | _ -> (vf, [], SMap.empty)
  in
  assert (extral = []);
  (* let ls = fun_label_shape vf in *)
  let apply_labelled vf (lab, arg) =
    match vf.v_ with
    | Fun (label, default, p, e, fenv_ref) ->
      (match (label, lab, default) with
      | Optional s, Labelled s', None ->
        assert (s = s');
        let v = new_vtrace @@ Constructor ("Some", 0, Some arg) in
        eval_expr
          fillings
          prims
          (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no v [] p v)
          lookup_exp_typed
          trace_state
          frame_no
          e
      | Optional s, Labelled s', Some _
      | Optional s, Optional s', None
      | Labelled s, Labelled s', None ->
        assert (s = s');
        eval_expr fillings prims (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no arg [] p arg) lookup_exp_typed trace_state frame_no e
      | Optional s, Optional s', Some def ->
        assert (s = s');
        let arg =
          match arg.v_ with
          | Constructor ("None", 0, None) -> eval_expr fillings prims !fenv_ref lookup_exp_typed trace_state frame_no def
          | Constructor ("Some", 0, Some arg) -> arg
          | _ -> assert false
        in
        eval_expr fillings prims (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no arg [] p arg) lookup_exp_typed trace_state frame_no e
      | _ -> assert false)
    | _ -> assert false
  in
  let apply_optional_noarg vf =
    match vf.v_ with
    | Fun (Optional _, None, p, e, fenv_ref) ->
      let v = new_vtrace @@ Constructor ("None", 0, None) in
      eval_expr
        fillings
        prims
        (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no v [] p v)
        lookup_exp_typed
        trace_state
        frame_no
        e
    | Fun (Optional _, Some def, p, e, fenv_ref) ->
      let fenv = !fenv_ref in
      let v = eval_expr fillings prims fenv lookup_exp_typed trace_state frame_no def in
      eval_expr
        fillings
        prims
        (pattern_bind fillings prims fenv lookup_exp_typed trace_state frame_no v [] p v)
        lookup_exp_typed
        trace_state
        frame_no
        e
    | _ -> assert false
  in
  let unlabelled =
    List.map snd (List.filter (fun (lab, _) -> lab = Nolabel) args)
  in
  let with_label =
    ref
      (List.fold_left
         (fun wl (lab, arg) ->
           match lab with
           | Nolabel -> wl
           | Optional s | Labelled s -> SMap.add s (lab, arg) wl)
         extram
         args)
  in
  let has_labelled = not (SMap.is_empty !with_label) in
  let rec apply_one vf arg =
    match vf.v_ with
    | Fun (Nolabel, _default, p, e, fenv_ref) ->
      eval_expr fillings prims (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no arg [] p arg) lookup_exp_typed trace_state frame_no e
    | Fun (((Labelled s | Optional s) as lab), _default, p, e, fenv_ref) ->
      if has_labelled
      then
        if SMap.mem s !with_label
        then (
          let v = SMap.find s !with_label in
          with_label := SMap.remove s !with_label;
          apply_one (apply_labelled vf v) arg)
        else (
          assert (lab = Optional s);
          apply_one (apply_optional_noarg vf) arg)
      else if lab = Optional s
      then apply_one (apply_optional_noarg vf) arg
      else eval_expr fillings prims (pattern_bind fillings prims !fenv_ref lookup_exp_typed trace_state frame_no arg [] p arg) lookup_exp_typed trace_state frame_no e
    | Function (cl, fenv_ref) -> eval_match fillings prims !fenv_ref lookup_exp_typed trace_state frame_no cl (Ok arg)
    | Prim (_, prim_f) -> prim_f arg
    | _ ->
      (* Format.eprintf "Trying to apply a nonfunction: %a@." pp_print_value vf; *)
      new_vtrace Bomb
      (* assert false *)
  in
  if SMap.is_empty !with_label
  then
    (* Special case to get tail recursion *)
    List.fold_left apply_one vf unlabelled
  else (
    let vf = List.fold_left apply_one vf unlabelled in
    let rec apply_loop vf =
      if SMap.is_empty !with_label
      then vf
      else (
        match vf.v_ with
        | Fun (((Labelled s | Optional s) as lab), _default, _p, _e, _fenv) ->
          if SMap.mem s !with_label
          then (
            let v = SMap.find s !with_label in
            with_label := SMap.remove s !with_label;
            apply_loop (apply_labelled vf v))
          else (
            assert (lab = Optional s);
            apply_loop (apply_optional_noarg vf))
        | _ -> new_vtrace @@ Fun_with_extra_args (vf, [], !with_label)) (* REVISIT *)
    in
    apply_loop vf)
  end with BombExn -> new_vtrace Bomb

and handle_fexpr_apply fillings prims env lookup_exp_typed trace_state frame_no loc fexpr l =
  match fexpr loc l with
  | None ->
    Format.eprintf "%a@.F-expr failure.@." Location.print_loc loc;
    assert false
  | Some expr -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr

and eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr =
  decr fuel;
  (* print_endline (string_of_int !fuel); *)
  (* print_endline (Shared.Ast.Exp.to_string expr); *)
  (* if true then failwith "asfasdfadaf" else *)
  if !fuel <= 0 then raise No_fuel;
  let attach_trace value =
    let trace_entry = (expr.pexp_loc, frame_no, value, env) in
    trace_state.Trace.trace <- Trace.add trace_entry trace_state.Trace.trace;
    value
  in
  let intro                       v = { v with vtrace = ((frame_no, expr.pexp_loc), Intro)                         :: v.vtrace } in
  let use                         v = { v with vtrace = ((frame_no, expr.pexp_loc), Use)                           :: v.vtrace } in
  let ret                         v = { v with vtrace = ((frame_no, expr.pexp_loc), Ret)                           :: v.vtrace } in
  let pat_match root_val val_path v = { v with vtrace = ((frame_no, expr.pexp_loc), PatMatch (root_val, val_path)) :: v.vtrace } in
  let intro_bomb () = intro @@ new_vtrace @@ Bomb in
  attach_trace @@
  begin match Shared.Loc_map.find_opt expr.pexp_loc fillings with
  | Some filling_exp -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no filling_exp
  | None ->
    begin match expr.pexp_desc with
    | Pexp_ident { txt = Longident.Lident "??"; _ } ->
      intro @@ new_vtrace @@ Hole (ref env, frame_no, expr)
    | Pexp_ident id -> use @@
      perhaps_add_type_opt lookup_exp_typed expr @@
      begin try match env_get_value_or_lvar env id with
        | Value ({ v_ = Hole (env_ref, frame_no, e); _ } as v) ->
          begin match Shared.Loc_map.find_opt e.pexp_loc fillings with
          | Some filling_exp -> eval_expr fillings prims !env_ref lookup_exp_typed trace_state frame_no filling_exp
          | None -> v
          end
        | Value v -> v
        | Instance_variable (obj, name) ->
          let var = SMap.find name obj.variables in
          !var
        with Not_found -> (* print_endline @@ "ident " ^ Longident.last id.txt ^ " not found"; *) intro_bomb ()
      end
    | Pexp_constant c -> add_type_opt (lookup_type_opt lookup_exp_typed expr.pexp_loc) @@ intro @@ value_of_constant c
    | Pexp_let (recflag, vbs, e) ->
      (* Don't bother attaching vtrace to let results for now (the body exp will have an entry) *)
      let alloc_fuel_per_binding = if !fuel > 100 then !fuel - 50 else 50 in
      eval_expr fillings prims (eval_bindings ~alloc_fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no recflag vbs) lookup_exp_typed trace_state frame_no e
    | Pexp_function cl -> add_type_opt (lookup_type_opt lookup_exp_typed expr.pexp_loc) @@ intro @@ new_vtrace @@ Function (cl, ref env)
    | Pexp_fun (label, default, p, e) -> add_type_opt (lookup_type_opt lookup_exp_typed expr.pexp_loc) @@ intro @@ new_vtrace @@ Fun (label, default, p, e, ref env)
    | Pexp_apply (f, l) -> ret @@
      perhaps_add_type_opt lookup_exp_typed expr @@
      (match eval_expr fillings prims env lookup_exp_typed trace_state frame_no f with
      | { v_ = Fexpr fexpr; _ } ->
        (* print_endline (Shared.Ast.Exp.to_string f);
        l |> List.iter (fun (_, arg) -> print_endline (Shared.Ast.Exp.to_string arg)); *)
        handle_fexpr_apply fillings prims env lookup_exp_typed trace_state frame_no expr.pexp_loc fexpr l
      | func_value ->
        let args = List.map (fun (lab, e) -> (lab, eval_expr fillings prims env lookup_exp_typed trace_state frame_no e)) l in
        if log_fun_calls
        then (
          match f.pexp_desc with
          | Pexp_ident lident ->
            Format.eprintf
              "apply %s"
              (String.concat "." (Longident.flatten lident.txt));
            incr log_fun_calls_cur;
            if !log_fun_calls_cur > log_fun_calls_arg_from
            then
              Format.eprintf
                " %a"
                (Format.pp_print_list
                  ~pp_sep:(fun ff () -> Format.fprintf ff " ")
                  (fun ff (_, v) -> Format.fprintf ff "%a" pp_print_value v))
                args;
            Format.eprintf "@."
          | _ -> ());
        apply fillings prims lookup_exp_typed trace_state func_value args)
    | Pexp_tuple l ->
      let args = List.map (eval_expr fillings prims env lookup_exp_typed trace_state frame_no) l in
      intro @@ new_vtrace @@ Tuple args
    | Pexp_match (e, cl) -> ret @@
      begin try eval_match fillings prims env lookup_exp_typed trace_state frame_no cl (eval_expr_exn fillings prims env lookup_exp_typed trace_state frame_no e)
      with Match_fail | BombExn -> intro_bomb ()
      end
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
    | Pexp_ifthenelse (e1, e2, e3_opt) -> ret @@
      let guard_val = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e1 in
      begin try if is_true guard_val
      then eval_expr fillings prims env lookup_exp_typed trace_state frame_no e2
      else (
        match e3_opt with
        | None -> unit
        | Some e3 -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no e3)
      with BombExn -> intro_bomb ()
      end
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
        | None -> (None, lookup_type_opt lookup_exp_typed expr.pexp_loc)
        | Some e ->
          let arg_val = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
          ( Some arg_val
          , type_ctor (lookup_type_env lookup_exp_typed expr.pexp_loc) c (Some arg_val)
          )
      in
      add_type_opt ctor_type_opt @@ intro @@ new_vtrace @@ Constructor (cn, d, vv)
    | Pexp_variant (cn, e) ->
      let ee =
        match e with
        | None -> None
        | Some e -> Some (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e)
      in
      intro @@ new_vtrace @@ Constructor ("`" ^ cn, Hashtbl.hash cn, ee)
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
        let assertion_failed () =
          (*failwith "assert failure"*)
          let loc = expr.pexp_loc in
          let Lexing.{ pos_fname; pos_lnum; pos_cnum; _ } =
            loc.Location.loc_start
          in
          raise
            (InternalException
              (Runtime_base.assert_failure_exn pos_fname pos_lnum pos_cnum))
        in
        begin match is_true (eval_expr fillings prims env lookup_exp_typed trace_state frame_no e) with
        | true              -> unit
        | _                 -> assertion_failed ()
        | exception No_fuel -> assertion_failed ()
        end
      | Gather assert_results ->
        begin match parse_assert e with
        | Some (lhs_exp, expected_exp) ->
          let eval_lhs () = eval_expr fillings prims env lookup_exp_typed trace_state frame_no lhs_exp in
          let allocation = if !fuel > 100 then !fuel - 50 else 50 in
          let actual   = (try alloc_fuel allocation eval_lhs (fun () -> intro_bomb ())                        with _ -> intro_bomb ()) in
          let expected = (try eval_expr fillings prims env lookup_exp_typed trace_state frame_no expected_exp with _ -> intro_bomb ()) in
          let passed =
            begin match (try Some (value_compare actual expected) with _ -> None) with
            | Some 0 -> true
            | _      -> false
            end in
          assert_results :=
            { env          = env
            ; lhs_exp      = lhs_exp
            ; expected_exp = expected_exp
            ; actual       = actual
            ; expected     = expected
            ; passed       = passed
            } :: !assert_results;
          unit
        | None ->
          print_endline "TODO: handle asserts that are not equality";
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
    | Pexp_pack me -> intro @@ new_vtrace @@ ModVal (eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me)
    | Pexp_extension _ -> unsupported expr.pexp_loc; assert false
    end
  end

and eval_expr_exn fillings prims env lookup_exp_typed trace_state frame_no expr =
  try Ok (eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr) with InternalException v -> Error v

(* fuel_per_binding is top-level only and not recursed to children *)
and eval_bindings ?fuel_per_binding ?alloc_fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no recflag defs =
  let fueled f out_of_fuel_f =
    begin match fuel_per_binding, alloc_fuel_per_binding with
    | Some fuel, _ -> with_fuel fuel f out_of_fuel_f (* Top level only, set fuel per binding. *)
    | _, Some fuel -> alloc_fuel fuel f out_of_fuel_f (* Non-top level, we can't exceed our fuel allocation but might not want to spend it all on one binding *)
    | _            -> f ()
    end
  in
  let bind_value env vb =
    let f () =
      let v = eval_expr fillings prims env lookup_exp_typed trace_state frame_no vb.pvb_expr in
      pattern_bind fillings prims env lookup_exp_typed trace_state frame_no v [] vb.pvb_pat v
    in
    let out_of_fuel_f () =
      (* If out of fuel, set all var names to Bomb *)
      vb.pvb_pat |> Shared.Ast.Pat.names |> List.fold_left (fun env name -> env_set_value name (new_vtrace Bomb) env) env
    in
    fueled f out_of_fuel_f
  in
  match recflag with
    | Nonrecursive ->
      List.fold_left bind_value env defs
    | Recursive ->
      (* LHS of let rec is always a single variable *)
      (* What's allowed on the RHS is rather complicated (see classify_expression in typecore.ml) *)
      (* But, expressions that only reference non-rec variables are allowed. *)
      (* As are functions. That should cover everything practical, right? *)
      (* The following is allowed but odd:
        let rec ff =
          ( (fun () -> (ff.v_) ())
          , (fun () -> (snd ff) ())
          )
        in
        ...
      *)
      (* let dummies = List.map (fun _ -> Ptr.dummy ()) defs in
      let declare env vb dummy =
        pattern_bind fillings prims env lookup_exp_typed trace_state frame_no vb.pvb_pat dummy in
      let define env vb dummy =
        let v = eval_expr fillings prims env lookup_exp_typed trace_state frame_no vb.pvb_expr in
        Ptr.backpatch dummy v in
      let nenv = List.fold_left2 declare env defs dummies in
      List.iter2 (define nenv) defs dummies; *)
      (* let declare env vb =
        pattern_bind fillings prims env lookup_exp_typed trace_state frame_no vb.pvb_pat Bomb in *)
      let rec single_name p =
        match p.ppat_desc with
        | Ppat_var s             -> s.txt
        | Ppat_constraint (p, _) -> single_name p
        | _                      ->
          Format.eprintf "Only single vars are allowed on the LHS of a let rec: %a\n" Pprintast.pattern p;
          raise (InternalException (Runtime_base.failure_exn "Only single vars are allowed on the LHS of a let rec"))
      in
      let dummy_env = List.fold_left (fun env vb -> env_set_value (single_name vb.pvb_pat) (new_vtrace Bomb) env) env defs in
      let vals = defs |> List.map begin fun vb ->
        let f () = eval_expr fillings prims dummy_env lookup_exp_typed trace_state frame_no vb.pvb_expr in
        fueled f (fun () -> new_vtrace Bomb) (* If out of fuel, value is Bomb *)
      end in
      let nenv = List.fold_left2
        (* (fun env vb v -> env_set_value (single_name vb.pvb_pat) (pat_match vb.pvb_pat [] v v) env) *)
        (fun env vb v -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no v [] vb.pvb_pat v)
        env defs vals in
      let rec packpatch_env { v_; _ } =
        match v_ with
        | Hole (env_ref, _, _)       -> env_ref := nenv
        | Fun (_, _, _, _, env_ref)  -> env_ref := nenv
        | Function (_, env_ref)      -> env_ref := nenv
        | Tuple vals                 -> List.iter packpatch_env vals
        | Constructor (_, _, Some v) -> packpatch_env v
        | Array vals                 -> Array.iter packpatch_env vals
        | Record field_map           -> SMap.iter (fun _ val_ref -> packpatch_env !val_ref) field_map
        | _                          -> ()
        (* | Fun_with_extra_args of value * value list * (arg_label * value) SMap.t *)
        (* | Object object_value -> *)
      in
      List.iter packpatch_env vals;
      nenv

and pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path pat ({ v_; _ } as v : value) =
  (* frame_no is passed in here because pattern matches can execute code, which will change the lookup_exp_typed trace_state frame_no for later calls to pattern_bind *)
  (* (namely the str = "Format" case) *)
  let intro          v = { v with vtrace = ((frame_no, pat.ppat_loc), Intro)                     :: v.vtrace } in
  let pat_match path v = { v with vtrace = ((frame_no, pat.ppat_loc), PatMatch (root_val, path)) :: v.vtrace } in
  let v = pat_match path v in
  let attach_trace env =
    let trace_entry = (pat.ppat_loc, frame_no, v, env) in
    trace_state.trace <- Trace.add trace_entry trace_state.trace;
    env
  in
  attach_trace @@
  match pat.ppat_desc with
  | Ppat_any -> env
  | Ppat_var s -> env_set_value s.txt v env
  | Ppat_alias (p, s) ->
    env_set_value s.txt
      v
      (pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path p v)
  | Ppat_constant c ->
    if value_equal (value_of_constant c) v then env else raise Match_fail
  | Ppat_interval (c1, c2) ->
    if value_le (value_of_constant c1) v && value_le v (value_of_constant c2)
    then env
    else raise Match_fail
  | Ppat_tuple l ->
    (match v_ with
    | Tuple vl ->
      assert (List.length l = List.length vl);
      List.fold_left2
        (fun env i (p, v) -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val (path @ [Child i]) p v)
        env
        (List.init (List.length l) (fun i -> i))
        (List.combine l vl)
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_construct (c, p) ->
    let cn = lident_name c.txt in
    begin try
      let dn = env_get_constr env c in
      (match v_ with
      | Constructor (ccn, ddn, e) ->
        if cn <> ccn then raise Match_fail;
        if dn <> ddn then raise Match_fail;
        (match (p, e) with
        | None, None -> env
        | Some p, Some e -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val (path @ [Child 0]) p e
        | _ -> mismatch pat.ppat_loc; assert false)
      | String _ ->
        assert (lident_name c.txt = "Format");
        let p =
          match p with
          | None -> mismatch pat.ppat_loc; assert false
          | Some p -> p
        in
        let fmt_ebb_of_string =
          let lid =
            Longident.(Ldot (Lident "CamlinternalFormat", "fmt_ebb_of_string"))
          in
          match env_get_value_or_lvar env { loc = c.loc; txt = lid } with
            | Instance_variable _ -> assert false
            | Value v -> v
        in
        let fmt = apply fillings prims lookup_exp_typed trace_state fmt_ebb_of_string [ (Nolabel, v) ] in
        let fmt =
          match fmt.v_ with
          | Constructor ("Fmt_EBB", _, Some fmt) -> fmt
          | _ -> mismatch pat.ppat_loc; assert false
        in
        (* What the heck is this *)
        let tupv = intro @@ new_vtrace @@ Tuple [ fmt; v ] in
        pattern_bind fillings prims env lookup_exp_typed trace_state frame_no tupv [] p tupv
      | Bomb
      | Hole _ ->
        raise BombExn
      | _ ->
        (* Format.eprintf "cn = %s@.v = %a@." cn pp_print_value v; *)
        assert false)
    with Not_found -> (* Bad ctor in pat position. *)
      raise BombExn
    end
  | Ppat_variant (name, p) ->
    (match v_ with
    | Constructor (cn, _, e) ->
      if cn <> "`" ^ name then raise Match_fail;
      (match (p, e) with
      | None, None -> env
      | Some p, Some e -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val (path @ [Child 0]) p e
      | _ -> mismatch pat.ppat_loc; assert false)
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_record (rp, _) ->
    (match v_ with
    | Record r ->
      List.fold_left
        (fun env (lident, p) ->
          let name = lident_name lident.txt in
          pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val (path @ [Field name]) p !(SMap.find name r))
        env
        rp
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_array ps ->
     (match v_ with
        | Array vs ->
          let vs = Array.to_list vs in
          if List.length ps <> List.length vs then raise Match_fail;
          List.fold_left2
            (fun env i (p, v) -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val (path @ [Child i]) p v)
            env
            (List.init (List.length ps) (fun i -> i))
            (List.combine ps vs)
        | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_or (p1, p2) ->
    (try pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path p1 v
     with Match_fail -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path p2 v)
  | Ppat_constraint (p, _) -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path p v
  | Ppat_type _ -> unsupported pat.ppat_loc; assert false
  | Ppat_lazy _ -> unsupported pat.ppat_loc; assert false
  | Ppat_unpack name ->
    (match v_ with
    | ModVal m -> env_set_module name.txt m env
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_exception _ -> raise Match_fail
  | Ppat_extension _ -> unsupported pat.ppat_loc; assert false
  | Ppat_open _ -> unsupported pat.ppat_loc; assert false

and pattern_bind_exn fillings prims env lookup_exp_typed trace_state frame_no root_val path pat v =
  match pat.ppat_desc with
  | Ppat_exception p -> pattern_bind fillings prims env lookup_exp_typed trace_state frame_no root_val path p v
  | _ -> raise Match_fail

and pattern_bind_checkexn fillings prims env lookup_exp_typed trace_state frame_no pat v =
  match v with
  | Ok    v -> pattern_bind     fillings prims env lookup_exp_typed trace_state frame_no v [] pat v
  | Error v -> pattern_bind_exn fillings prims env lookup_exp_typed trace_state frame_no v [] pat v

and eval_match fillings prims env lookup_exp_typed trace_state frame_no cl arg =
  match cl with
  | [] ->
    (match arg with
    | Ok _ -> raise Match_fail
    | Error v -> raise (InternalException v))
  | c :: cl ->
    (match pattern_bind_checkexn fillings prims env lookup_exp_typed trace_state frame_no c.pc_lhs arg with
    | exception Match_fail -> eval_match fillings prims env lookup_exp_typed trace_state frame_no cl arg
    | nenv ->
      let guard_ok =
        match c.pc_guard with
        | None -> true
        | Some guard -> is_true (eval_expr fillings prims nenv lookup_exp_typed trace_state frame_no guard)
      in
      if guard_ok
      then eval_expr fillings prims nenv lookup_exp_typed trace_state frame_no c.pc_rhs
      else eval_match fillings prims env lookup_exp_typed trace_state frame_no cl arg)

and lookup_viewed_object obj =
  let rec lookup obj = function
    | [] -> obj
    | parent :: parent_view ->
       lookup (SMap.find parent obj.named_parents) parent_view
  in lookup obj obj.parent_view

(* OO vtracing is ill-defined right now *)
and eval_expr_in_object fillings prims lookup_exp_typed trace_state frame_no obj expr_in_object =
  let expr_env = match expr_in_object.source with
      | Parent parent -> parent.env
      | Current_object -> (lookup_viewed_object obj).env
  in
  let bind_self obj env =
    let self_view = { obj with parent_view = [] } in
    let self_pattern = match expr_in_object.source with
      | Parent parent -> parent.self
      | Current_object -> (lookup_viewed_object obj).self in
    let self_v = new_vtrace @@ Object self_view in
    pattern_bind fillings prims env lookup_exp_typed trace_state frame_no self_v [] self_pattern self_v in
  let add_parent obj name env =
    let parent_view =
      { obj with parent_view = name :: obj.parent_view } in
    env_set_value name (new_vtrace @@ Object parent_view) env in
  let add_variable name env =
    env_set_lvar name obj env in
  let activate_object obj env =
    { env with current_object = Some obj } in
  let env =
    expr_env
    |> bind_self obj
    |> SSet.fold (add_parent obj) expr_in_object.named_parents_scope
    |> SSet.fold add_variable expr_in_object.instance_variable_scope
    |> activate_object obj
  in
  eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr_in_object.expr

and eval_obj_send fillings loc prims lookup_exp_typed trace_state frame_no obj meth =
  match SMap.find meth.txt (lookup_viewed_object obj).methods with
    | exception Not_found ->
       mismatch loc; assert false
    | expr_in_object ->
       eval_expr_in_object fillings prims lookup_exp_typed trace_state frame_no obj expr_in_object

and eval_obj_override fillings prims env lookup_exp_typed trace_state frame_no obj fields =
  let override_field (x, e) obj =
    let v = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
    { obj with variables = SMap.add x.txt (ref v) obj.variables } in
  let obj = List.fold_right override_field fields obj in
  obj

and eval_class_expr fillings prims env lookup_exp_typed trace_state frame_no class_expr =
  (* To avoid redundancy we express evaluation of class expressions by
     rewriting the non-base cases into usual expressions (fun => fun,
     etc.).  For example

    new (fun x -> <clexp>)
    =>
    fun x -> new <clexp>
  *)
  let eval_as_exp exp_desc =
    eval_expr fillings prims env lookup_exp_typed trace_state frame_no {
        pexp_desc = exp_desc;
        pexp_loc = class_expr.pcl_loc;
        pexp_attributes = class_expr.pcl_attributes;
    } in
  let new_ class_exp =
    (* The expression construction (new <class>) only accepts a class
       *identifier* (new <lid>), not a general class expression (new
       <clexp>), and we need the latter in our rewrite rules.

       This function uses a boilerplaty construction to turn an arbitrary
       class expression into a class identifier:

         new <cle>

       is defined as

         let module M = struct class cl = <cle> end in
         new M.cl
     *)
    let open Ast_helper in
    let noloc = Location.mknoloc in
    let modname = "<class_exp_mod>" in
    let clname = "<class_exp>" in
    Exp.letmodule (noloc modname)
      (Mod.structure [Str.class_ [Ci.mk (noloc clname) class_exp]])
      (Exp.new_ (noloc (Longident.(Ldot (Lident modname, clname)))))
  in
  match class_expr.pcl_desc with
  | Pcl_constr (lid, _type_args) ->
     eval_as_exp (Pexp_new lid)
  | Pcl_fun (arg, def, pat, cle) ->
     eval_as_exp (Pexp_fun (arg, def, pat, new_ cle))
  | Pcl_apply (cle, args) ->
     eval_as_exp (Pexp_apply (new_ cle, args))
  | Pcl_let (rec_flag, bindings, cle) ->
     eval_as_exp (Pexp_let (rec_flag, bindings, new_ cle))
  | Pcl_constraint (cle, _cty) ->
     eval_obj_new fillings prims env lookup_exp_typed trace_state frame_no cle
  | Pcl_open (ov_flag, open_, cle) ->
     eval_as_exp (Pexp_open (ov_flag, open_, new_ cle))
  | Pcl_extension _ ->
     unsupported class_expr.pcl_loc; assert false
  | Pcl_structure class_structure ->
     let obj = eval_class_structure fillings prims env lookup_exp_typed trace_state frame_no class_expr.pcl_loc class_structure in
     new_vtrace @@ Object obj

and eval_class_structure fillings prims env lookup_exp_typed trace_state frame_no loc class_structure =
  let eval_obj_field ((rev_inits,
                       parents, parents_in_scope,
                       variables, variables_in_scope,
                       methods) as state) class_field =
    let in_object expr = {
        source = Current_object;
        instance_variable_scope = variables_in_scope;
        named_parents_scope = parents_in_scope;
        expr;
      } in
    match class_field.pcf_desc with
    | Pcf_val (lab, _mut_flag, Cfk_virtual _) ->
       (* we chose to ignore virtual variables and methods in object values;
          it would be possible to give a more precise description by storing
          them as fields without a value *)
       (rev_inits,
        parents,
        SSet.remove lab.txt parents_in_scope,
        variables,
        variables_in_scope,
        methods)
    | Pcf_val (lab, _mut_flag, Cfk_concrete (_ov_flag, expr)) ->
       let v = eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr in
       (rev_inits,
        parents,
        SSet.remove lab.txt parents_in_scope,
        SMap.add lab.txt (ref v) variables,
        SSet.add lab.txt variables_in_scope,
        methods)
    | Pcf_method (_lab, _priv_flag, Cfk_virtual _) ->
        state
    | Pcf_method (lab, _priv_flag, Cfk_concrete (_ov_flag, expr)) ->
       (rev_inits,
        parents, parents_in_scope,
        variables, variables_in_scope,
        SMap.add lab.txt (in_object expr) methods)
    | Pcf_initializer expr ->
       (in_object expr :: rev_inits,
        parents, parents_in_scope,
        variables, variables_in_scope,
        methods)
    | Pcf_inherit (_ov_flag, class_expr, parent_name) ->
       let in_parent parent expr_in_object =
         match expr_in_object.source with
           | Parent _ -> expr_in_object
           | Current_object -> { expr_in_object with source = Parent parent } in
       begin match eval_class_expr fillings prims env lookup_exp_typed trace_state frame_no class_expr with
         | { v_ = Object parent; _ } ->
            let rev_inits =
              let parent_initializers =
                List.map (in_parent parent) parent.initializers in
              List.rev_append parent_initializers rev_inits in
            let parents, parents_in_scope = match parent_name with
                | None -> parents, parents_in_scope
                | Some name ->
                   SMap.add name.txt parent parents,
                   SSet.add name.txt parents_in_scope in
            let variables =
              SMap.union (fun _k _old new_ -> Some new_)
              variables
              parent.variables
            in
            let set_of_keys dict =
              SMap.to_seq dict
              |> Seq.map fst
              |> SSet.of_seq in
            let variables_in_scope =
              (* first add the parent variables *)
              SSet.union variables_in_scope
                (set_of_keys parent.variables) in
            let variables_in_scope =
              (* then remove the 'super' name if any *)
              match parent_name with
                | None -> variables_in_scope
                | Some name ->
                   SSet.remove name.txt variables_in_scope in
            let methods =
              SMap.union (fun _k _old new_ -> Some new_)
              methods
              (SMap.map (in_parent parent) parent.methods)
            in
            (rev_inits,
             parents, parents_in_scope,
             variables, variables_in_scope,
             methods)
         | _ -> mismatch loc; assert false
       end
    | Pcf_constraint _ ->
       state
    | Pcf_attribute _ ->
       state
    | Pcf_extension _ ->
       unsupported loc; assert false
  in
  let self = class_structure.pcstr_self in
  let fields = class_structure.pcstr_fields in
  let (rev_inits,
       parents, _parents_in_scope,
       variables, _variables_in_scope,
       methods) =
    List.fold_left eval_obj_field
      ([],
       SMap.empty, SSet.empty,
       SMap.empty, SSet.empty,
       SMap.empty) fields in
  {
    env;
    self;
    named_parents = parents;
    initializers = List.rev rev_inits;
    variables;
    methods;
    parent_view = [];
  }

and eval_obj_initializers fillings prims _env lookup_exp_typed trace_state frame_no obj =
  let eval_init expr =
    Runtime_base.unwrap_unit (eval_expr_in_object fillings prims lookup_exp_typed trace_state frame_no obj expr) in
  List.iter eval_init obj.initializers

and eval_obj_new fillings prims env lookup_exp_typed trace_state frame_no class_expr =
  match eval_class_expr fillings prims env lookup_exp_typed trace_state frame_no class_expr with
    | { v_ = Object obj; _ } as v ->
       eval_obj_initializers fillings prims env lookup_exp_typed trace_state frame_no obj;
       v
    | other ->
       (* Class expressions may validly return non-Obj values,
          which have nothing to initialize. For example,
              (new (fun x -> foo x))
          returns the value of
              (fun x -> new (foo x))
          as a closure, which does not initialize.
        *)
       other

and eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me =
  match me.pmod_desc with
  | Pmod_ident lident -> env_get_module env lident
  | Pmod_structure str -> Module (make_module_data (eval_structure fillings prims env lookup_exp_typed trace_state frame_no str))
  | Pmod_functor ({ txt = arg_name; _ }, _, e) -> Functor (arg_name, e, env)
  | Pmod_constraint (me, _) -> eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me
  | Pmod_apply (me1, me2) ->
    let m1 = eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me1 in
    let m2 = eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me2 in
    let arg_name, body, env = eval_functor_data env me.pmod_loc m1 in
    eval_module_expr fillings prims (env_set_module arg_name m2 env) lookup_exp_typed trace_state frame_no body
  | Pmod_unpack e ->
    (match eval_expr fillings prims env lookup_exp_typed trace_state frame_no e with
    | { v_ = ModVal m; _ } -> m
    | _ -> mismatch me.pmod_loc; assert false)
  | Pmod_extension _ -> unsupported me.pmod_loc; assert false

and eval_functor_data _env _loc = function
  | Module _ -> failwith "tried to apply a simple module"
  | Unit _ -> failwith "tried to apply a simple module unit"
  | Functor (arg_name, body, env) -> (arg_name, body, env)

and eval_structitem ?fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no it =
  match it.pstr_desc with
  | Pstr_eval (e, _) ->
    let f () = eval_expr fillings prims env lookup_exp_typed trace_state frame_no e in
    let v =
      begin match fuel_per_binding with
      | None      -> f ()
      | Some fuel -> with_fuel fuel f (fun () -> new_vtrace Bomb) (* If out of fuel, value is Bomb *)
      end
    in
    Format.printf "%a@." pp_print_value v;
    env
  | Pstr_value (recflag, defs) -> eval_bindings ?fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no recflag defs
  | Pstr_primitive { pval_name = { txt = name; loc }; pval_prim = l; _ } ->
    let prim_name = List.hd l in
    let prim =
      try SMap.find prim_name prims
      with Not_found ->
        new_vtrace @@ Prim
          (prim_name, fun _ ->
            Format.eprintf "Unimplemented primitive %s as %s %a@." prim_name name Location.print_loc loc;
            failwith ("Unimplemented primitive " ^ prim_name))
    in
    env_set_value name prim env
  | Pstr_type (_, tl) ->
    List.fold_left
      (fun env t ->
        match t.ptype_kind with
        | Ptype_variant l ->
          let _, _, env =
            List.fold_left
              (fun (u, v, env) cd ->
                match cd.pcd_args with
                | Pcstr_tuple [] ->
                  (u + 1, v, env_set_constr cd.pcd_name.txt u env)
                | _ -> (u, v + 1, env_set_constr cd.pcd_name.txt v env))
              (0, 0, env)
              l
          in
          env
        | _ -> env)
      env
      tl
  | Pstr_typext _ -> env
  | Pstr_exception { pext_name = name; pext_kind = k; _ } ->
    (match k with
    | Pext_decl _ ->
      let d = next_exn_id () in
      env_set_constr name.txt d env
    | Pext_rebind path -> env_set_constr name.txt (env_get_constr env path) env)
  | Pstr_module { pmb_name = name; pmb_expr = me; _ } ->
     env_set_module name.txt (eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me) env
  | Pstr_recmodule _ -> unsupported it.pstr_loc; assert false
  | Pstr_modtype _ -> env
  | Pstr_open { popen_lid = lident; _ } ->
    env_extend false env (env_get_module_data env lident)
  | Pstr_class class_decls ->
     let forward_env = ref env in
     let add_class class_decl env =
       let name = class_decl.pci_name.txt in
       let class_expr = class_decl.pci_expr in
       env_set_class name (class_expr, forward_env) env in
     let env = List.fold_right add_class class_decls env in
     forward_env := env;
     env
  | Pstr_class_type _ -> env
  | Pstr_include { pincl_mod = me; pincl_loc = loc; _ } ->
    let m = eval_module_expr fillings prims env lookup_exp_typed trace_state frame_no me in
    env_extend true env (get_module_data loc m)
  | Pstr_attribute _ -> env
  | Pstr_extension _ -> unsupported it.pstr_loc; assert false

and eval_structure_ ?fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no str =
  match str with
  | [] -> env
  | it :: str ->
    eval_structure_
      ?fuel_per_binding
      fillings
      prims
      (eval_structitem ?fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no it)
      lookup_exp_typed
      trace_state
      frame_no
      str

and eval_structure ?fuel_per_binding fillings prims env lookup_exp_typed trace_state frame_no str =
  eval_structure_ ?fuel_per_binding fillings prims (prevent_export env) lookup_exp_typed trace_state frame_no str

let eval_expr_with_fuel_or_bomb fuel fillings prims env lookup_exp_typed trace_state frame_no expr =
  with_fuel fuel
    (fun _ -> eval_expr fillings prims env lookup_exp_typed trace_state frame_no expr)
    (fun _ -> new_vtrace Bomb)
