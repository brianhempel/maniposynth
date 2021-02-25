open Asttypes
open Parsetree

open Conf
open Data
open Envir

exception Match_fail

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

let rec apply prims trace_state vf args =
  trace_state.Trace.frame_no <- trace_state.Trace.frame_no + 1;
  let frame_no = trace_state.frame_no in
  let vf, extral, extram =
    match vf with
    | Fun_with_extra_args (vf, extral, extram) -> (vf, extral, extram)
    | _ -> (vf, [], SMap.empty)
  in
  assert (extral = []);
  (* let ls = fun_label_shape vf in *)
  let apply_labelled vf (lab, arg) =
    match vf with
    | Fun (label, default, p, e, fenv_ref) ->
      (match (label, lab, default) with
      | Optional s, Labelled s', None ->
        assert (s = s');
        eval_expr
          prims
          (pattern_bind prims !fenv_ref trace_state frame_no p (Constructor ("Some", 0, Some arg)))
          trace_state
          frame_no
          e
      | Optional s, Labelled s', Some _
      | Optional s, Optional s', None
      | Labelled s, Labelled s', None ->
        assert (s = s');
        eval_expr prims (pattern_bind prims !fenv_ref trace_state frame_no p arg) trace_state frame_no e
      | Optional s, Optional s', Some def ->
        assert (s = s');
        let arg =
          match arg with
          | Constructor ("None", 0, None) -> eval_expr prims !fenv_ref trace_state frame_no def
          | Constructor ("Some", 0, Some arg) -> arg
          | _ -> assert false
        in
        eval_expr prims (pattern_bind prims !fenv_ref trace_state frame_no p arg) trace_state frame_no e
      | _ -> assert false)
    | _ -> assert false
  in
  let apply_optional_noarg vf =
    match vf with
    | Fun (Optional _, None, p, e, fenv_ref) ->
      eval_expr
        prims
        (pattern_bind prims !fenv_ref trace_state frame_no p (Constructor ("None", 0, None)))
        trace_state
        frame_no
        e
    | Fun (Optional _, Some def, p, e, fenv_ref) ->
      let fenv = !fenv_ref in
      eval_expr
        prims
        (pattern_bind prims fenv trace_state frame_no p (eval_expr prims fenv trace_state frame_no def))
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
    match vf with
    | Fun (Nolabel, _default, p, e, fenv_ref) ->
      eval_expr prims (pattern_bind prims !fenv_ref trace_state frame_no p arg) trace_state frame_no e
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
      else eval_expr prims (pattern_bind prims !fenv_ref trace_state frame_no p arg) trace_state frame_no e
    | Function (cl, fenv_ref) -> eval_match prims !fenv_ref trace_state frame_no cl (Ok arg)
    | Prim prim -> prim arg
    | _ ->
      Format.eprintf "%a@." pp_print_value vf;
      assert false
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
        match vf with
        | Fun (((Labelled s | Optional s) as lab), _default, _p, _e, _fenv) ->
          if SMap.mem s !with_label
          then (
            let v = SMap.find s !with_label in
            with_label := SMap.remove s !with_label;
            apply_loop (apply_labelled vf v))
          else (
            assert (lab = Optional s);
            apply_loop (apply_optional_noarg vf))
        | _ -> Fun_with_extra_args (vf, [], !with_label))
    in
    apply_loop vf)

and eval_expr prims env trace_state frame_no expr =
  let attach_trace value =
    let trace_entry = (expr.pexp_loc, frame_no, value) in
    trace_state.Trace.trace <- Trace.add trace_entry trace_state.Trace.trace;
    value
  in
  attach_trace @@
  match expr.pexp_desc with
  | Pexp_ident { txt = Longident.Lident "??"; _ } -> Bomb
  | Pexp_ident id ->
     begin match env_get_value_or_lvar env id with
       | Value v -> v
       | Instance_variable (obj, name) ->
          let var = SMap.find name obj.variables in
          !var
     end
  | Pexp_constant c -> value_of_constant c
  | Pexp_let (recflag, vals, e) ->
    eval_expr prims (eval_bindings prims env trace_state frame_no recflag vals) trace_state frame_no e
  | Pexp_function cl -> Function (cl, ref env)
  | Pexp_fun (label, default, p, e) -> Fun (label, default, p, e, ref env)
  | Pexp_apply (f, l) ->
    (match eval_expr prims env trace_state frame_no f with
    | Fexpr fexpr ->
      let loc = expr.pexp_loc in
      (match fexpr loc l with
      | None ->
        Format.eprintf "%a@.F-expr failure.@." Location.print_loc loc;
        assert false
      | Some expr -> eval_expr prims env trace_state frame_no expr)
    | func_value ->
      let args = List.map (fun (lab, e) -> (lab, eval_expr prims env trace_state frame_no e)) l in
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
      apply prims trace_state (func_value) args)
  | Pexp_tuple l ->
    let args = List.map (eval_expr prims env trace_state frame_no) l in
    Tuple args
  | Pexp_match (e, cl) -> eval_match prims env trace_state frame_no cl (eval_expr_exn prims env trace_state frame_no e)
  | Pexp_coerce (e, _, _) -> eval_expr prims env trace_state frame_no e
  | Pexp_constraint (e, _) -> eval_expr prims env trace_state frame_no e
  | Pexp_sequence (e1, e2) ->
    let _ = eval_expr prims env trace_state frame_no e1 in
    eval_expr prims env trace_state frame_no e2
  | Pexp_while (e1, e2) ->
    while is_true (eval_expr prims env trace_state frame_no e1) do
      ignore (eval_expr prims env trace_state frame_no e2)
    done;
    unit
  | Pexp_for (p, e1, e2, flag, e3) ->
    let v1 = Runtime_base.unwrap_int (eval_expr prims env trace_state frame_no e1) in
    let v2 = Runtime_base.unwrap_int (eval_expr prims env trace_state frame_no e2) in
    if flag = Upto
    then
      for x = v1 to v2 do
        let vx = Runtime_base.wrap_int x in
        ignore (eval_expr prims (pattern_bind prims env trace_state frame_no p vx) trace_state frame_no e3)
      done
    else
      for x = v1 downto v2 do
        let vx = Runtime_base.wrap_int x in
        ignore (eval_expr prims (pattern_bind prims env trace_state frame_no p vx) trace_state frame_no e3)
      done;
    unit
  | Pexp_ifthenelse (e1, e2, e3) ->
    if is_true (eval_expr prims env trace_state frame_no e1)
    then eval_expr prims env trace_state frame_no e2
    else (
      match e3 with
      | None -> unit
      | Some e3 -> eval_expr prims env trace_state frame_no e3)
  | Pexp_unreachable -> failwith "reached unreachable"
  | Pexp_try (e, cs) ->
    (try eval_expr prims env trace_state frame_no e
     with InternalException v ->
       (try eval_match prims env trace_state frame_no cs (Ok v)
        with Match_fail -> raise (InternalException v)))
  | Pexp_construct (c, e) ->
    let cn = lident_name c.txt in
    let d = env_get_constr env c in
    let ee =
      match e with
      | None -> None
      | Some e -> Some (eval_expr prims env trace_state frame_no e)
    in
    Constructor (cn, d, ee)
  | Pexp_variant (cn, e) ->
    let ee =
      match e with
      | None -> None
      | Some e -> Some (eval_expr prims env trace_state frame_no e)
    in
    Constructor (cn, Hashtbl.hash cn, ee)
  | Pexp_record (r, e) ->
    let base =
      match e with
      | None -> SMap.empty
      | Some e ->
        (match eval_expr prims env trace_state frame_no e with
        | Record r -> r
        | _ -> mismatch expr.pexp_loc; assert false)
    in
    Record
      (List.fold_left
         (fun rc ({ txt = lident; _ }, ee) ->
           SMap.add (lident_name lident) (ref (eval_expr prims env trace_state frame_no ee)) rc)
         base
         r)
  | Pexp_field (e, { txt = lident; _ }) ->
    (match eval_expr prims env trace_state frame_no e with
    | Record r -> !(SMap.find (lident_name lident) r)
    | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_setfield (e1, { txt = lident; _ }, e2) ->
    let v1 = eval_expr prims env trace_state frame_no e1 in
    let v2 = eval_expr prims env trace_state frame_no e2 in
    (match v1 with
    | Record r ->
      SMap.find (lident_name lident) r := v2;
      unit
    | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_array l -> Array (Array.of_list (List.map (eval_expr prims env trace_state frame_no) l))
  | Pexp_send (obj_expr, meth) ->
     let obj = eval_expr prims env trace_state frame_no obj_expr in
     (match obj with
      | Object obj -> eval_obj_send expr.pexp_loc prims trace_state frame_no obj meth
      | _ -> mismatch expr.pexp_loc; assert false)
  | Pexp_new lid ->
     let (class_expr, class_env) = env_get_class env lid in
     eval_obj_new prims !class_env trace_state frame_no class_expr
  | Pexp_setinstvar (x, e) ->
     let v = eval_expr prims env trace_state frame_no e in
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
          let new_obj = eval_obj_override prims env trace_state frame_no obj fields in
          Object new_obj
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
    eval_expr prims nenv trace_state frame_no e
  | Pexp_letmodule (name, me, e) ->
    let m = eval_module_expr prims env trace_state frame_no me in
    eval_expr prims (env_set_module name.txt m env) trace_state frame_no e
  | Pexp_assert e ->
    if is_true (eval_expr prims env trace_state frame_no e)
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
  | Pexp_lazy e -> Lz (ref (fun () -> eval_expr prims env trace_state frame_no e))
  | Pexp_poly (e, _ty) -> eval_expr prims env trace_state frame_no e
  | Pexp_newtype (_, e) -> eval_expr prims env trace_state frame_no e
  | Pexp_open (_, lident, e) ->
    let nenv =
      match env_get_module_data env lident with
      | exception Not_found ->
        (* Module might be a .mli only *)
        env
      | module_data -> env_extend false env module_data
    in
    eval_expr prims nenv trace_state frame_no e
  | Pexp_object _ -> unsupported expr.pexp_loc; assert false
  | Pexp_pack me -> ModVal (eval_module_expr prims env trace_state frame_no me)
  | Pexp_extension _ -> unsupported expr.pexp_loc; assert false

and eval_expr_exn prims env trace_state frame_no expr =
  try Ok (eval_expr prims env trace_state frame_no expr) with InternalException v -> Error v

and bind_value prims env trace_state frame_no vb =
  let v = eval_expr prims env trace_state frame_no vb.pvb_expr in
  pattern_bind prims env trace_state frame_no vb.pvb_pat v

and eval_bindings prims env trace_state frame_no recflag defs =
  match recflag with
    | Nonrecursive ->
      List.fold_left (fun env vb -> bind_value prims env trace_state frame_no vb) env defs
    | Recursive ->
      (* LHS of let rec is always a single variable *)
      (* What's allowed on the RHS is rather complicated (see classify_expression in typecore.ml) *)
      (* But, expressions that only reference non-rec variables are allowed. *)
      (* As are functions. That should cover everything practical, right? *)
      (* The following is allowed but odd:
        let rec ff =
          ( (fun () -> (fst ff) ())
          , (fun () -> (snd ff) ())
          )
        in
        ...
      *)
      (* let dummies = List.map (fun _ -> Ptr.dummy ()) defs in
      let declare env vb dummy =
        pattern_bind prims env trace_state frame_no vb.pvb_pat dummy in
      let define env vb dummy =
        let v = eval_expr prims env trace_state frame_no vb.pvb_expr in
        Ptr.backpatch dummy v in
      let nenv = List.fold_left2 declare env defs dummies in
      List.iter2 (define nenv) defs dummies; *)
      let rec_names =
        let single_name vb =
          let rec single_name p =
            match p.ppat_desc with
            | Ppat_var s             -> s.txt
            | Ppat_constraint (p, _) -> single_name p
            | _                      ->
              Format.eprintf "Only single vars are allowed on the LHS of a let rec: %a\n" Pprintast.pattern vb.pvb_pat;
              raise (InternalException (Runtime_base.failure_exn "Only single vars are allowed on the LHS of a let rec"))
          in
          single_name vb.pvb_pat
        in
        List.map single_name defs
      in
      (* let declare env vb =
        pattern_bind prims env trace_state frame_no vb.pvb_pat Bomb in *)
      let dummy_env = List.fold_left (fun env name -> env_set_value name Bomb env) env rec_names in
      let vals = List.map (fun vb -> eval_expr prims dummy_env trace_state frame_no vb.pvb_expr) defs in
      let nenv = List.fold_left2 (fun env name v -> env_set_value name v env) env rec_names vals in
      let rec packpatch_env = function
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

and pattern_bind prims env trace_state frame_no pat v =
  (* frame_no is passed in here because pattern matches can execute code, which will change the trace_state frame_no for later calls to pattern_bind *)
  (* (namely the str = "Format" case) *)
  let attach_trace value env =
    let trace_entry = (pat.ppat_loc, frame_no, value) in
    trace_state.trace <- Trace.add trace_entry trace_state.trace;
    env
  in
  attach_trace v @@
  match pat.ppat_desc with
  | Ppat_any -> env
  | Ppat_var s -> env_set_value s.txt v env
  | Ppat_alias (p, s) -> env_set_value s.txt v (pattern_bind prims env trace_state frame_no p v)
  | Ppat_constant c ->
    if value_equal (value_of_constant c) v then env else raise Match_fail
  | Ppat_interval (c1, c2) ->
    if value_le (value_of_constant c1) v && value_le v (value_of_constant c2)
    then env
    else raise Match_fail
  | Ppat_tuple l ->
    (match v with
    | Tuple vl ->
      assert (List.length l = List.length vl);
      List.fold_left2 (fun env -> pattern_bind prims env trace_state frame_no) env l vl
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_construct (c, p) ->
    let cn = lident_name c.txt in
    let dn = env_get_constr env c in
    (match v with
    | Constructor (ccn, ddn, e) ->
      if cn <> ccn then raise Match_fail;
      if dn <> ddn then raise Match_fail;
      (match (p, e) with
      | None, None -> env
      | Some p, Some e -> pattern_bind prims env trace_state frame_no p e
      | _ -> mismatch pat.ppat_loc; assert false)
    | String s ->
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
      let fmt = apply prims trace_state fmt_ebb_of_string [ (Nolabel, String s) ] in
      let fmt =
        match fmt with
        | Constructor ("Fmt_EBB", _, Some fmt) -> fmt
        | _ -> mismatch pat.ppat_loc; assert false
      in
      pattern_bind prims env trace_state frame_no p (Tuple [ fmt; v ])
    | _ ->
      Format.eprintf "cn = %s@.v = %a@." cn pp_print_value v;
      assert false)
  | Ppat_variant (name, p) ->
    (match v with
    | Constructor (cn, _, e) ->
      if cn <> name then raise Match_fail;
      (match (p, e) with
      | None, None -> env
      | Some p, Some e -> pattern_bind prims env trace_state frame_no p e
      | _ -> mismatch pat.ppat_loc; assert false)
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_record (rp, _) ->
    (match v with
    | Record r ->
      List.fold_left
        (fun env (lident, p) ->
          pattern_bind prims env trace_state frame_no p !(SMap.find (lident_name lident.txt) r))
        env
        rp
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_array ps ->
     (match v with
        | Array vs ->
           let vs = Array.to_list vs in
           if List.length ps <> List.length vs then raise Match_fail;
           List.fold_left2 (fun env p v -> pattern_bind prims env trace_state frame_no p v) env ps vs
        | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_or (p1, p2) ->
    (try pattern_bind prims env trace_state frame_no p1 v
     with Match_fail -> pattern_bind prims env trace_state frame_no p2 v)
  | Ppat_constraint (p, _) -> pattern_bind prims env trace_state frame_no p v
  | Ppat_type _ -> unsupported pat.ppat_loc; assert false
  | Ppat_lazy _ -> unsupported pat.ppat_loc; assert false
  | Ppat_unpack name ->
    (match v with
    | ModVal m -> env_set_module name.txt m env
    | _ -> mismatch pat.ppat_loc; assert false)
  | Ppat_exception _ -> raise Match_fail
  | Ppat_extension _ -> unsupported pat.ppat_loc; assert false
  | Ppat_open _ -> unsupported pat.ppat_loc; assert false

and pattern_bind_exn prims env trace_state frame_no pat v =
  match pat.ppat_desc with
  | Ppat_exception p -> pattern_bind prims env trace_state frame_no p v
  | _ -> raise Match_fail

and pattern_bind_checkexn prims env trace_state frame_no pat v =
  match v with
  | Ok v -> pattern_bind prims env trace_state frame_no pat v
  | Error v -> pattern_bind_exn prims env trace_state frame_no pat v

and eval_match prims env trace_state frame_no cl arg =
  match cl with
  | [] ->
    (match arg with
    | Ok _ -> raise Match_fail
    | Error v -> raise (InternalException v))
  | c :: cl ->
    (match pattern_bind_checkexn prims env trace_state frame_no c.pc_lhs arg with
    | exception Match_fail -> eval_match prims env trace_state frame_no cl arg
    | nenv ->
      let guard_ok =
        match c.pc_guard with
        | None -> true
        | Some guard -> is_true (eval_expr prims nenv trace_state frame_no guard)
      in
      if guard_ok
      then eval_expr prims nenv trace_state frame_no c.pc_rhs
      else eval_match prims env trace_state frame_no cl arg)

and lookup_viewed_object obj =
  let rec lookup obj = function
    | [] -> obj
    | parent :: parent_view ->
       lookup (SMap.find parent obj.named_parents) parent_view
  in lookup obj obj.parent_view

and eval_expr_in_object prims trace_state frame_no obj expr_in_object =
  let expr_env = match expr_in_object.source with
      | Parent parent -> parent.env
      | Current_object -> (lookup_viewed_object obj).env
  in
  let bind_self obj env =
    let self_view = { obj with parent_view = [] } in
    let self_pattern = match expr_in_object.source with
      | Parent parent -> parent.self
      | Current_object -> (lookup_viewed_object obj).self in
    pattern_bind prims env trace_state frame_no self_pattern (Object self_view) in
  let add_parent obj name env =
    let parent_view =
      { obj with parent_view = name :: obj.parent_view } in
    env_set_value name (Object parent_view) env in
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
  eval_expr prims env trace_state frame_no expr_in_object.expr

and eval_obj_send loc prims trace_state frame_no obj meth =
  match SMap.find meth.txt (lookup_viewed_object obj).methods with
    | exception Not_found ->
       mismatch loc; assert false
    | expr_in_object ->
       eval_expr_in_object prims trace_state frame_no obj expr_in_object

and eval_obj_override prims env trace_state frame_no obj fields =
  let override_field (x, e) obj =
    let v = eval_expr prims env trace_state frame_no e in
    { obj with variables = SMap.add x.txt (ref v) obj.variables } in
  let obj = List.fold_right override_field fields obj in
  obj

and eval_class_expr prims env trace_state frame_no class_expr =
  (* To avoid redundancy we express evaluation of class expressions by
     rewriting the non-base cases into usual expressions (fun => fun,
     etc.).  For example

    new (fun x -> <clexp>)
    =>
    fun x -> new <clexp>
  *)
  let eval_as_exp exp_desc =
    eval_expr prims env trace_state frame_no {
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
     eval_obj_new prims env trace_state frame_no cle
  | Pcl_open (ov_flag, open_, cle) ->
     eval_as_exp (Pexp_open (ov_flag, open_, new_ cle))
  | Pcl_extension _ ->
     unsupported class_expr.pcl_loc; assert false
  | Pcl_structure class_structure ->
     let obj = eval_class_structure prims env trace_state frame_no class_expr.pcl_loc class_structure in
     Object obj

and eval_class_structure prims env trace_state frame_no loc class_structure =
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
       let v = eval_expr prims env trace_state frame_no expr in
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
       begin match eval_class_expr prims env trace_state frame_no class_expr with
         | Object parent ->
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

and eval_obj_initializers prims _env trace_state frame_no obj =
  let eval_init expr =
    Runtime_base.unwrap_unit (eval_expr_in_object prims trace_state frame_no obj expr) in
  List.iter eval_init obj.initializers

and eval_obj_new prims env trace_state frame_no class_expr =
  match eval_class_expr prims env trace_state frame_no class_expr with
    | Object obj ->
       eval_obj_initializers prims env trace_state frame_no obj;
       Object obj
    | other ->
       (* Class expressions may validly return non-Obj values,
          which have nothing to initialize. For example,
              (new (fun x -> foo x))
          returns the value of
              (fun x -> new (foo x))
          as a closure, which does not initialize.
        *)
       other

and eval_module_expr prims env trace_state frame_no me =
  match me.pmod_desc with
  | Pmod_ident lident -> env_get_module env lident
  | Pmod_structure str -> Module (make_module_data (eval_structure prims env trace_state frame_no str))
  | Pmod_functor ({ txt = arg_name; _ }, _, e) -> Functor (arg_name, e, env)
  | Pmod_constraint (me, _) -> eval_module_expr prims env trace_state frame_no me
  | Pmod_apply (me1, me2) ->
    let m1 = eval_module_expr prims env trace_state frame_no me1 in
    let m2 = eval_module_expr prims env trace_state frame_no me2 in
    let arg_name, body, env = eval_functor_data env me.pmod_loc m1 in
    eval_module_expr prims (env_set_module arg_name m2 env) trace_state frame_no body
  | Pmod_unpack e ->
    (match eval_expr prims env trace_state frame_no e with
    | ModVal m -> m
    | _ -> mismatch me.pmod_loc; assert false)
  | Pmod_extension _ -> unsupported me.pmod_loc; assert false

and eval_functor_data _env _loc = function
  | Module _ -> failwith "tried to apply a simple module"
  | Unit _ -> failwith "tried to apply a simple module unit"
  | Functor (arg_name, body, env) -> (arg_name, body, env)

and eval_structitem prims env trace_state frame_no it =
  match it.pstr_desc with
  | Pstr_eval (e, _) ->
    let v = eval_expr prims env trace_state frame_no e in
    Format.printf "%a@." pp_print_value v;
    env
  | Pstr_value (recflag, defs) -> eval_bindings prims env trace_state frame_no recflag defs
  | Pstr_primitive { pval_name = { txt = name; loc }; pval_prim = l; _ } ->
    let prim_name = List.hd l in
    let prim =
      try SMap.find prim_name prims
      with Not_found ->
        Prim
          (fun _ ->
            Format.eprintf "%a@." Location.print_loc loc;
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
     env_set_module name.txt (eval_module_expr prims env trace_state frame_no me) env
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
    let m = eval_module_expr prims env trace_state frame_no me in
    env_extend true env (get_module_data loc m)
  | Pstr_attribute _ -> env
  | Pstr_extension _ -> unsupported it.pstr_loc; assert false

and eval_structure_ prims env trace_state frame_no str =
  match str with
  | [] -> env
  | it :: str ->
    eval_structure_
      prims
      (eval_structitem prims env trace_state frame_no it)
      trace_state
      frame_no
      str

and eval_structure prims env trace_state frame_no str =
  eval_structure_ prims (prevent_export env) trace_state frame_no str
