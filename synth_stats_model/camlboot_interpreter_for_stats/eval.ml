open Shared.Util

open Asttypes
open Parsetree

(* open Conf *)
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

(* let rec apply prims vf args =
  let vf, extral, extram =
    match Ptr.get vf with
    | Fun_with_extra_args (vf, extral, extram) -> (vf, extral, extram)
    | _ -> (vf, [], SMap.empty)
  in
  assert (extral = []);
  (* let ls = fun_label_shape vf in *)
  let apply_labelled vf (lab, arg) =
    match Ptr.get vf with
    | Fun (label, default, p, e, fenv) ->
      (match (label, lab, default) with
      | Optional s, Labelled s', None ->
        assert (s = s');
        eval_expr
          prims
          (pattern_bind prims fenv p (ptr @@ Constructor ("Some", 0, Some arg)))
          e
      | Optional s, Labelled s', Some _
      | Optional s, Optional s', None
      | Labelled s, Labelled s', None ->
        assert (s = s');
        eval_expr prims (pattern_bind prims fenv p arg) e
      | Optional s, Optional s', Some def ->
        assert (s = s');
        let arg =
          match Ptr.get arg with
          | Constructor ("None", 0, None) -> eval_expr prims fenv def
          | Constructor ("Some", 0, Some arg) -> arg
          | _ -> assert false
        in
        eval_expr prims (pattern_bind prims fenv p arg) e
      | _ -> assert false)
    | _ -> assert false
  in
  let apply_optional_noarg vf =
    match Ptr.get vf with
    | Fun (Optional _, None, p, e, fenv) ->
      eval_expr
        prims
        (pattern_bind prims fenv p (ptr @@ Constructor ("None", 0, None)))
        e
    | Fun (Optional _, Some def, p, e, fenv) ->
      eval_expr
        prims
        (pattern_bind prims fenv p (eval_expr prims fenv def))
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
    match Ptr.get vf with
    | Fun (Nolabel, _default, p, e, fenv) ->
      eval_expr prims (pattern_bind prims fenv p arg) e
    | Fun (((Labelled s | Optional s) as lab), _default, p, e, fenv) ->
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
      else eval_expr prims (pattern_bind prims fenv p arg) e
    | Function (cl, fenv) -> eval_match prims fenv cl (Ok arg)
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
        match Ptr.get vf with
        | Fun (((Labelled s | Optional s) as lab), _default, _p, _e, _fenv) ->
          if SMap.mem s !with_label
          then (
            let v = SMap.find s !with_label in
            with_label := SMap.remove s !with_label;
            apply_loop (apply_labelled vf v))
          else (
            assert (lab = Optional s);
            apply_loop (apply_optional_noarg vf))
        | _ -> ptr @@ Fun_with_extra_args (vf, [], !with_label))
    in
    apply_loop vf) *)

let rec eval_expr prims env expr : unit =
  (* if Conf.debug then print_endline (Pprintast.string_of_expression expr); *)
  let remove_stdlib_prefix lid =
    match Longident.flatten lid with
    | "Stdlib"::lid -> (match Longident.unflatten lid with Some lid -> lid | _ -> failwith "adsflashfasdhfladskf")
    | _             -> lid
  in
  match expr.pexp_desc with
  | Pexp_ident lid ->
    (* let _, new_prefix, mod_env, name = decompose env_get_module_data env lid in *)
    (* print_endline (Shared.Ast.Exp.to_string expr); *)
    (* print_endline (Shared.Ast.Longident.to_string new_prefix) *)
    let name = Longident.last lid.txt in
    begin try
      let (full_mod_path_opt, val_or_lvar) = env_get_value_or_lvar env lid in
      (* print_endline name; *)
      (* let (_exported, source_mod_path, val_or_lvar) = List.assoc name mod_env.values in *)
      (* let full_mod_path_opt = append_lident_opts new_prefix source_mod_path in *)
      let nth_in_env =
        if full_mod_path_opt = None then
          begin match env.values |> List.findi_opt (fun (name', _) -> name = name') with
          | Some i -> i
          | None   -> -1
          end
        else
          -1
      in
      (* var_uses v1 *)
      begin match val_or_lvar, full_mod_path_opt with
      | Value ({ contents = None } as last_use_ref, _intro_loc), None ->
        (* Var is unqualified. First use. *)
        (* Count the number of unused vars before it in the env *)
        let newer_env_vars = env.values |> List.take_while (fun (k, _) -> name <> k) in
        let newer_unused_count =
          let count = ref 0 in
          newer_env_vars |> List.iter begin fun (_, (_exported, source_mod_path, val_or_lvar)) ->
            match val_or_lvar with
            | Value ({ contents = None }, _intro_loc)
              when source_mod_path = None -> incr count
            | _ -> ()
          end;
          !count
        in
        let use  = FirstUse (newer_unused_count + 1, name) in
        let use2 = NthInEnv (nth_in_env, name) in
        stats.local_ident_count <- 1 + stats.local_ident_count;
        stats.local_idents      <- use  :: stats.local_idents;
        stats.local_idents2     <- use2 :: stats.local_idents2;
        stats.var_uses          <- Loc_map.add expr.pexp_loc use  stats.var_uses;
        stats.var_uses2         <- Loc_map.add expr.pexp_loc use2 stats.var_uses2;
        last_use_ref := Some expr.pexp_loc
      | Value ({ contents = Some var_most_recent_use_loc } as last_use_ref, _intro_loc), None ->
        (* Var is unqualified. Reuse *)
        (* Sort the env variables by most recent use locations and mark the var as a copy of nth most recently used variable *)
        let more_recently_used_vars =
          env.values
          |>@& begin fun (name, (_exported, source_mod_path, val_or_lvar)) ->
            match val_or_lvar with
            | Value ({ contents = Some use_loc }, _intro_loc)
              when source_mod_path = None
              && use_loc.loc_start.pos_fname = var_most_recent_use_loc.loc_start.pos_fname ->
                Some (use_loc, name)
            | _ -> None
          end
          |> List.sort begin fun (use_loc1, _) (use_loc2, _) -> (* Most recent first. *)
            -(Shared.Ast.Loc.compare use_loc1 use_loc2)
          end
          |> List.take_while (fun (use_loc, _) -> use_loc <> var_most_recent_use_loc)
        in
        let use = Reuse (List.length more_recently_used_vars + 1, name) in
        let use2 = NthInEnv (nth_in_env, name) in
        stats.local_ident_count <- 1 + stats.local_ident_count;
        stats.local_idents      <- use  :: stats.local_idents;
        stats.local_idents2     <- use2 :: stats.local_idents2;
        stats.var_uses          <- Loc_map.add expr.pexp_loc use  stats.var_uses;
        stats.var_uses2         <- Loc_map.add expr.pexp_loc use2 stats.var_uses2;
        last_use_ref := Some expr.pexp_loc
      | Value (_last_use_ref, _intro_loc), Some full_mod_path ->
        (* Var is qualified. *)
        let full_lid = Longident.Ldot (full_mod_path, name) in
        let use  = External full_lid in
        let use2 = External2 full_lid in
        stats.name_expansions      <- Loc_map.add lid.loc full_lid stats.name_expansions;
        stats.external_ident_count <- 1 + stats.external_ident_count;
        stats.var_uses             <- Loc_map.add expr.pexp_loc use  stats.var_uses;
        stats.var_uses2            <- Loc_map.add expr.pexp_loc use2 stats.var_uses2;
        begin if List.hd (Longident.flatten full_lid) = "Stdlib" then
          stats.stdlib_idents <- remove_stdlib_prefix full_lid :: stats.stdlib_idents
        end;
        | _ -> ()
      end;
    with Not_found ->
      print_endline name;
      (* eeeestimation. *)
      begin match lid.txt with
      | Longident.Ldot _ ->
        let use = External lid.txt in
        stats.var_uses <- Loc_map.add expr.pexp_loc use stats.var_uses
      | _ -> ()
      end;
      if name <> "self" then begin
        Format.eprintf
          "%a@. %s not found"
          Location.print_loc
          expr.pexp_loc
          name;
        (* raise Not_found *)
      end
    end
  | Pexp_constant (Parsetree.Pconst_integer (_, _)) -> stats.const_ints   <- expr :: stats.const_ints;   stats.const_int_count   <- 1 + stats.const_int_count
  | Pexp_constant (Parsetree.Pconst_char _)         -> stats.const_chars  <- expr :: stats.const_chars;  stats.const_char_count  <- 1 + stats.const_char_count
  | Pexp_constant (Parsetree.Pconst_string  (_, _)) -> stats.const_strs   <- expr :: stats.const_strs;   stats.const_str_count   <- 1 + stats.const_str_count
  | Pexp_constant (Parsetree.Pconst_float   (_, _)) -> stats.const_floats <- expr :: stats.const_floats; stats.const_float_count <- 1 + stats.const_float_count
  | Pexp_let (recflag, vals, e) ->
    stats.let_count <- 1 + stats.let_count;
    eval_expr prims (eval_bindings prims env recflag vals) e
  | Pexp_function cases ->
    stats.fun_count <- 1 + stats.fun_count;
    stats.match_count <- 1 + stats.match_count;
    eval_cases prims env cases
  | Pexp_fun (_label, default, p, e) ->
    stats.fun_count <- 1 + stats.fun_count;
    begin match default with
    | Some e -> eval_expr prims env e
    | None -> ()
    end;
    eval_expr prims (pattern_bind prims env p) e
  | Pexp_apply (f, l) ->
    stats.app_count <- 1 + stats.app_count;
    eval_expr prims env f;
    l |>@ snd |> List.iter (eval_expr prims env)
  | Pexp_tuple l ->
    begin match List.length l with
    | 2 -> stats.tup2_count <- 1 + stats.tup2_count
    | 3 -> stats.tup3_count <- 1 + stats.tup3_count
    | 4 -> stats.tup4_count <- 1 + stats.tup4_count
    | 5 -> stats.tup5_count <- 1 + stats.tup5_count
    | _ -> ()
    end;
    l |> List.iter (eval_expr prims env)
  | Pexp_match (e, cases) ->
    stats.match_count <- 1 + stats.match_count;
    eval_expr prims env e;
    eval_cases prims env cases
  | Pexp_coerce (e, _, _)  -> eval_expr prims env e
  | Pexp_constraint (e, _) -> eval_expr prims env e
  | Pexp_sequence (e1, e2) ->
    eval_expr prims env e1;
    eval_expr prims env e2
  | Pexp_while (e1, e2) ->
    eval_expr prims env e1;
    eval_expr prims env e2
  | Pexp_for (p, e1, e2, _flag, e3) ->
    eval_expr prims env e1;
    eval_expr prims env e2;
    eval_expr prims (pattern_bind prims env p) e3
  | Pexp_ifthenelse (e1, e2, e3) ->
    stats.ite_count <- 1 + stats.ite_count;
    eval_expr prims env e1;
    eval_expr prims env e2;
    begin match e3 with
    | None -> ()
    | Some e3 -> eval_expr prims env e3
    end
  | Pexp_unreachable                                -> failwith "reached unreachable"
  | Pexp_try (e, cases) ->
    eval_expr prims env e;
    eval_cases prims env cases
  | Pexp_construct (c, e) ->
    let name = lident_name c.txt in
    let (full_mod_path_opt, _d) =
      try env_get_constr env c
      with Not_found ->
        ( begin match c.txt with Longident.Ldot (mod_path, _) -> Some mod_path | _ -> None end
        , -1
        )
    in
    (* Maniposynth_lib.Name.pervasives_ctor_names; *)
    begin match full_mod_path_opt with
      | Some mod_path ->
        let full_lid = Longident.Ldot (mod_path, name) in
        stats.name_expansions <- Loc_map.add c.loc full_lid stats.name_expansions;
        begin if List.hd (Longident.flatten full_lid) = "Stdlib" then begin
          stats.stdlib_ctors      <- remove_stdlib_prefix full_lid :: stats.stdlib_ctors;
          stats.stdlib_ctor_count <- 1 + stats.stdlib_ctor_count
        end else
          stats.nonstdlib_ctor_count <- 1 + stats.nonstdlib_ctor_count
        end
      | None ->
        if SSet.mem name Maniposynth_lib.Name.pervasives_ctor_names then begin
          stats.stdlib_ctors      <- Longident.Lident name :: stats.stdlib_ctors;
          stats.stdlib_ctor_count <- 1 + stats.stdlib_ctor_count
        end else
          stats.nonstdlib_ctor_count <- 1 + stats.nonstdlib_ctor_count
    end;
    begin match e with
    | None -> ()
    | Some e -> eval_expr prims env e
    end
  | Pexp_variant (_cn, e) ->
    stats.nonstdlib_ctor_count <- 1 + stats.nonstdlib_ctor_count;
    begin match e with
    | None -> ()
    | Some e -> eval_expr prims env e
    end
  | Pexp_record (r, e) ->
    stats.record_count <- 1 + stats.record_count;
    begin match e with
    | None -> ()
    | Some e -> eval_expr prims env e
    end;
    r |>@ snd |> List.iter (eval_expr prims env)
  | Pexp_field (e, { txt = _lident; _ }) ->
    stats.field_count <- 1 + stats.field_count;
    eval_expr prims env e
  | Pexp_setfield (e1, { txt = _lident; _ }, e2) ->
    eval_expr prims env e1;
    eval_expr prims env e2
  | Pexp_array l                                    -> l |> List.iter (eval_expr prims env)
  | Pexp_send (obj_expr, _meth) ->
    eval_expr prims env obj_expr
  | Pexp_new lid ->
     let (_source_mod_lid, (class_expr, class_env)) = env_get_class env lid in
     eval_obj_new prims !class_env class_expr
  | Pexp_setinstvar (_x, e) ->
    eval_expr prims env e
  | Pexp_override fields ->
    fields |>@ snd |> List.iter (eval_expr prims env)
  | Pexp_letexception ({ pext_name = name; pext_kind = k; _ }, e) ->
    let env' =
      match k with
      | Pext_decl _ ->
        let d = next_exn_id () in
        env_set_constr name.txt d env
      | Pext_rebind path ->
        env_set_constr name.txt (env_get_constr env path |> snd) env
    in
    eval_expr prims env' e
  | Pexp_letmodule (name, me, e) ->
    let (_, m) = eval_module_expr prims env me in
    eval_expr prims (env_set_module name.txt m env) e
  | Pexp_assert e ->
    eval_expr prims env e
  | Pexp_lazy e                                     -> eval_expr prims env e
  | Pexp_poly (e, _ty)                              -> eval_expr prims env e
  | Pexp_newtype                            (_, e)  -> eval_expr prims env e
  | Pexp_open                               (_, lident, e) ->
    let env' =
      match env_get_module_data env lident with
      | exception Not_found ->
        (* Module might be a .mli only *)
        env
      | (_, module_data) -> env_extend (Some lident.txt) false env module_data
    in
    eval_expr prims env' e
  | Pexp_object _                                   -> unsupported expr.pexp_loc; assert false
  | Pexp_pack me                                    -> ignore (eval_module_expr prims env me)
  | Pexp_extension _                                -> unsupported expr.pexp_loc; assert false

and bind_value prims env vb =
  eval_expr prims env vb.pvb_expr;
  pattern_bind prims env vb.pvb_pat

and eval_bindings prims env recflag defs =
  match recflag with
    | Nonrecursive ->
       List.fold_left (bind_value prims) env defs
    | Recursive ->
      (* let dummies = List.map (fun _ -> Ptr.dummy ()) defs in *)
      let declare env vb = pattern_bind prims env vb.pvb_pat in
      (* let define env vb =
        let v = eval_expr prims env vb.pvb_expr in
        Ptr.backpatch dummy (Ptr.get v) in *)
      let nenv = List.fold_left declare env defs in
      (* List.iter (define nenv) defs; *)
      nenv

and pattern_bind prims env pat =
  match pat.ppat_desc with
  | Ppat_any -> env
  | Ppat_var s -> env_set_value s () env
  | Ppat_alias (p, s) -> env_set_value s () (pattern_bind prims env p)
  | Ppat_constant _c ->
    env
  | Ppat_interval (_c1, _c2) ->
    env
  | Ppat_tuple l ->
    List.fold_left (pattern_bind prims) env l
  | Ppat_construct (_, None) | Ppat_variant (_, None) -> env
  | Ppat_construct (_, Some p) | Ppat_variant (_, Some p) -> pattern_bind prims env p
  | Ppat_record (rp, _) ->
    rp |>@ snd |> List.fold_left (pattern_bind prims) env
  | Ppat_array ps -> ps |> List.fold_left (pattern_bind prims) env
  | Ppat_or (p1, _p2) -> pattern_bind prims env p1
  | Ppat_constraint (p, _) -> pattern_bind prims env p
  | Ppat_type _ -> unsupported pat.ppat_loc; assert false
  | Ppat_lazy _ -> unsupported pat.ppat_loc; assert false
  | Ppat_unpack _name -> failwith "Ppat_unpack"
    (* (match Ptr.get v with
    | ModVal m -> env_set_module name.txt m env
    | _ -> mismatch pat.ppat_loc; assert false) *)
  | Ppat_exception p -> pattern_bind prims env p
  | Ppat_extension _ -> unsupported pat.ppat_loc; assert false
  | Ppat_open _ -> unsupported pat.ppat_loc; assert false

(* and pattern_bind_exn prims env pat v =
  match pat.ppat_desc with
  | Ppat_exception p -> pattern_bind prims env p v
  | _ -> raise Match_fail *)

(* and pattern_bind_checkexn prims env pat v =
  match v with
  | Ok v -> pattern_bind prims env pat v
  | Error v -> pattern_bind_exn prims env pat v *)

and eval_cases prims env cases =
  cases
  |> List.iter begin fun case ->
    let env' = pattern_bind prims env case.pc_lhs in
    begin match case.pc_guard with
    | None -> ()
    | Some guard -> eval_expr prims env' guard
    end;
    eval_expr prims env' case.pc_rhs
  end

(* and lookup_viewed_object obj =
  let rec lookup obj = function
    | [] -> obj
    | parent :: parent_view ->
       lookup (SMap.find parent obj.named_parents) parent_view
  in lookup obj obj.parent_view *)

(* and eval_expr_in_object prims obj expr_in_object =
  let expr_env = match expr_in_object.source with
      | Parent parent -> parent.env
      | Current_object -> (lookup_viewed_object obj).env
  in
  let bind_self obj env =
    let self_view = { obj with parent_view = [] } in
    let self_pattern = match expr_in_object.source with
      | Parent parent -> parent.self
      | Current_object -> (lookup_viewed_object obj).self in
    pattern_bind prims env self_pattern (ptr @@ Object self_view) in
  let add_parent obj name env =
    let parent_view =
      { obj with parent_view = name :: obj.parent_view } in
    env_set_value { txt = name; loc = Location.none } (ptr @@ Object parent_view) env in
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
  eval_expr prims env expr_in_object.expr *)

(* and eval_obj_send loc prims obj meth =
  match SMap.find meth.txt (lookup_viewed_object obj).methods with
    | exception Not_found ->
       mismatch loc; assert false
    | expr_in_object ->
       eval_expr_in_object prims obj expr_in_object *)

(* and eval_obj_override prims env obj fields =
  let override_field (x, e) obj =
    let v = eval_expr prims env e in
    { obj with variables = SMap.add x.txt (ref v) obj.variables } in
  let obj = List.fold_right override_field fields obj in
  obj *)

and eval_class_expr prims env class_expr =
  (* To avoid redundancy we express evaluation of class expressions by
     rewriting the non-base cases into usual expressions (fun => fun,
     etc.).  For example

    new (fun x -> <clexp>)
    =>
    fun x -> new <clexp>
  *)
  let eval_as_exp exp_desc =
    eval_expr prims env {
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
     eval_obj_new prims env cle
  | Pcl_open (ov_flag, open_, cle) ->
     eval_as_exp (Pexp_open (ov_flag, open_, new_ cle))
  | Pcl_extension _ ->
     unsupported class_expr.pcl_loc; assert false
  | Pcl_structure class_structure ->
     eval_class_structure prims env class_expr.pcl_loc class_structure

and eval_class_structure _prims _env _loc _class_structure =
  ()
  (* let eval_obj_field class_field =
    match class_field.pcf_desc with
    | Pcf_val (_lab, _mut_flag, Cfk_virtual _) -> ()
    | Pcf_val (_lab, _mut_flag, Cfk_concrete (_ov_flag, expr)) ->
      eval_expr prims env expr
    | Pcf_method (_lab, _priv_flag, Cfk_virtual _) ->
        ()
    | Pcf_method (_lab, _priv_flag, Cfk_concrete (_ov_flag, expr)) ->
      eval_expr prims env expr
    | Pcf_initializer expr ->
      eval_expr prims env expr
    | Pcf_inherit (_ov_flag, class_expr, _parent_name) ->
      eval_class_expr prims env class_expr
    | Pcf_constraint _ ->
       ()
    | Pcf_attribute _ ->
       ()
    | Pcf_extension _ ->
       unsupported loc; assert false
  in *)
  (* let self = class_structure.pcstr_self in *)
  (* let fields = class_structure.pcstr_fields in *)
  (* List.iter eval_obj_field fields; *)

(* and eval_obj_initializers prims _env obj =
  let eval_init expr =
    Runtime_base.unwrap_unit (eval_expr_in_object prims obj expr) in
  List.iter eval_init obj.initializers *)

and eval_obj_new prims env class_expr =
  eval_class_expr prims env class_expr
  (* match Ptr.get @@ eval_class_expr prims env class_expr with
    | Object obj ->
       eval_obj_initializers prims env obj;
       ptr @@ Object obj
    | other ->
       (* Class expressions may validly return non-Obj values,
          which have nothing to initialize. For example,
              (new (fun x -> foo x))
          returns the value of
              (fun x -> new (foo x))
          as a closure, which does not initialize.
        *)
       ptr @@ other *)

and eval_module_expr prims env me =
  match me.pmod_desc with
  | Pmod_ident lident ->
    begin try env_get_module env lident
    with Not_found ->
      (Some lident.txt, Module { mod_values = []; mod_modules = []; mod_constructors = []; mod_classes = [] })
    end
  | Pmod_structure str -> (None, Module (make_module_data (eval_structure prims env str)))
  | Pmod_functor ({ txt = arg_name; _ }, _, e) ->
    print_endline @@ "ignoring functor with arg " ^ arg_name;
    (* ignore (eval_module_expr prims env e); *)
    (None, Functor (arg_name, e, env))
  | Pmod_constraint (me, _) -> eval_module_expr prims env me
  | Pmod_apply (me1, me2) ->
    let m1 = eval_module_expr prims env me1 in
    let m2 = eval_module_expr prims env me2 in
    let arg_name, body, env = eval_functor_data env me.pmod_loc (snd m1) in
    eval_module_expr prims (env_set_module arg_name (snd m2) env) body
  | Pmod_unpack e ->
    eval_expr prims env e;
    print_endline "can't Pmod_unpack";
    (None, Module { mod_values = []; mod_modules = []; mod_constructors = []; mod_classes = [] })
    (* failwith "Pmod_unpack" *)
    (* (match Ptr.get @@ eval_expr prims env e with
    | ModVal m -> m
    | _ -> mismatch me.pmod_loc; assert false) *)
  | Pmod_extension _ -> unsupported me.pmod_loc; assert false

and eval_functor_data _env _loc = function
  | Module _ -> failwith "tried to apply a simple module"
  | Unit _ -> failwith "tried to apply a simple module unit"
  | Functor (arg_name, body, env) -> (arg_name, body, env)

and eval_structitem prims env it =
  (* print_endline @@ Pprintast.string_of_structure [it]; *)
  match it.pstr_desc with
  | Pstr_eval (e, _) ->
    let _v = eval_expr prims env e in
    (* Format.printf "%a@." pp_print_value v; *)
    env
  | Pstr_value (recflag, defs) -> eval_bindings prims env recflag defs
  | Pstr_primitive { pval_name; pval_prim = l; _ } ->
    let prim_name = List.hd l in
    let prim =
      try SMap.find prim_name prims
      with Not_found ->
        ptr @@ Prim
          (fun _ ->
            Format.eprintf "%a@." Location.print_loc pval_name.loc;
            failwith ("Unimplemented primitive " ^ prim_name))
    in
    env_set_value pval_name prim env
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
    | Pext_rebind path -> env_set_constr name.txt (env_get_constr env path |> snd) env)
  | Pstr_module { pmb_name = name; pmb_expr = me; _ } ->
     env_set_module name.txt (eval_module_expr prims env me |> snd) env
  | Pstr_recmodule _ -> unsupported it.pstr_loc; assert false
  | Pstr_modtype _ -> env
  | Pstr_open { popen_lid = lident; _ } ->
    env_extend (Some lident.txt) false env (env_get_module_data env lident |> snd)
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
    let m = eval_module_expr prims env me in
    env_extend None true env (get_module_data loc m |> snd)
  | Pstr_attribute _ -> env
  | Pstr_extension _ -> unsupported it.pstr_loc; assert false

and eval_structure_ prims env str =
  match str with
  | [] -> env
  | it :: str ->
    eval_structure_
      prims
      (eval_structitem prims env it)
      str

and eval_structure prims env str =
  eval_structure_ prims (prevent_export env) str
