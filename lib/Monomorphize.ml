(*
Need to add instrumentation skeleton before monomorphization, so that instrumentation records the original expr ids (locations). Fill in the skeleton after monomorphization.

Monomorphization:

Until no changes:
  1. Find a fully typed function application of a polymorphic function
      (1. find app  2. find f type  3. find f def  (4. check def type))

  2. Check if a monomorphic definition of that function exists, if so, replace and restart loop.
      (1. find f_monoNNN defs  2. check types  3. replace if reasonable)

  3. Copy function def to f_monoNNN and add type annotations on its arguments.
*)

let let_bound_idents_of_structure (structure : Typedtree.structure) : (Ident.t * string Location.loc * Types.type_expr) list =
  let idents_names_types = ref [] in
  let iterator =
    let gather_idents iterator (rec_flag, value_bindings) =
      idents_names_types := Typedtree.let_bound_idents_full value_bindings @ !idents_names_types;
      Tast_iterator.default_iterator.value_bindings iterator (rec_flag, value_bindings)
    in
    { Tast_iterator.default_iterator with value_bindings = gather_idents }
  in
  iterator.structure iterator structure;
  !idents_names_types

let simple_vars_of_structure (structure : Typedtree.structure) : (Ident.t * Longident.t Location.loc * Types.type_expr) list =
  let idents_names_types = ref [] in
  let iterator =
    let gather_idents iterator expr =
      let () =
        match expr.Typedtree.exp_desc with
        | Typedtree.Texp_ident (Pident ident, longident_loced, _type_value_desc) ->
            ignore (idents_names_types := (ident, longident_loced, expr.exp_type) :: !idents_names_types)
        | _ -> ()
      in
      Tast_iterator.default_iterator.expr iterator expr
    in
    { Tast_iterator.default_iterator with expr = gather_idents }
  in
  iterator.structure iterator structure;
  !idents_names_types


let tvar_str_opts_of_type (typ : Types.type_expr) : string option list =
  let open Types in
  let gather_idents idents typ =
    match typ.desc with
    | Tvar str_opt -> str_opt::idents
    | _ -> idents
  in
  Type_utils.deep_fold_type_expr gather_idents [] typ

(* let tvars_of_type (typ : Types.type_expr) : string option list =
  let open Types in
  let gather_tvars tvars typ =
    match typ.desc with
    | Tvar _ -> typ::tvars
    | _ -> tvars
  in
  Btype.fold_type_expr gather_tvars [] typ *)

let is_monomorphic (typ : Types.type_expr) : bool =
  (* Printtyp.raw_type_expr Format.std_formatter typ;
  Format.pp_print_newline Format.std_formatter ();
  print_endline (string_of_int (List.length (tvar_str_opts_of_type typ))); *)
  let result =
    tvar_str_opts_of_type typ
    |> List.for_all (function | None -> false | Some str -> not (Typetexp.valid_tyvar_name str))
  in
  (* print_endline (string_of_bool result); *)
  result

let rec all_args_monomorphic (typ : Types.type_expr) : bool =
  match typ.desc with
  | Types.Tlink typ -> all_args_monomorphic typ
  | Types.Tarrow (_label, l_type, r_type, _commutable) ->
      (* Printtyp.type_expr Format.std_formatter typ;
      Format.pp_print_newline Format.std_formatter (); *)
      is_monomorphic l_type && all_args_monomorphic r_type
  | _ -> true

(* let print_implementation_types (structure : Typedtree.structure) =
  let iterator =
    let print_expr_type iterator (expr : Typedtree.expression) =
      Format.pp_print_string Format.std_formatter "Expr\t";
      Location.print_loc Format.std_formatter expr.Typedtree.exp_loc;
      Format.pp_print_string Format.std_formatter "\t";
      Printtyp.type_expr Format.std_formatter expr.Typedtree.exp_type;
      Format.pp_print_newline Format.std_formatter ();
      Tast_iterator.default_iterator.expr iterator expr
    in
    let print_pat_type iterator pat =
      Format.pp_print_string Format.std_formatter "Pat\t";
      Location.print_loc Format.std_formatter pat.Typedtree.pat_loc;
      Format.pp_print_string Format.std_formatter "\t";
      Printtyp.type_expr Format.std_formatter pat.Typedtree.pat_type;
      Format.pp_print_newline Format.std_formatter ();
      Tast_iterator.default_iterator.pat iterator pat
    in
    { Tast_iterator.default_iterator with expr = print_expr_type; pat = print_pat_type }
  in
  iterator.structure iterator structure *)

let core_type_of_type_expr type_expr =
  Printtyp.Naming_context.enable false; (* print "nat" instead of "nat/2" *)
  let type_str = (Utils.formatter_to_stringifyer Printtyp.type_expr) type_expr in
  (* print_endline type_str; *)
  Printtyp.Naming_context.reset ();
  Parse.core_type (Lexing.from_string type_str)

let add_monomorphic_bindng_to_toplevel_phrases
    (phrases : Parsetree.toplevel_phrase list)
    (binding_pat_loc : Location.t)
    (mono_arrow_type : Types.type_expr)
    (mono_name : string)
  : Parsetree.toplevel_phrase list
  =
  let open Parsetree in
  let is_target_vb value_binding : bool =
    match value_binding.pvb_pat.ppat_desc with
    | Ppat_var { txt = _name; loc } ->
        (* Location.print_loc Format.std_formatter loc;
        Format.pp_print_newline Format.std_formatter ();
        Location.print_loc Format.std_formatter binding_pat_loc;
        Format.pp_print_newline Format.std_formatter (); *)
        loc = binding_pat_loc
    | _                            -> false
  in
  let monomorphize_vb value_binding : value_binding =
    let loc = Location.none in
    let rec monomorphize_fun expr mono_type =
      match expr with
      | [%expr fun [%p? arg] -> [%e? body]] ->
        (match mono_type with
        | [%type: [%t? arg_type] -> [%t? rest_type]] ->
          let body' = monomorphize_fun body rest_type in
          [%expr fun ([%p arg] : [%t arg_type]) -> [%e body']]
        | _ ->
          expr
        )
      | _ ->
        expr
    in
    { value_binding with pvb_pat  = Ast_helper.Pat.var (Location.mknoloc mono_name)
    ;                    pvb_expr = monomorphize_fun value_binding.pvb_expr (core_type_of_type_expr mono_arrow_type)
    }    
  in
  let map_structure_item structure_item =
    match structure_item.pstr_desc with
    | Pstr_value (rec_flag, value_bindings) ->
        let monomorphized_vb_opt =
          value_bindings
          |> List.find_map (fun value_binding ->
            if is_target_vb value_binding
            then Some (monomorphize_vb value_binding)
            else None
          )
        in
        (match monomorphized_vb_opt with
        | None -> [structure_item]
        | Some monomorphized_vb ->
            [ structure_item
            ; { structure_item with pstr_desc = Pstr_value (rec_flag, [monomorphized_vb]) }
            ]
        )
    | _ ->
        [structure_item]
  in
  phrases
  |> Ast_utils.structure_of_toplevel_phrases
  |> List.concat_map map_structure_item
  |> Ast_utils.toplevel_phrases_of_structure


let f scratch_file_path =
  let rec loop mono_counter ident_monotype_mononame_assoc =
    let (_, typed_structure) = Type_utils.final_env_and_typed_structure_of_file scratch_file_path in
    let let_bound_polymorphic_idents_names_types =
      let_bound_idents_of_structure typed_structure
      |> List.filter (fun (_ident, _binding_pat_str_loced, fun_type) ->
        (* Ident.print Format.std_formatter ident;
        Format.pp_print_newline Format.std_formatter ();
        Printtyp.type_expr Format.std_formatter fun_type;
        Format.pp_print_newline Format.std_formatter (); *)
        not (all_args_monomorphic fun_type) (* && binding_pat_str_loced.Location.txt <> "tracepoint" *)
      )
    in
    let var_idents_names_types = simple_vars_of_structure typed_structure in
    let fully_typed_usage_of_polymorphic_fun_with_let_bound_fun_ident_opt =
      var_idents_names_types
      |> List.find_map (fun (ident, longident_loced, ident_type) ->
        (* Ident.print Format.std_formatter ident;
        Format.pp_print_newline Format.std_formatter (); *)
        if not (all_args_monomorphic ident_type) then
          None
        else
          let mono_type = ident_type in
          (* Ident.print Format.std_formatter ident;
          Format.pp_print_newline Format.std_formatter ();
          Printtyp.type_expr Format.std_formatter mono_type;
          Format.pp_print_newline Format.std_formatter ();
          Printtyp.raw_type_expr Format.std_formatter mono_type;
          Format.pp_print_newline Format.std_formatter (); *)
          List_utils.assoc3_opt ident let_bound_polymorphic_idents_names_types
          |> Option.map (fun (binding_pat_str_loced, fun_type) -> (ident, longident_loced, mono_type, binding_pat_str_loced, fun_type))
      )
    in
    match fully_typed_usage_of_polymorphic_fun_with_let_bound_fun_ident_opt with
    | None ->
        (* Done. *)
        ()
    | Some (ident, longident_loced, mono_type, binding_pat_str_loced, _fun_type) ->
        (* Location.print_loc Format.std_formatter longident_loced.loc;
        Format.pp_print_newline Format.std_formatter ();
        Location.print_loc Format.std_formatter binding_pat_str_loced.loc;
        Format.pp_print_newline Format.std_formatter ();
        print_endline binding_pat_str_loced.txt; *)
        let existing_mono_name_opt =
          ident_monotype_mononame_assoc
          |> List.find_opt (fun (existing_ident, existing_mono_type, _mono_name) ->
            (* Printtyp.type_expr Format.std_formatter mono_type;
            Printtyp.type_expr Format.std_formatter existing_mono_type;
            Format.pp_print_newline Format.std_formatter ();
            Ident.print Format.std_formatter ident;
            Ident.print Format.std_formatter existing_ident;
            Format.pp_print_newline Format.std_formatter ();
            print_endline (string_of_bool @@ Ident.same ident existing_ident);
            print_endline (string_of_bool @@ Ctype.equal typed_structure.str_final_env true [mono_type] [existing_mono_type]); *)
            Ident.same ident existing_ident && Ctype.equal typed_structure.str_final_env true [mono_type] [existing_mono_type]
          )
          |> Option.map (fun (_, _, mono_name) -> mono_name)
        in
        let parsed_with_comments = Parse_unparse.parse_file scratch_file_path in
        (match existing_mono_name_opt with
        | None ->
            (* Copy function def to f_monoNNN and add type annotations on its arguments *)
            let mono_name = Longident.last longident_loced.txt ^ "_mono" ^ string_of_int mono_counter in
            let parsed_with_comments' =
              let ast' =
                add_monomorphic_bindng_to_toplevel_phrases parsed_with_comments.ast binding_pat_str_loced.loc mono_type mono_name
              in
              { parsed_with_comments with ast = ast' }
            in
            let out_str = Parse_unparse.unparse scratch_file_path parsed_with_comments' in
            (* print_string @@ out_str; *)
            Sys_utils.save_file scratch_file_path out_str;
            loop (mono_counter + 1) ((ident, mono_type, mono_name)::ident_monotype_mononame_assoc)            

        | Some mono_name ->
            let parsed_with_comments' =
              let ast' =
                let expr_id = Ast_id.of_loc longident_loced.loc in
                let expr'   = Ast_utils.Exp.var mono_name in
                Ast_utils.replace_expr_by_id ~expr_id ~expr' parsed_with_comments.ast
              in
              { parsed_with_comments with ast = ast' }
            in
            let out_str = Parse_unparse.unparse scratch_file_path parsed_with_comments' in
            (* print_string @@ out_str; *)
            Sys_utils.save_file scratch_file_path out_str;
            loop mono_counter ident_monotype_mononame_assoc
        )

  in
  loop 1 []
