open Data
open Conf
open Eval
open Envir

let parse filename =
  let inc = open_in filename in
  let lexbuf = Lexing.from_channel inc in
  Location.init lexbuf filename;
  let parsed = Parse.implementation lexbuf in
  close_in inc;
  parsed

type env_flag = Open of Longident.t

let stdlib_flag = [Open (Longident.Lident "Stdlib")]
let no_stdlib_flag = []

let stdlib_units =
  let stdlib_path = stdlib_path () in
  let fullpath file = Filename.concat stdlib_path file in
  (no_stdlib_flag, fullpath "camlinternalFormatBasics.ml")
  ::
  (no_stdlib_flag, fullpath "stdlib.ml")
  ::
  List.map (fun file -> stdlib_flag, fullpath file) [
    "sys.ml";
    "char.ml";
    "seq.ml";
    "bytes.ml";
    "marshal.ml";
    "obj.ml";
    "callback.ml";
    "complex.ml";
    "float.ml";
    "string.ml";
    "bytesLabels.ml";
    "stringLabels.ml";
    "list.ml";
    "listLabels.ml";
    (* "ord.ml"; *)
    "set.ml";
    "map.ml";
    "uchar.ml";
    "buffer.ml";
    "stream.ml";
    "array.ml";
    "int64.ml";
    "nativeint.ml";
    "digest.ml";
    "random.ml";
    "camlinternalLazy.ml";
    "lazy.ml";
    "hashtbl.ml";
    "genlex.ml";
    "camlinternalFormat.ml";
    "printf.ml";
    "scanf.ml";
    "format.ml";
    "gc.ml";
    "camlinternalOO.ml";
    "oo.ml";
    "printexc.ml";
    "arrayLabels.ml";
    "sort.ml";
    "queue.ml";
    "int32.ml";
    "lexing.ml";
    "parsing.ml";
    "weak.ml";
    "ephemeron.ml";
    "spacetime.ml";
    "stack.ml";
    "arg.ml";
    "filename.ml";
    "bigarray.ml";
    "moreLabels.ml";
    "stdLabels.ml";
  ]

let eval_env_flag ~loc env flag =
  match flag with
  | Open module_ident ->
     let module_ident = Location.mkloc module_ident loc in
     env_extend (Some module_ident.txt) false env (env_get_module_data env module_ident |> snd)

let load_rec_units env flags_and_units =
  let unit_paths = List.map snd flags_and_units in
  let env = List.fold_left declare_unit env unit_paths in
  List.fold_left
    (fun global_env (flags, unit_path) ->
      let module_name = module_name_of_unit_path unit_path in
      if debug then Format.eprintf "Loading %s from %s@." module_name unit_path;
      let module_contents =
        let loc = Location.in_file unit_path in
        let local_env = List.fold_left (eval_env_flag ~loc) global_env flags in
        eval_structure Primitives.prims local_env (parse unit_path)
      in
      define_unit global_env unit_path (make_module_data module_contents))
    env
    flags_and_units

let stdlib_env () =
  let env = Runtime_base.initial_env in
  let env = load_rec_units env stdlib_units in
  env

module Compiler_files = struct
  let utils = List.map (Filename.concat "utils") [
    "config.ml";
    "misc.ml";
    "identifiable.ml";
    "numbers.ml";
    "arg_helper.ml";
    "clflags.ml";
    "tbl.ml";
    "profile.ml";
    "terminfo.ml";
    "ccomp.ml";
    "warnings.ml";
    "consistbl.ml";
    "strongly_connected_components.ml";
    "build_path_prefix_map.ml";
    "targetint.ml";
  ]

  let parsing = List.map (Filename.concat "parsing") [
    "asttypes.mli";
    "location.ml";
    "longident.ml";
    "parsetree.mli";
    "docstrings.ml";
    "syntaxerr.ml";
    "ast_helper.ml";
    "parser.ml";
    "lexer.ml";
    "parse.ml";
    "printast.ml";
    "pprintast.ml";
    "ast_mapper.ml";
    "ast_iterator.ml";
    "attr_helper.ml";
    "builtin_attributes.ml";
    "ast_invariants.ml";
    "depend.ml";
  ]

  let pure_typing = List.map (Filename.concat "typing") [
    "ident.ml";
    "outcometree.mli";
    "annot.mli";
    "path.ml";
    "primitive.ml";
    "types.ml";
    "btype.ml";
    "oprint.ml";
    "subst.ml";
    "predef.ml";
    "datarepr.ml";
    "cmi_format.ml";
    "env.ml";
    "typedtree.ml";
    "printtyped.ml";
    "ctype.ml";
    "printtyp.ml";
    "includeclass.ml";
    "mtype.ml";
    "envaux.ml";
    "includecore.ml";
    "typedtreeIter.ml";
    "typedtreeMap.ml";
    "tast_mapper.ml";
    "cmt_format.ml";
    "untypeast.ml";
    "includemod.ml";
    "typetexp.ml";
    "printpat.ml";
    "parmatch.ml";
    "stypes.ml";
    "typedecl.ml";
  ]

  let lambda = List.map (Filename.concat "bytecomp") [
    "lambda.ml";
  ]

  let more_typing = List.map (Filename.concat "typing") [
    "typeopt.ml";
    "typecore.ml";
    "typeclass.ml";
    "typemod.ml";
  ]

  let bytecomp = List.map (Filename.concat "bytecomp") [
    "cmo_format.mli";
    "printlambda.ml";
    "semantics_of_primitives.ml";
    "switch.ml";
    "matching.ml";
    "translobj.ml";
    "translattribute.ml";
    "translprim.ml";
    "translcore.ml";
    "translclass.ml";
    "translmod.ml";
    "simplif.ml";
    "runtimedef.ml";
    "meta.ml";
    "opcodes.ml";
    "bytesections.ml";
    "dll.ml";
    "symtable.ml";
  ]

  let driver = List.map (Filename.concat "driver") [
    "pparse.ml";
    "main_args.ml";
    "compenv.ml";
    "compmisc.ml";
    "compdynlink.mlno";
    "compplugin.ml";
    "makedepend.ml";
  ]

  let middle_end = List.map (Filename.concat "middle_end") [
    "base_types/id_types.ml";
    "base_types/linkage_name.ml";
    "base_types/compilation_unit.ml";
    "base_types/set_of_closures_id.ml";
    "base_types/variable.ml";
    "base_types/symbol.ml";
    "base_types/closure_element.ml";
    "base_types/closure_id.ml";
    "base_types/closure_origin.ml";
    "base_types/var_within_closure.ml";
    "base_types/set_of_closures_origin.ml";
    "base_types/tag.ml";
    "base_types/static_exception.ml";
    "base_types/mutable_variable.ml";
    "base_types/export_id.ml";
    "projection.ml";
    "allocated_const.ml";
    "parameter.ml";
    "flambda.ml";
    "flambda_iterators.ml";
    "internal_variable_names.ml";
    "debuginfo.ml";
    (* "default_inline.ml"; *)
    "flambda_utils.ml";
    "freshening.ml";
    "inlining_cost.ml";
    "effect_analysis.ml";
    "simple_value_approx.ml";
    "find_recursive_functions.ml";
    "inlining_stats.ml";
    "inline_and_simplify_aux.ml";
    "invariant_params.ml";
    "flambda_invariants.ml";
    "closure_conversion_aux.ml";
    "closure_conversion.ml";
    "lift_code.ml";
    "alias_analysis.ml";
    "inconstant_idents.ml";
    "lift_constants.ml";
    "share_constants.ml";
    "inline_and_simplify.ml";
    "remove_unused_closure_vars.ml";
    "ref_to_variables.ml";
    "initialize_symbol_to_let_symbol.ml";
    "lift_let_to_initialize_symbol.ml";
    "remove_unused_program_constructs.ml";
    "middle_end.ml";
  ]

  let asmcomp = List.map (Filename.concat "asmcomp") [
    "cmx_format.mli";
    "clambda.ml";
    "export_info.ml";
    "compilenv.ml";
    "import_approx.ml";

    "x86_ast.mli";
    "x86_proc.ml";
    "x86_dsl.ml";
    "x86_gas.ml";

    "arch.ml";
    "cmm.ml";
    "reg.ml";

    "debug/reg_with_debug_info.ml";
    "debug/reg_availability_set.ml";

    "mach.ml";
    "proc.ml";
    "interval.ml";
    "printcmm.ml";
    "printmach.ml";
    "debug/available_regs.ml";


    "selectgen.ml";
    "spacetime_profiling.ml";
    "selection.ml";

    "closure.ml";
    "strmatch.ml";
    "printclambda.ml";
    "un_anf.ml";
    "afl_instrument.ml";
    "cmmgen.ml";
    "linearize.ml";
    "branch_relaxation.ml";
    "emitaux.ml";
    "x86_masm.ml";
    "emit.ml";
    "comballoc.ml";
    "CSEgen.ml";
    "CSE.ml";
    "liveness.ml";
    "deadcode.ml";
    "split.ml";
    "spill.ml";
    "interf.ml";
    "coloring.ml";
    "reloadgen.ml";
    "reload.ml";
    "schedgen.ml";
    "scheduling.ml";
    "printlinear.ml";
    "traverse_for_exported_symbols.ml";
    "build_export_info.ml";
    "closure_offsets.ml";
    "flambda_to_clambda.ml";
    "asmgen.ml";
    "asmlink.ml";
    "asmlibrarian.ml";
    "export_info_for_pack.ml";
    "asmpackager.ml";
  ]

  let bytegen = List.map (Filename.concat "bytecomp") [
    "instruct.ml";
    "bytegen.ml";
    "printinstr.ml";
    "emitcode.ml";
    "bytelink.ml";
    "bytelibrarian.ml";
    "bytepackager.ml";
  ]

  let bytecode_main = List.map (Filename.concat "driver") [
    "errors.ml";
    "compile.ml";
    "main.ml";
  ]

  let native_main = List.map (Filename.concat "driver") [
    "opterrors.ml";
    "optcompile.ml";
    "optmain.ml";
  ]
end

let bytecode_compiler_units =
  let compiler_source_path = compiler_source_path () in
  let fullpath file = Filename.concat compiler_source_path file in
  List.map (fun modfile -> stdlib_flag, fullpath modfile)
  ( Compiler_files.utils
  @ Compiler_files.parsing
  @ Compiler_files.pure_typing
  @ Compiler_files.lambda
  @ Compiler_files.more_typing
  @ Compiler_files.bytecomp
  @ Compiler_files.driver
  @ Compiler_files.bytegen
  @ Compiler_files.bytecode_main
  )

let native_compiler_units =
  let compiler_source_path = compiler_source_path () in
  let fullpath file = Filename.concat compiler_source_path file in
  List.map (fun modfile -> stdlib_flag, fullpath modfile)
  ( Compiler_files.utils
  @ Compiler_files.parsing
  @ Compiler_files.pure_typing
  @ Compiler_files.lambda
  @ Compiler_files.more_typing
  @ Compiler_files.bytecomp
  @ Compiler_files.driver
  @ Compiler_files.middle_end
  @ Compiler_files.asmcomp
  @ Compiler_files.native_main
  )

let run_ocamlc () =
  ignore (load_rec_units (stdlib_env ()) bytecode_compiler_units)

let run_ocamlopt () =
  ignore (load_rec_units (stdlib_env ()) native_compiler_units)

let run_files files =
  (* let rev_files = ref [] in
  let anon_fun file = rev_files := file :: !rev_files in
  Arg.parse [] anon_fun "";
  let files = List.rev !rev_files in *)
  files
  |> List.map (fun file -> stdlib_flag, file)
  |> load_rec_units (stdlib_env ())
  |> ignore

let get_stats () =
  let open Shared.Ast in
  let open Shared.Util in
  clear_stats ();
  print_endline "============= BEGINNING STATISTICS COLLECTION =====================";
  ignore @@ load_rec_units (stdlib_env ()) native_compiler_units;
  print_endline "============= ANNOTATING FILES WITH VAR USAGE (FOR MANUAL VERIFICATION THAT WE ARE NOT CRAZY) =====================";
  native_compiler_units |> List.iter begin fun (_, unit_path) ->
    let parsed = parse unit_path in
    let _use_to_exp = function
      | FirstUse (n, _name) -> Exp.from_string @@ "First " ^ string_of_int n
      | Reuse (n, _name)    -> Exp.from_string @@ "Reuse " ^ string_of_int n
      | External lid        -> Exp.ident (Loc.mk lid)
    in
    let use2_to_exp = function
      | NthInEnv (n, _name) -> Exp.from_string @@ "NthInEnv " ^ string_of_int n
      | External2 lid       -> Exp.ident (Loc.mk lid)
    in
    let annotated =
      parsed |> Exp.map begin fun exp ->
        match exp.pexp_desc with
        | Pexp_ident _ ->
          begin match Loc_map.find_opt exp.pexp_loc stats.var_uses2 with
          | Some var_use2 -> { exp with pexp_attributes = Attr.set_exp "use" (use2_to_exp var_use2) exp.pexp_attributes }
          | None -> exp
          end
        | _ -> exp
      end
    in
    write_file (StructItems.to_string annotated) (Filename.concat "annotated" (Filename.basename unit_path))
  end;
  stats



(* let _ = load_rec_units stdlib_env [stdlib_flag, "test.ml"] *)
(* let () = *)
  (* run_files () *)
  (* print_endline "hello"; *)
  (* let open Conf in
  try match Conf.command () with
    | Some cmd ->
      begin match cmd with
        | Ocamlc -> run_ocamlc ()
        | Ocamlopt -> run_ocamlopt ()
        | Files -> print_endline "running files ()";
      end
    | None -> run_ocamlc ()
  with InternalException e ->
    Format.eprintf "Code raised exception: %a@." pp_print_value e *)
