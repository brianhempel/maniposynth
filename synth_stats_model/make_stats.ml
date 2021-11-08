(* open Maniposynth_lib *)
open Shared.Ast
open Shared.Util

(* utop # Camlboot_interpreter.Interp.native_compiler_units () |>@ snd;; *)
let corpus_files =
  ["ocaml-4.07.1/utils/config.ml"; "ocaml-4.07.1/utils/misc.ml";
  "ocaml-4.07.1/utils/identifiable.ml"; "ocaml-4.07.1/utils/numbers.ml";
  "ocaml-4.07.1/utils/arg_helper.ml"; "ocaml-4.07.1/utils/clflags.ml";
  "ocaml-4.07.1/utils/tbl.ml"; "ocaml-4.07.1/utils/profile.ml";
  "ocaml-4.07.1/utils/terminfo.ml"; "ocaml-4.07.1/utils/ccomp.ml";
  "ocaml-4.07.1/utils/warnings.ml"; "ocaml-4.07.1/utils/consistbl.ml";
  "ocaml-4.07.1/utils/strongly_connected_components.ml";
  "ocaml-4.07.1/utils/build_path_prefix_map.ml";
  "ocaml-4.07.1/utils/targetint.ml"; "ocaml-4.07.1/parsing/asttypes.mli";
  "ocaml-4.07.1/parsing/location.ml"; "ocaml-4.07.1/parsing/longident.ml";
  "ocaml-4.07.1/parsing/parsetree.mli"; "ocaml-4.07.1/parsing/docstrings.ml";
  "ocaml-4.07.1/parsing/syntaxerr.ml"; "ocaml-4.07.1/parsing/ast_helper.ml";
  "ocaml-4.07.1/parsing/parser.ml"; "ocaml-4.07.1/parsing/lexer.ml";
  "ocaml-4.07.1/parsing/parse.ml"; "ocaml-4.07.1/parsing/printast.ml";
  "ocaml-4.07.1/parsing/pprintast.ml"; "ocaml-4.07.1/parsing/ast_mapper.ml";
  "ocaml-4.07.1/parsing/ast_iterator.ml"; "ocaml-4.07.1/parsing/attr_helper.ml";
  "ocaml-4.07.1/parsing/builtin_attributes.ml";
  "ocaml-4.07.1/parsing/ast_invariants.ml"; "ocaml-4.07.1/parsing/depend.ml";
  "ocaml-4.07.1/typing/ident.ml"; "ocaml-4.07.1/typing/outcometree.mli";
  "ocaml-4.07.1/typing/annot.mli"; "ocaml-4.07.1/typing/path.ml";
  "ocaml-4.07.1/typing/primitive.ml"; "ocaml-4.07.1/typing/types.ml";
  "ocaml-4.07.1/typing/btype.ml"; "ocaml-4.07.1/typing/oprint.ml";
  "ocaml-4.07.1/typing/subst.ml"; "ocaml-4.07.1/typing/predef.ml";
  "ocaml-4.07.1/typing/datarepr.ml"; "ocaml-4.07.1/typing/cmi_format.ml";
  "ocaml-4.07.1/typing/env.ml"; "ocaml-4.07.1/typing/typedtree.ml";
  "ocaml-4.07.1/typing/printtyped.ml"; "ocaml-4.07.1/typing/ctype.ml";
  "ocaml-4.07.1/typing/printtyp.ml"; "ocaml-4.07.1/typing/includeclass.ml";
  "ocaml-4.07.1/typing/mtype.ml"; "ocaml-4.07.1/typing/envaux.ml";
  "ocaml-4.07.1/typing/includecore.ml"; "ocaml-4.07.1/typing/typedtreeIter.ml";
  "ocaml-4.07.1/typing/typedtreeMap.ml"; "ocaml-4.07.1/typing/tast_mapper.ml";
  "ocaml-4.07.1/typing/cmt_format.ml"; "ocaml-4.07.1/typing/untypeast.ml";
  "ocaml-4.07.1/typing/includemod.ml"; "ocaml-4.07.1/typing/typetexp.ml";
  "ocaml-4.07.1/typing/printpat.ml"; "ocaml-4.07.1/typing/parmatch.ml";
  "ocaml-4.07.1/typing/stypes.ml"; "ocaml-4.07.1/typing/typedecl.ml";
  "ocaml-4.07.1/bytecomp/lambda.ml"; "ocaml-4.07.1/typing/typeopt.ml";
  "ocaml-4.07.1/typing/typecore.ml"; "ocaml-4.07.1/typing/typeclass.ml";
  "ocaml-4.07.1/typing/typemod.ml"; "ocaml-4.07.1/bytecomp/cmo_format.mli";
  "ocaml-4.07.1/bytecomp/printlambda.ml";
  "ocaml-4.07.1/bytecomp/semantics_of_primitives.ml";
  "ocaml-4.07.1/bytecomp/switch.ml"; "ocaml-4.07.1/bytecomp/matching.ml";
  "ocaml-4.07.1/bytecomp/translobj.ml";
  "ocaml-4.07.1/bytecomp/translattribute.ml";
  "ocaml-4.07.1/bytecomp/translprim.ml"; "ocaml-4.07.1/bytecomp/translcore.ml";
  "ocaml-4.07.1/bytecomp/translclass.ml"; "ocaml-4.07.1/bytecomp/translmod.ml";
  "ocaml-4.07.1/bytecomp/simplif.ml"; "ocaml-4.07.1/bytecomp/runtimedef.ml";
  "ocaml-4.07.1/bytecomp/meta.ml"; "ocaml-4.07.1/bytecomp/opcodes.ml";
  "ocaml-4.07.1/bytecomp/bytesections.ml"; "ocaml-4.07.1/bytecomp/dll.ml";
  "ocaml-4.07.1/bytecomp/symtable.ml"; "ocaml-4.07.1/driver/pparse.ml";
  "ocaml-4.07.1/driver/main_args.ml"; "ocaml-4.07.1/driver/compenv.ml";
  "ocaml-4.07.1/driver/compmisc.ml"; "ocaml-4.07.1/driver/compdynlink.mlno";
  "ocaml-4.07.1/driver/compplugin.ml"; "ocaml-4.07.1/driver/makedepend.ml";
  "ocaml-4.07.1/middle_end/base_types/id_types.ml";
  "ocaml-4.07.1/middle_end/base_types/compilation_unit.ml";
  "ocaml-4.07.1/middle_end/base_types/set_of_closures_id.ml";
  "ocaml-4.07.1/middle_end/base_types/symbol.ml";
  "ocaml-4.07.1/middle_end/base_types/variable.ml";
  "ocaml-4.07.1/middle_end/base_types/closure_element.ml";
  "ocaml-4.07.1/middle_end/base_types/closure_id.ml";
  "ocaml-4.07.1/middle_end/base_types/var_within_closure.ml";
  "ocaml-4.07.1/middle_end/base_types/linkage_name.ml";
  "ocaml-4.07.1/middle_end/flambda_utils.ml";
  "ocaml-4.07.1/middle_end/simple_value_approx.ml";
  "ocaml-4.07.1/middle_end/debuginfo.ml"; "ocaml-4.07.1/asmcomp/cmx_format.mli";
  "ocaml-4.07.1/asmcomp/clambda.ml"; "ocaml-4.07.1/asmcomp/export_info.ml";
  "ocaml-4.07.1/asmcomp/compilenv.ml"; "ocaml-4.07.1/asmcomp/import_approx.ml";
  "ocaml-4.07.1/asmcomp/debug/reg_with_debug_info.ml";
  "ocaml-4.07.1/asmcomp/debug/reg_availability_set.ml";
  "ocaml-4.07.1/asmcomp/debug/available_regs.ml";
  "ocaml-4.07.1/asmcomp/x86_ast.mli"; "ocaml-4.07.1/asmcomp/x86_proc.ml";
  "ocaml-4.07.1/asmcomp/x86_dsl.ml"; "ocaml-4.07.1/asmcomp/x86_gas.ml";
  "ocaml-4.07.1/asmcomp/arch.ml"; "ocaml-4.07.1/asmcomp/cmm.ml";
  "ocaml-4.07.1/asmcomp/reg.ml"; "ocaml-4.07.1/asmcomp/mach.ml";
  "ocaml-4.07.1/asmcomp/proc.ml"; "ocaml-4.07.1/asmcomp/selectgen.ml";
  "ocaml-4.07.1/asmcomp/spacetime_profiling.ml";
  "ocaml-4.07.1/asmcomp/selection.ml"; "ocaml-4.07.1/asmcomp/closure.ml";
  "ocaml-4.07.1/asmcomp/strmatch.ml"; "ocaml-4.07.1/asmcomp/cmmgen.ml";
  "ocaml-4.07.1/asmcomp/linearize.ml";
  "ocaml-4.07.1/asmcomp/branch_relaxation.ml";
  "ocaml-4.07.1/asmcomp/emitaux.ml"; "ocaml-4.07.1/asmcomp/emit.ml";
  "ocaml-4.07.1/asmcomp/comballoc.ml"; "ocaml-4.07.1/asmcomp/CSEgen.ml";
  "ocaml-4.07.1/asmcomp/CSE.ml"; "ocaml-4.07.1/asmcomp/liveness.ml";
  "ocaml-4.07.1/asmcomp/deadcode.ml"; "ocaml-4.07.1/asmcomp/split.ml";
  "ocaml-4.07.1/asmcomp/spill.ml"; "ocaml-4.07.1/asmcomp/interf.ml";
  "ocaml-4.07.1/asmcomp/coloring.ml"; "ocaml-4.07.1/asmcomp/reloadgen.ml";
  "ocaml-4.07.1/asmcomp/reload.ml"; "ocaml-4.07.1/asmcomp/schedgen.ml";
  "ocaml-4.07.1/asmcomp/scheduling.ml"; "ocaml-4.07.1/asmcomp/asmgen.ml";
  "ocaml-4.07.1/asmcomp/asmlink.ml"; "ocaml-4.07.1/driver/opterrors.ml";
  "ocaml-4.07.1/driver/optcompile.ml"; "ocaml-4.07.1/driver/optmain.ml"]

let corpus_path path = Filename.concat (Filename.dirname __FILE__) (Filename.concat "corpus" path)

let names_seen_in_corpus () =
  let simple_idents_seen = ref [] in
  corpus_files
  |>@ corpus_path
  |> List.iter begin fun path ->
    try
      (* print_endline path; *)
      let parsed = Camlboot_interpreter.Interp.parse path in
      let simple_names_in_file = parsed |> Exp.all |>@& Exp.simple_name in
      simple_idents_seen := simple_names_in_file @ !simple_idents_seen
    with _ ->
      ()
  end;
  !simple_idents_seen

let ints_seen_in_corpus () =
  let ints_seen = ref [] in
  corpus_files
  |>@ corpus_path
  |> List.iter begin fun path ->
    try
      (* print_endline path; *)
      let parsed = Camlboot_interpreter.Interp.parse path in
      let ints_in_file = parsed |> Exp.all |>@& Exp.int in
      ints_seen := ints_in_file @ !ints_seen
    with _ ->
      ()
  end;
  !ints_seen

(* let used_pervasives_names () =
  SSet.inter Name.pervasives_names (names_seen_in_corpus ()) *)

(* let unused_pervasives_names () =
  SSet.diff Name.pervasives_names (names_seen_in_corpus ()) *)

(* let ununsed_pervasives_names = SSet.of_list ["&"; "??"; "^^"; "__FILE__"; "__LINE_OF__"; "__LINE__"; "__LOC_OF__"; "__MODULE__"; "__POS_OF__"; "__POS__"; "acos"; "asin"; "atan"; "atan2"; "bool_of_string"; "ceil"; "char_of_int"; "close_in_noerr"; "close_out_noerr"; "copysign"; "cos"; "cosh"; "do_at_exit"; "epsilon_float"; "expm1"; "false"; "float_of_string_opt"; "flush_all"; "format_of_string"; "frexp"; "hypot"; "infinity"; "input_byte"; "input_char"; "int_of_string_opt"; "ldexp"; "log10"; "log1p"; "max_float"; "min_float"; "mod_float"; "modf"; "nan"; "open_in_gen"; "open_out_gen"; "or"; "out_channel_length"; "output_byte"; "output_bytes"; "output_substring"; "prerr_bytes"; "prerr_char"; "prerr_float"; "prerr_int"; "print_float"; "print_int"; "raise_notrace"; "read_float"; "read_float_opt"; "read_int"; "read_int_opt"; "read_line"; "seek_out"; "set_binary_mode_in"; "set_binary_mode_out"; "sin"; "sinh"; "sqrt"; "stdin"; "string_of_format"; "tan"; "tanh"; "truncate"; "unsafe_really_input"; "valid_float_lexem"; "~+"; "~+."] *)

let rec counts_on_sorted = function
  | []         -> []
  | item::rest ->
    let (items, rest') = List.take_while ((=) item) rest in
    [(item, 1 + List.length items)] @ counts_on_sorted rest'

let counts stuff =
  counts_on_sorted (List.sort compare stuff)
  |> List.sort_by (fun (item, count) -> (-count, item))

let print_counts counts =
  counts
  |> List.iter (fun (item, count) -> print_endline @@ string_of_int count ^ "\t" ^ item)

let make_stats () =
  begin
    names_seen_in_corpus ()
    |>@? (fun name -> SSet.mem name Maniposynth_lib.Name.pervasives_names)
    |> counts
    |> print_counts
  end;
  begin
    ints_seen_in_corpus ()
    |>@ string_of_int
    |> counts
    |> print_counts
  end