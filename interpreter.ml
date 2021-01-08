
let main () =
  let ocaml_file_path subpath = Filename.concat "ocaml-4.07.1" subpath in
  Camlboot_interpreter.Interp.run_files
    [ ocaml_file_path @@ Filename.concat "utils" "config.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "misc.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "identifiable.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "numbers.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "arg_helper.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "clflags.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "terminfo.ml"
    ; ocaml_file_path @@ Filename.concat "utils" "warnings.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "asttypes.mli"
    ; ocaml_file_path @@ Filename.concat "parsing" "location.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "longident.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "parsetree.mli"
    ; ocaml_file_path @@ Filename.concat "parsing" "docstrings.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "ast_helper.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "parser.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "lexer.ml"
    ; ocaml_file_path @@ Filename.concat "parsing" "parse.ml"
    ; Filename.concat "camlboot_interpreter" "data.ml"
    ; Filename.concat "camlboot_interpreter" "conf.ml"
    ; Filename.concat "camlboot_interpreter" "envir.ml"
    ; Filename.concat "camlboot_interpreter" "eval.ml"
    ; Filename.concat "camlboot_interpreter" "runtime_lib.ml"
    ; Filename.concat "camlboot_interpreter" "runtime_base.ml"
    ; Filename.concat "camlboot_interpreter" "runtime_stdlib.ml"
    ; Filename.concat "camlboot_interpreter" "runtime_compiler.ml"
    ; Filename.concat "camlboot_interpreter" "primitives.ml"
    ; Filename.concat "camlboot_interpreter" "interp.ml"
    ; "interpret_simple_ml.ml"
    ; "simple.ml"
    ]
;;

main ()