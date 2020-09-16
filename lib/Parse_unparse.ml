open Ocamlformat_lib

(* Comment-preserving parse/unparse using ocamlformat *)

type parsed = Parsetree.toplevel_phrase list Parse_with_comments.with_comments

let conf = Conf.ocamlformat_profile

let conf_opts : Conf.opts =
  { debug                = false
  ; margin_check         = false
  ; format_invalid_files = false
  }

let translation_ops : Parsetree.toplevel_phrase list Translation_unit.t =
  Translation_unit.impl

let parse_file_string source =
  Parse_with_comments.parse
    Migrate_ast.Parse.use_file
    conf
    ~source

let with_input_name name thunk =
  let old_name = !Location.input_name in
  Location.input_name := name;
  let result = thunk () in
  Location.input_name := old_name;
  result

let parse_file input_name =
  with_input_name input_name @@ fun () ->
    let source = Sys_utils.string_of_file input_name in
    parse_file_string source

(* Wants pre-existing file name. *)
(* On error, returns the unchanged contents of the original file. *)
let unparse input_name parsed =
  let source = Sys_utils.string_of_file input_name in
  match Translation_unit.format translation_ops ~input_name ~source ~parsed conf conf_opts with
  | Ok formatted_str ->
    formatted_str
  | Error err ->
    Translation_unit.print_error ~debug:conf_opts.debug ~quiet:false ~input_name err;
    source
