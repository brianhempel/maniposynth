open Ocamlformat_lib

type parsed = Parsetree.toplevel_phrase list Parse_with_comments.with_comments

let conf = Conf.ocamlformat_profile

let conf_opts : Conf.opts =
  { debug                = false
  ; margin_check         = false
  ; format_invalid_files = false }

let translation_ops : Parsetree.toplevel_phrase list Translation_unit.t =
  Translation_unit.impl

let parse_string source =
  Parse_with_comments.parse
    Migrate_ast.Parse.use_file
    conf
    ~source
  
let parse_file input_name =
  let source = Utils.string_of_file input_name in
  parse_string source

(* On error, returns the unchanged contents of the original file. *)
let unparse input_name parsed =
  let source = Utils.string_of_file input_name in
  match Translation_unit.format translation_ops ~input_name ~source ~parsed conf conf_opts with
  | Ok formatted_str ->
    formatted_str
  | Error err ->
    Translation_unit.print_error ~debug:conf_opts.debug ~quiet:false ~input_name err;
    source
