open Ocamlformat_lib

(* Jeffrey Scofield https://stackoverflow.com/a/53840784 *)
let read_file_to_string path =
  let in_chan = open_in path in
  let str = really_input_string in_chan (in_channel_length in_chan) in
  close_in in_chan;
  str;;

let main () =
  let conf = Conf.ocamlformat_profile in
  let conf_opts : Conf.opts =
    { debug                = false
    ; margin_check         = false
    ; format_invalid_files = false }
  in
  let translation_ops : Parsetree.toplevel_phrase list Translation_unit.t = Translation_unit.impl in
  let input_name = "parse_test.ml" in
  let source = read_file_to_string input_name in
  let parsed =
    Parse_with_comments.parse
      Migrate_ast.Parse.use_file
      conf
      ~source
  in
  match Translation_unit.format translation_ops ~input_name ~source ~parsed conf conf_opts with
  | Ok formatted_str ->
    print_string formatted_str
  | Error err ->
    Translation_unit.print_error ~debug:conf_opts.debug ~quiet:false ~input_name err
  ;;

main ();;
