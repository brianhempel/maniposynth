open Maniposynth_lib

let main () =
  let file_path = "simple.ml" in
  let parsed_with_comments = Parse_unparse.parse_file file_path in
  let ast' = Tracing.add_tracepoint_placeholders parsed_with_comments.ast in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let out_str = Parse_unparse.unparse file_path parsed_with_comments' in
  print_string @@ out_str;
  let tp_file_path = file_path ^ ".tp_placeholders" in
  Sys_utils.save_file tp_file_path out_str;
  let mono_file_path = tp_file_path ^ ".mono" in
  Sys_utils.copy_file tp_file_path mono_file_path;
  Monomorphize.f mono_file_path;
;;

main ();;
