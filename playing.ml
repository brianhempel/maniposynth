open Maniposynth_lib

let main () =
  let file_path = "simple.ml" in
  let parsed_with_comments = Parse_unparse.parse_file file_path in
  let trace_file_path = file_path ^ ".trace" in
  let ast' = Tracing.add_tracepoint_placeholders trace_file_path parsed_with_comments.ast in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let out_str = Parse_unparse.unparse file_path parsed_with_comments' in
  (* print_string @@ out_str; *)
  let tp_file_path = file_path ^ ".tp_placeholders" in
  Sys_utils.save_file tp_file_path out_str;
  let mono_file_path = tp_file_path ^ ".mono" in
  Sys_utils.copy_file tp_file_path mono_file_path;
  Monomorphize.f mono_file_path;
  let parsed_with_comments = Parse_unparse.parse_file mono_file_path in
  let (env, typed_structure) = Type_utils.final_env_and_typed_structure_of_file mono_file_path in
  let ast' = Tracing.fill_tracepoint_placeholders env typed_structure parsed_with_comments.ast in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let out_str = Parse_unparse.unparse file_path parsed_with_comments' in
  print_string @@ out_str;
  Sys_utils.save_file (file_path ^ ".traced.ml") out_str;
  ()
;;

main ();;
