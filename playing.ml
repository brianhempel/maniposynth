open Maniposynth_lib

let main () =
  let file_path = "simple.ml" in
  (* let with_tracepoints_path = file_path ^ ".with_tracepoints" in
  Sys_utils.copy_file file_path with_tracepoints_path;
  Tracing.add_tracepoint_placeholders with_tracepoints_path *)
  let mono_file_path = file_path ^ ".mono" in
  Sys_utils.copy_file file_path mono_file_path;
  Monomorphize.f mono_file_path;

;;

main ();;
