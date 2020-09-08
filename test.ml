open Maniposynth_lib
(* open Maniposynth_lib.Utils *)

let main () =
  let path = "simple.ml" in
  let parsed_with_comments = Parse_unparse.parse_file path in
  let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
  let callables = Read_execution_env.callables_of_file path in
  let html_str = View.html_str callables bindings_skels in
  Utils.save_file "simple.html" html_str;
  (* List.iter (print_string % Skeleton.show) skeletons; *)
  print_string @@ Parse_unparse.unparse path parsed_with_comments
  ;;

main ();;
