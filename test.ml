open Maniposynth_lib
open Maniposynth_lib.Utils

let main () =
  let path = "simple.ml" in
  let parsed_with_comments = Parse_unparse.parse_file path in
  let skeletons = Skeleton.skeletons_of_parsed_with_comments parsed_with_comments in
  let html_str = Html_of_skeletons.html_str_of_skeletons skeletons in
  Utils.save_file "simple.html" html_str;
  List.iter (print_string % Skeleton.show) skeletons;
  print_string @@ Parse_unparse.unparse path parsed_with_comments
  ;;

main ();;
