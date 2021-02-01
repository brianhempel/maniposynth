
let main () =
  let trace = Camlboot_interpreter.Interp.run_files ["simple.ml"] in
  trace
;;

main ()