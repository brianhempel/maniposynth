
let main () =
  let trace = Interp.run_files ["simple.ml"] in
  trace
;;

main ()