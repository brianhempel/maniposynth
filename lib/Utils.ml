
(* Jeffrey Scofield https://stackoverflow.com/a/53840784 *)
let string_of_file path =
  let in_chan = open_in path in
  let str = really_input_string in_chan (in_channel_length in_chan) in
  close_in in_chan;
  str

let save_file path str =
  let out_chan = open_out path in
  output_string out_chan str;
  close_out out_chan
  
let (%)  f g = fun x -> f (g x)
let (%>) f g = fun x -> g (f x)
