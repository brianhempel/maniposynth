
(* Jeffrey Scofield https://stackoverflow.com/a/53840784 *)
let string_of_file path =
  let in_chan = open_in_bin path in
  let str = Misc.string_of_file in_chan in
  close_in in_chan;
  str

let save_file path str =
  let out_chan = open_out path in
  output_string out_chan str;
  close_out out_chan

let copy_file path path' =
  string_of_file path
  |> save_file path'

let is_finished pid =
  match Unix.waitpid [Unix.WNOHANG] pid with
  | (0, _) -> false
  | _      -> true

(* Runs command and returns its std out as a string *)
let command ?(verbose = false) cmd =
  if verbose then
    print_endline cmd;
  let chunk_size = 1000 in
  let chan = Unix.open_process_in cmd in
  let pid = Unix.process_in_pid chan in
  let str = ref "" in
  let bytes_buf = Bytes.create chunk_size in
  let rec read_until_process_exit () =
    let len_read = input chan bytes_buf 0 chunk_size in
    if len_read = 0 && is_finished pid then
      ()
    else if len_read = 0 then
      read_until_process_exit ()
    else begin
      str := !str ^ Bytes.sub_string bytes_buf 0 len_read;
      read_until_process_exit ()
    end
  in
  read_until_process_exit ();
  close_in_noerr chan;
  if verbose then
    print_string !str;
  !str
