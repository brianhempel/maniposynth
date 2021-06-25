open Maniposynth_lib
open Core

let port = 1111

let respond ?(content_type = "text/html") ?(status_str = "200 OK") out_chan content_str =
  if not @@ String.equal status_str "200 OK" then print_endline status_str;
  Out_channel.output_string out_chan ("HTTP/1.1 " ^ status_str ^ "\r\n");
  Out_channel.output_string out_chan "Connection: close\r\n";
  Out_channel.output_string out_chan ("Content-Type: " ^ content_type ^ "\r\n");
  Out_channel.output_string out_chan ("Content-Length: " ^ string_of_int (String.length content_str) ^ "\r\n");
  Out_channel.output_string out_chan "\r\n";
  Out_channel.output_string out_chan content_str

let respond_not_found out_chan =
  respond ~status_str:"404 Not Found" out_chan "<html><head><title>Not found.</title></head><body>Not found.</body></html>"

(* More here: https://developer.mozilla.org/en-US/docs/Web/HTTP/Basics_of_HTTP/MIME_types/Common_types *)
let file_extension_content_types =
  [ (".css", "text/css")
  ; (".gif", "image/gif")
  ; (".htm", "text/html")
  ; (".html", "text/html")
  ; (".jpeg", "image/jpeg")
  ; (".jpg", "image/jpeg")
  ; (".js", "text/javascript")
  ; (".png", "image/png")
  ; (".pdf", "application/pdf")
  ; (".svg", "image/svg+xml")
  ; (".txt", "text/plain")
  ; (".zip", "application/zip")
  ]

let content_type_opt_of_path path =
  file_extension_content_types
  |> List.find
      ~f:(fun (extn, _) -> String.is_suffix path ~suffix:extn)
  |> Option.map ~f:snd

let serve_asset out_chan url =
  try
    let content_str = In_channel.read_all ("./" ^ url) in
    match content_type_opt_of_path url with
    | Some content_type -> respond ~content_type out_chan content_str
    | None -> respond ~content_type:"application/yolo" out_chan content_str
  with Sys_error _ -> respond_not_found out_chan

let render_maniposynth out_chan url =
  let path = String.drop_prefix url 1 in
  let parsed = Camlboot_interpreter.Interp.parse path in
  (* let parsed_with_comments = Parse_unparse.parse_file path in
  let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
  let callables = Read_execution_env.callables_of_file path in
  let trace = Tracing.run_with_tracing path in
  let html_str = View.html_str callables trace bindings_skels in *)
  let lookup_exp_typed = Typing.exp_typed_lookup_of_file path in
  let (trace, assert_results) =
    Camlboot_interpreter.Eval.with_gather_asserts begin fun () ->
      Camlboot_interpreter.Interp.run_files lookup_exp_typed [path]
    end in
  (* print_endline @@ string_of_int (List.length assert_results); *)
  let html_str = View.html_str parsed trace assert_results lookup_exp_typed in
  (* Utils.save_file (path ^ ".html") html_str; *)
  (* List.iter (print_string % Skeleton.show) skeletons; *)
  (* print_string @@ Parse_unparse.unparse path parsed_with_comments; *)
  respond out_chan html_str


let colon_space = String.Search_pattern.create ": "

let handle_connection in_chan out_chan =
  let rec read_header_lines chan : (string * string) list =
    let line = In_channel.input_line_exn chan in
    let trim = String.strip ~drop:Char.is_whitespace in
    if String.length (trim line) = 0 then
      []
    else
      match String.Search_pattern.index colon_space ~in_:line with
      | Some i ->
        let key = String.slice line 0 i in
        let value = String.slice line (i+2) (String.length line) in
        (key, trim value) :: read_header_lines chan
      | None ->
        print_endline ("Bad header line: " ^ line);
        read_header_lines chan


        (*
      match String_utils.split ~limit:2 line ": " with
      | [key; value] ->
          (* print_endline (key ^ "\t" ^ value); *)
          (key, String.trim value) :: read_header_lines chan
      | _ ->
          print_endline ("Bad header line: " ^ line);
          read_header_lines chan *)
  in
  let request_str = In_channel.input_line_exn in_chan in
  let headers = read_header_lines in_chan in
  let content_length = int_of_string (List.Assoc.find headers ~equal:String.equal "Content-Length" |> Option.value ~default:"0") in
  (* print_endline request_str; "GET /path HTTP/1.1" *)
  (match String.split ~on:' ' request_str with
  | "GET"::url::_ ->
      if String.is_prefix url ~prefix:"/assets/" then
        serve_asset out_chan url
      else if String.is_suffix url ~suffix:".ml" then
        render_maniposynth out_chan url
      else
        respond_not_found out_chan
  | "PATCH"::url::_ ->
      if String.is_suffix url ~suffix:".ml" then begin
        (* print_endline "hi"; *)
        (* let content_str = In_channel.input_all in_chan in *)
        let content_str =
          let buf = Bytes.create content_length in
          In_channel.really_input_exn in_chan ~buf ~pos:0 ~len:content_length;
          Bytes.to_string buf
        in
        (* print_endline "bye"; *)
        (* print_endline content_str; *)
        let action_yojson = Yojson.Safe.from_string content_str in
        let action = Action.t_of_yojson action_yojson in
        let path = String.drop_prefix url 1 in
        let parsed = Camlboot_interpreter.Interp.parse path in
        let parsed' = Action.f action parsed in
        (* Pprintast.structure Format.std_formatter parsed'; *)
        Out_channel.with_file path ~f:begin fun out ->
          Shared.Formatter_to_stringifier.f Pprintast.structure parsed'
          |> Out_channel.output_string out
        end;
        respond ~content_type:"text/plain" out_chan "Done."
      end else
        respond_not_found out_chan
  | _ ->
      print_string "UNHANDLED REQUEST: ";
      print_endline request_str;
      respond_not_found out_chan
  );
  Out_channel.flush out_chan;
  In_channel.close in_chan (* This apparently closes both channels. *)

let main () =
  let open Unix in
  let sockaddr = ADDR_INET (Unix.Inet_addr.bind_any, port) in
  print_endline ("Listening for connections on http://localhost:" ^ string_of_int port ^ "/");
  establish_server handle_connection ~addr:sockaddr
;;

main ();
