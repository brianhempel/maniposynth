open Maniposynth_lib

let port = 1111

let respond ?(content_type = "text/html") ?(status_str = "200 OK") out_chan content_str =
  if status_str != "200 OK" then print_endline status_str;
  output_string out_chan ("HTTP/1.1 " ^ status_str ^ "\r\n");
  output_string out_chan "Connection: close\r\n";
  output_string out_chan ("Content-Type: " ^ content_type ^ "\r\n");
  output_string out_chan ("Content-Length: " ^ string_of_int (String.length content_str) ^ "\r\n");
  output_string out_chan "\r\n";
  output_string out_chan content_str

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
  |> List.find_opt
      (fun (extn, _) -> StringUtils.ends_with path extn) 
  |> Option.map snd

let serve_asset out_chan url =
  try
    let content_str = Utils.string_of_file ("./" ^ url) in
    match content_type_opt_of_path url with
    | Some content_type -> respond ~content_type out_chan content_str
    | None -> respond ~content_type:"application/yolo" out_chan content_str
  with Sys_error _ -> respond_not_found out_chan

let render_maniposynth out_chan url =
  let path = "./" ^ url in
  let parsed_with_comments = Parse_unparse.parse_file path in
  let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
  let callables = Read_execution_env.callables_of_file path in
  let html_str = View.html_str callables bindings_skels in
  (* Utils.save_file (path ^ ".html") html_str; *)
  (* List.iter (print_string % Skeleton.show) skeletons; *)
  (* print_string @@ Parse_unparse.unparse path parsed_with_comments; *)
  respond out_chan html_str

let handle_connection in_chan out_chan =
  let rec read_header_lines chan : (string * string) list =
    let line = input_line chan in
    if String.length (String.trim line) = 0 then
      []
    else
      match StringUtils.split ~limit:2 line ": " with
      | [key; value] ->
          (* print_endline (key ^ "\t" ^ value); *)
          (key, String.trim value) :: read_header_lines chan
      | _ ->
          print_endline ("Bad header line: " ^ line);
          read_header_lines chan
  in
  let request_str = input_line in_chan in
  let headers = read_header_lines in_chan in
  let content_length = int_of_string (ListUtils.assoc_with_default "Content-Length" "0" headers) in
  let content_str = really_input_string in_chan content_length in
  (* print_endline request_str; "GET /path HTTP/1.1" *)
  (match String.split_on_char ' ' request_str with
  | "GET"::url::_ ->
      if StringUtils.starts_with url "/assets/" then
        serve_asset out_chan url
      else if StringUtils.ends_with url ".ml" then
        render_maniposynth out_chan url
      else
        respond_not_found out_chan
  | "PATCH"::url::_ ->
      if StringUtils.ends_with url ".ml" then
        let action_yojson = Yojson.Safe.from_string content_str in
        (* print_endline content_str; *)
        let action = Action.t_of_yojson action_yojson in
        let file_path = "./" ^ url in
        Action.f file_path action;
        respond ~content_type:"text/plain" out_chan "Done."
      else
        respond_not_found out_chan
  | _ ->
      print_string "UNHANDLED REQUEST: ";
      print_endline request_str;
      respond_not_found out_chan
  );
  flush out_chan;
  close_in in_chan (* This apparently closes both channels. *)

let main () =
  let open Unix in
  let sockaddr = ADDR_INET (inet_addr_any, port) in
  print_endline ("Listening for connections on http://localhost:" ^ string_of_int port ^ "/");
  establish_server handle_connection sockaddr
;;

main ();
