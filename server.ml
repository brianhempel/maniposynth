open Maniposynth_lib
open Shared.Util

let port = 1111

let respond ?(content_type = "text/html") ?(status_str = "200 OK") out_chan content_str =
  if not @@ String.equal status_str "200 OK" then print_endline status_str;
  output_string out_chan ("HTTP/1.1 " ^ status_str ^ "\r\n");
  output_string out_chan "Connection: close\r\n";
  output_string out_chan ("Content-Type: " ^ content_type ^ "\r\n");
  output_string out_chan ("Content-Length: " ^ string_of_int (String.length content_str) ^ "\r\n");
  output_string out_chan "\r\n";
  output_string out_chan content_str

let respond_bad_request out_chan =
  respond ~status_str:"400 Bad Request" out_chan "<html><head><title>Bad request.</title></head><body>Bad request.</body></html>"

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
  |> List.find_opt (fun (extn, _) -> String.ends_with extn path)
  |>& snd

(* https://stackoverflow.com/a/53840784 *)
let string_of_file path =
  let in_chan = open_in path in
  let str = really_input_string in_chan (in_channel_length in_chan) in
  close_in in_chan;
  str


let serve_asset out_chan url =
  try
    let content_str = string_of_file ("./" ^ url) in
    match content_type_opt_of_path url with
    | Some content_type -> respond ~content_type out_chan content_str
    | None -> respond ~content_type:"application/yolo" out_chan content_str
  with Sys_error _ -> respond_not_found out_chan

let render_maniposynth out_chan url =
  let path = String.drop 1 url in
  let parsed = Camlboot_interpreter.Interp.parse path in
  (* let parsed_with_comments = Parse_unparse.parse_file path in
  let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
  let callables = Read_execution_env.callables_of_file path in
  let trace = Tracing.run_with_tracing path in
  let html_str = View.html_str callables trace bindings_skels in *)
  let (typed_struct, _, final_tenv) = Typing.typedtree_sig_env_of_file path in
  let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
  let (trace, assert_results) =
    let open Camlboot_interpreter in
    Eval.reset_value_id_counter ();
    Eval.with_gather_asserts begin fun () ->
      Interp.run_files ~fuel_per_top_level_binding:1000 type_lookups.lookup_exp [path]
    end
  in
  (* print_endline @@ string_of_int (List.length assert_results); *)
  let html_str = View.html_str parsed trace assert_results type_lookups final_tenv in
  (* Utils.save_file (path ^ ".html") html_str; *)
  (* List.iter (print_string % Skeleton.show) skeletons; *)
  (* print_string @@ Parse_unparse.unparse path parsed_with_comments; *)
  respond out_chan html_str

(* /simple.ml/search?frame_no=123&valid_ids_visible=&q=asdf *)
let render_suggestions out_chan uri =
  let url_path = uri |> Uri.path |> Uri.pct_decode in
  let file_path = url_path |> String.drop 1 |> String.drop_suffix "/search" in
  let query_params = uri |> Uri.query in

  match List.assoc_opt "frame_no" query_params, List.assoc_opt "value_ids_visible" query_params, List.assoc_opt "q" query_params with
  | Some [frame_no_str], Some [value_ids_visible_comma_separated], Some [q_str] ->
    let value_ids_visible = value_ids_visible_comma_separated |> String.split_on_char ',' |>@ int_of_string |> List.dedup in
    let parsed = Camlboot_interpreter.Interp.parse file_path in
    (* let parsed_with_comments = Parse_unparse.parse_file file_path in
    let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
    let callables = Read_execution_env.callables_of_file file_path in
    let trace = Tracing.run_with_tracing file_path in
    let html_str = View.html_str callables trace bindings_skels in *)
    let (typed_struct, _, _final_tenv) = Typing.typedtree_sig_env_of_file file_path in
    let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
    let (trace, _assert_results) =
      let open Camlboot_interpreter in
      Eval.reset_value_id_counter ();
      Eval.with_gather_asserts begin fun () ->
        Interp.run_files ~fuel_per_top_level_binding:1000 type_lookups.lookup_exp [file_path]
      end
    in
    let frame_no = int_of_string frame_no_str in
    let suggestions = Suggestions.suggestions trace type_lookups parsed frame_no value_ids_visible q_str in
    (* print_endline @@ string_of_int (List.length assert_results); *)
    (* let html_str = View.html_str parsed trace assert_results type_lookups final_tenv in *)
    (* Utils.save_file (file_path ^ ".html") html_str; *)
    (* List.iter (print_string % Skeleton.show) skeletons; *)
    (* print_string @@ Parse_unparse.unparse file_path parsed_with_comments; *)
    respond out_chan (String.concat "|$SEPARATOR$|" suggestions)
  | _ ->
    respond_bad_request out_chan


let handle_connection in_chan out_chan =
  let rec read_header_lines chan : (string * string) list =
    let line = input_line chan in
    if String.length (String.trim line) = 0 then
      []
    else
      match String.split ~limit:2 ": " line with
      | [key; value] -> (key, String.trim value) :: read_header_lines chan
      | _            -> print_endline ("Bad header line: " ^ line); read_header_lines chan
  in
  let request_str = input_line in_chan in
  let headers = read_header_lines in_chan in
  let content_length = int_of_string (List.assoc_opt "Content-Length" headers ||& "0") in
  (* print_endline request_str; "GET /path HTTP/1.1" *)
  let request_str = String.drop_suffix " HTTP/1.1" (String.trim request_str) in
  (match String.split ~limit:2 " " request_str with
  | "GET"::url::_ ->
      let uri = Uri.of_string url in
      let path = uri |> Uri.path |> Uri.pct_decode in
      (* print_endline (Uri.to_string uri); *)
      if String.starts_with "/assets/" path then
        serve_asset out_chan path
      else if String.ends_with ".ml/search" path then
        render_suggestions out_chan uri
      else if String.ends_with ".ml" path then
        render_maniposynth out_chan url
      else
        respond_not_found out_chan
  | "PATCH"::url::_ ->
      if String.ends_with ".ml" url then begin
        (* print_endline "hi"; *)
        (* let content_str = In_channel.input_all in_chan in *)
        let content_str =
          let buf = Bytes.create content_length in
          really_input in_chan buf 0 content_length;
          Bytes.to_string buf
        in
        (* print_endline "bye"; *)
        print_endline content_str;
        let action_yojson = Yojson.Safe.from_string content_str in
        let action = Action.t_of_yojson action_yojson in
        let path = String.drop 1 url in
        let parsed = Camlboot_interpreter.Interp.parse path in
        let (_, _, final_tenv) = Typing.typedtree_sig_env_of_parsed parsed path in
        let parsed' = Action.f path final_tenv action parsed in
        (* Pprintast.structure Format.std_formatter parsed'; *)
        if parsed <> parsed' then Pretty_code.output_code parsed' path; (* This was overwriting synth results! :o *)
        respond ~content_type:"text/plain" out_chan "Done."
      end else
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
  let sockaddr = ADDR_INET (Unix.inet_addr_any, port) in
  print_endline ("Listening for connections on http://localhost:" ^ string_of_int port ^ "/");
  establish_server handle_connection sockaddr
;;

main ();
