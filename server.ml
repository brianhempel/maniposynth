open Maniposynth_lib
open Shared.Util

let port = 1111

let respond ?(content_type = "text/html") ?(status_str = "200 OK") out_chan content_str =
  if not @@ List.mem status_str ["200 OK"; "404 Not Found"] then print_endline status_str;
  output_string out_chan ("HTTP/1.1 " ^ status_str ^ "\r\n");
  output_string out_chan "Connection: close\r\n";
  output_string out_chan ("Content-Type: " ^ content_type ^ "\r\n");
  output_string out_chan ("Content-Length: " ^ string_of_int (String.length content_str) ^ "\r\n");
  output_string out_chan "\r\n";
  output_string out_chan content_str

let respond_bad_request out_chan =
  respond ~status_str:"400 Bad Request" out_chan "<html><head><title>Bad request.</title></head><body>Bad request.</body></html>"

let respond_not_found request_str out_chan =
  let status_str = "404 Not Found" in
  if not (String.includes "/assets/still_synthesizing.html" request_str) then print_endline @@ status_str ^ " " ^ request_str;
  respond ~status_str out_chan "<html><head><title>Not found.</title></head><body>Not found.</body></html>"

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

let serve_asset request_str out_chan url =
  try
    let path1 = nativize_path @@ "./" ^ url in (* Relative to location server started *)
    let path2 = Filename.concat executable_dir (nativize_path url) in (* Relative to server executable *)
    let path = if Sys.file_exists path1 then path1 else path2 in
    let content_str = string_of_file path in
    match content_type_opt_of_path url with
    | Some content_type -> respond ~content_type out_chan content_str
    | None -> respond ~content_type:"application/yolo" out_chan content_str
  with Sys_error _ -> respond_not_found request_str out_chan

let render_maniposynth out_chan url =
  let path = String.drop 1 url |> nativize_path in
  let (parsed, trace, assert_results, type_lookups, fatal_errors, type_errors, file_final_env, final_tenv) =
    try
      let parsed = Camlboot_interpreter.Interp.parse path in
      (* let parsed_with_comments = Parse_unparse.parse_file path in
      let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
      let callables = Read_execution_env.callables_of_file path in
      let trace = Tracing.run_with_tracing path in
      let html_str = View.html_str callables trace bindings_skels in *)
      let (type_lookups, final_tenv, type_errors) =
        try
          let (typed_struct, _, final_tenv, type_errors) = Typing.typedtree_sig_env_of_file_with_error_recovery path in
          let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
          (type_lookups, final_tenv, type_errors)
        with Typecore.Error (loc, tenv, err) ->
          (Typing.empty_lookups, Typing.initial_env, [(loc, tenv, err)])
      in
      let ((trace, final_env), assert_results) =
        let open Camlboot_interpreter in
        Eval.with_gather_asserts begin fun () ->
          Interp.run_files ~fuel_per_top_level_binding:1000 type_lookups.lookup_exp [path]
        end
      in
      let file_final_env =
        let open Camlboot_interpreter in
        (* open the module, basically *)
        (Envir.env_get_module_data final_env (Shared.Ast.Longident.lident (Data.module_name_of_unit_path path))).mod_internal_env
      in
      (parsed, trace, assert_results, type_lookups, [], type_errors, file_final_env, final_tenv)
    with error ->
      ([], Camlboot_interpreter.Trace.empty, [], Typing.empty_lookups, [error], [], Camlboot_interpreter.Envir.empty_env, Env.empty)
  in
  (* print_endline (SMap.keys final_env.values |> String.concat " "); *)
  (* print_endline @@ string_of_int (List.length assert_results); *)
  let html_str = View.html_str parsed trace assert_results type_lookups fatal_errors type_errors file_final_env final_tenv in
  (* Utils.save_file (path ^ ".html") html_str; *)
  (* List.iter (print_string % Skeleton.show) skeletons; *)
  (* print_string @@ Parse_unparse.unparse path parsed_with_comments; *)
  respond out_chan html_str

(* /simple.ml/search?frame_no=123&valid_ids_visible=&q=asdf *)
let render_suggestions out_chan uri =
  let url_path = uri |> Uri.path |> Uri.pct_decode in
  let file_path = url_path |> String.drop 1 |> String.drop_suffix "/search" |> nativize_path in
  let query_params = uri |> Uri.query in
  match ["vbs_loc"; "value_ids_visible"; "value_strs"; "q"] |>@ (fun key -> List.assoc_opt key query_params) |> Option.project with
  | Some [[vbs_loc_str]; [value_ids_visible_comma_separated]; [value_strs_comma_separated]; [q_str]] ->
    (* print_endline value_ids_visible_comma_separated; *)
    let value_ids_visible = value_ids_visible_comma_separated |> String.split_on_char ',' |> List.remove "" |>@ int_of_string in
    (* print_endline value_strs_comma_separated; *)
    let value_strs = value_strs_comma_separated |> String.split_on_char ',' |> List.remove "" |>@ String.replace "~CoMmA~" "," in
    let vbs_loc = Serialize.loc_of_string vbs_loc_str in
    let parsed = Camlboot_interpreter.Interp.parse file_path in
    (* let parsed_with_comments = Parse_unparse.parse_file file_path in
    let bindings_skels = Skeleton.bindings_skels_of_parsed_with_comments parsed_with_comments in
    let callables = Read_execution_env.callables_of_file file_path in
    let trace = Tracing.run_with_tracing file_path in
    let html_str = View.html_str callables trace bindings_skels in *)
    let (typed_struct, _, final_tenv, _type_errors) = Typing.typedtree_sig_env_of_file_with_error_recovery file_path in
    let type_lookups = Typing.type_lookups_of_typed_structure typed_struct in
    let selected_value_id = List.assoc_opt "selected_value_id" query_params |>&& List.hd_opt |>& int_of_string in
    let suggestions = Suggestions.suggestions type_lookups final_tenv parsed vbs_loc value_ids_visible value_strs ?selected_value_id q_str in
    (* print_endline @@ string_of_int (List.length assert_results); *)
    (* let html_str = View.html_str parsed trace assert_results type_lookups final_tenv in *)
    (* Utils.save_file (file_path ^ ".html") html_str; *)
    (* List.iter (print_string % Skeleton.show) skeletons; *)
    (* print_string @@ Parse_unparse.unparse file_path parsed_with_comments; *)
    respond out_chan (String.concat "|$SEPARATOR$|" (List.prefix 20 suggestions))
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
        serve_asset request_str out_chan path
      else if String.ends_with ".ml/search" path then
        render_suggestions out_chan uri
      else if String.ends_with ".ml" path then
        render_maniposynth out_chan url
      else
        respond_not_found request_str out_chan
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
        let (_, _, final_tenv, _type_errors) = Typing.typedtree_sig_env_of_parsed_with_error_recovery parsed path in
        let parsed' = Action.f path final_tenv action parsed in
        (* Pprintast.structure Format.std_formatter parsed'; *)
        Undo_redo.perhaps_initialize_undo_history path;
        if parsed <> parsed' then begin
          Pretty_code.output_code parsed' path; (* This was overwriting synth results! :o *)
          Undo_redo.perhaps_log_revision path
        end;
        if Action.should_synth_afterward action then Synth.try_async path;
        respond ~content_type:"text/plain" out_chan "Done."
      end else
        respond_not_found request_str out_chan
  | _ ->
      print_string "UNHANDLED REQUEST: ";
      print_endline request_str;
      respond_not_found request_str out_chan
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
