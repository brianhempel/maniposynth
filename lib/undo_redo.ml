open Shared.Util

(* Two folders. "history" holds undo states as "filename-1234.ml". "future" holds redo states similarly. *)

let history_path path = Filename.concat "history" path
let future_path path  = Filename.concat "future" path
let history_dir       = history_path %> Filename.dirname
let future_dir        = future_path %> Filename.dirname

let modification_time path = (Unix.stat path).st_mtime

type history_or_future = History | Future

let sorted_revision_paths history_or_future path =
  let dirify = match history_or_future with History -> history_dir | Future -> future_dir in
  ensure_dir @@ dirify path;
  let file_basename = Filename.basename path |> String.replace ".ml" "" in
  let names = Sys.readdir (dirify path) in (* Returns names in directory, without the directory prefix. *)
  names
  |> Array.to_list
  |>@? String.starts_with file_basename
  |>@ Filename.concat (dirify path) (* Slap the directory prefix back on. *)
  |> List.sort_by modification_time

let parse_latest_revision path prog =
  match List.last_opt (sorted_revision_paths History path) with
  | Some latest_path -> Camlboot_interpreter.Interp.parse latest_path
  | None             -> prog

let undo path prog =
  let history_paths = sorted_revision_paths History path in
  match List.last_opt history_paths with
  | Some latest_path when List.length history_paths >= 2 -> (* Make sure  *)
    (* Move to redo folder. *)
    let redo_path = Filename.concat (future_dir path) (Filename.basename latest_path) in
    ensure_dir (Filename.dirname redo_path);
    Sys.rename latest_path redo_path;
    parse_latest_revision path prog
  | _ ->
    prog

let redo path prog =
  match List.hd_opt (sorted_revision_paths Future path) with
  | Some oldest_path ->
    (* Move to undo folder. *)
    Sys.rename oldest_path (Filename.concat (history_dir path) (Filename.basename oldest_path));
    parse_latest_revision path prog
  | None ->
    prog

let perhaps_log_revision path =
  let code_on_disk = string_of_file path in
  let undo_code    = List.last_opt (sorted_revision_paths History path) |>& string_of_file ||& "" in
  if code_on_disk <> undo_code then begin
    (* "asdf/jkl.ml" -> "asdf/jkl-92834902734234.ml" *)
    (* Just needs to be a unique name because we use file creation time to sort. *)
    let path_with_blerg = path |> String.replace ".ml" ("-" ^ string_of_float (Unix.gettimeofday ()) ^ ".ml") in
    write_file code_on_disk (history_path path_with_blerg);
    (* Remove redo history by removing "future/asdf/jkl-*.ml" *)
    ignore @@ Unix.system @@ "rm " ^ ( future_path path |> String.replace ".ml" "") ^ "-*.ml"
  end

let perhaps_initialize_undo_history path =
  if sorted_revision_paths History path = [] then
    let code_on_disk = string_of_file path in
    let path_with_blerg = path |> String.replace ".ml" ("-1.ml") in
    write_file code_on_disk (history_path path_with_blerg)

