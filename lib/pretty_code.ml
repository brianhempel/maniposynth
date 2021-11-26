open Shared.Util

let hole_lit_regexp = Str.regexp "([ \t\n]*\\?\\?[ \t\n]*)"

(* "( ?? )" -> "(??)" *)
let tighten_holes code =  Str.global_replace hole_lit_regexp "(??)" code

(* Output formatted code. *)
let output_code parsed path =
  let old_parsed = Camlboot_interpreter.Interp.parse path in
  let old_code = Shared.Formatter_to_stringifier.f Pprintast.structure old_parsed in
  let code = Shared.Formatter_to_stringifier.f Pprintast.structure parsed in
  if code <> old_code then begin
    let old_path = String.replace ".ml" "-old.ml" path in
    (* Use a temp file for formatting. Otherwise we get 2 undo steps in VS Code. *)
    let temp_path = String.replace ".ml" "-tmp.ml" path in
    ignore @@ Unix.system @@ "cp " ^ path ^ " " ^ old_path; (* Save previous version as path-old.ml for diff. *)
    write_file code temp_path;
    (* Shared.Util.time "ocamlformat" (fun () -> ignore @@ Unix.system @@ "ocamlformat --inplace --enable-outside-detected-project '" ^ temp_path ^ "'"); *)
    ignore @@ Unix.system @@ "ocamlformat --inplace --enable-outside-detected-project '" ^ temp_path ^ "'";
    (* Turn ( ?? ) into (??) *)
    let formatted = string_of_file temp_path |> tighten_holes in
    ignore @@ Unix.system @@ "rm " ^ temp_path;
    write_file formatted path
    (* Ensure diff view open *)
    (* ignore @@ Unix.system @@ "code --diff " ^ old_path ^ " " ^ path; *)
  end
