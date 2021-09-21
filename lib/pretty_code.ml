open Shared.Util

(* Output formatted code. *)
let output_code parsed path =
  let old_parsed = Camlboot_interpreter.Interp.parse path in
  let old_code = Shared.Formatter_to_stringifier.f Pprintast.structure old_parsed in
  let code = Shared.Formatter_to_stringifier.f Pprintast.structure parsed in
  if code <> old_code then begin
    let old_path = String.replace ".ml" "-old.ml" path in
    ignore @@ Unix.system @@ "cp " ^ path ^ " " ^ old_path; (* Save previous version as path-old.ml for diff. *)
    let out_chan = open_out path in
    output_string out_chan code;
    close_out out_chan;
    ignore @@ Unix.system @@ "ocamlformat --inplace --enable-outside-detected-project '" ^ path ^ "'";
    (* Turn ( ?? ) into (??) *)
    ignore @@ Unix.system @@ "ruby -e \"File.write(ARGV[0], File.read(ARGV[0]).gsub(/\\(\\s*\\?\\?\\s*\\)/m, '(??)'))\" '" ^ path ^ "'";
    (* Ensure diff view open *)
    (* ignore @@ Unix.system @@ "code --diff " ^ old_path ^ " " ^ path; *)
  end
