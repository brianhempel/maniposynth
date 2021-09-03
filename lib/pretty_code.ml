(* Output formatted code. *)
let output_code parsed path =
  let old_parsed = Camlboot_interpreter.Interp.parse path in
  let old_code = Shared.Formatter_to_stringifier.f Pprintast.structure old_parsed in
  let code = Shared.Formatter_to_stringifier.f Pprintast.structure parsed in
  if code <> old_code then begin
    let out_chan = open_out path in
    output_string out_chan code;
    close_out out_chan;
    ignore @@ Unix.system @@ "ocamlformat --inplace --enable-outside-detected-project '" ^ path ^ "'";
    (* Turn ( ?? ) into (??) *)
    ignore @@ Unix.system @@ "ruby -e \"File.write(ARGV[0], File.read(ARGV[0]).gsub(/\\(\\s*\\?\\?\\s*\\)/m, '(??)'))\" '" ^ path ^ "'"
  end
