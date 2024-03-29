open Data
(* open Envir *)
open Runtime_lib
open Runtime_base
open Runtime_stdlib
open Runtime_compiler

let exp_of_desc loc desc =
  Parsetree.{ pexp_desc = desc; pexp_loc = loc; pexp_attributes = [] }

let seq_or loc = function
  | [ (_, arg1); (_, arg2) ] ->
    let open Parsetree in
    let expr_true =
      Pexp_construct ({ txt = Longident.Lident "true"; loc }, None)
    in
    Some
      (exp_of_desc
         loc
         (Pexp_ifthenelse (arg1, exp_of_desc loc expr_true, Some arg2)))
  | _ -> None

let seq_and loc = function
  | [ (_, arg1); (_, arg2) ] ->
    let open Parsetree in
    let expr_false =
      Pexp_construct ({ txt = Longident.Lident "false"; loc }, None)
    in
    Some
      (exp_of_desc
         loc
         (Pexp_ifthenelse (arg1, arg2, Some (exp_of_desc loc expr_false))))
  | _ -> None

let apply loc = function
  | [ (_, f); (_, x) ] ->
    let open Parsetree in
    Some (exp_of_desc loc (Pexp_apply (f, [ (Nolabel, x) ])))
  | _ -> None

let rev_apply loc = function
  | [ (_, x); (_, f) ] ->
    let open Parsetree in
    Some (exp_of_desc loc (Pexp_apply (f, [ (Asttypes.Nolabel, x) ])))
  | _ -> None

external reraise : exn -> 'a = "%reraise"
external raise_notrace : exn -> 'a = "%raise_notrace"

let prims =
  let prim1 name f = prim1 name f Runtime_base.wrap_exn in
  let prim2 name f = prim2 name f Runtime_base.wrap_exn in
  let prim3 name f = prim3 name f Runtime_base.wrap_exn in
  let prim4 name f = prim4 name f Runtime_base.wrap_exn in
  let prim5 name f = prim5 name f Runtime_base.wrap_exn in
  [ ("%apply", new_vtrace @@ Fexpr apply);
    ("%revapply", new_vtrace @@ Fexpr rev_apply);
    ("%raise", new_vtrace @@ Prim ("raise", fun v -> raise (InternalException v)));
    ("%reraise", new_vtrace @@ Prim ("reraise", fun v -> reraise (InternalException v)));
    ("%raise_notrace", new_vtrace @@ Prim ("raise_notrace", fun v -> raise_notrace (InternalException v)));
    ("%sequand", new_vtrace @@ Fexpr seq_and);
    ("%sequor", new_vtrace @@ Fexpr seq_or);
    ("%boolnot", prim1 "not" not unwrap_bool wrap_bool);
    ("%negint", prim1 "~-" ( ~- ) unwrap_int wrap_int);
    ("%succint", prim1 "succ" succ unwrap_int wrap_int);
    ("%predint", prim1 "pred" pred unwrap_int wrap_int);
    ("%addint", prim2 "(+)" ( + ) unwrap_int unwrap_int wrap_int);
    ("%subint", prim2 "(-)" ( - ) unwrap_int unwrap_int wrap_int);
    ("%mulint", prim2 "(*)" ( * ) unwrap_int unwrap_int wrap_int);
    ("%divint", prim2 "(/)" ( / ) unwrap_int unwrap_int wrap_int);
    ("%modint", prim2 "(mod)" ( mod ) unwrap_int unwrap_int wrap_int);
    ("%andint", prim2 "()" ( land ) unwrap_int unwrap_int wrap_int);
    ("%orint", prim2 "(lor)" ( lor ) unwrap_int unwrap_int wrap_int);
    ("%xorint", prim2 "(lxor)" ( lxor ) unwrap_int unwrap_int wrap_int);
    ("%lslint", prim2 "(lsl)" ( lsl ) unwrap_int unwrap_int wrap_int);
    ("%lsrint", prim2 "(lsr)" ( lsr ) unwrap_int unwrap_int wrap_int);
    ("%asrint", prim2 "(asr)" ( asr ) unwrap_int unwrap_int wrap_int);
    ("%addfloat", prim2 "(+.)" ( +. ) unwrap_float unwrap_float wrap_float);
    ("%subfloat", prim2 "(-.)" ( -. ) unwrap_float unwrap_float wrap_float);
    ("%mulfloat", prim2 "(*.)" ( *. ) unwrap_float unwrap_float wrap_float);
    ("%divfloat", prim2 "(/.)" ( /. ) unwrap_float unwrap_float wrap_float);
    ("%floatofint", prim1 "floatofint" float_of_int unwrap_int wrap_float);
    ("%intoffloat", prim1 "intoffloat" int_of_float unwrap_float wrap_int);
    ("%lessthan", prim2 "(<)" value_lt id id wrap_bool);
    ("%lessequal", prim2 "(<=)" value_le id id wrap_bool);
    ("%greaterthan", prim2 "(>)" value_gt id id wrap_bool);
    ("%greaterequal", prim2 "(>=)" value_ge id id wrap_bool);
    ("%compare", prim2 "compare" value_compare id id wrap_int);
    ("%equal", prim2 "(=)" value_equal id id wrap_bool);
    ("%notequal", prim2 "(<>)" value_equal id id (fun x -> wrap_bool (not x)));
    ("%eq", prim2 "(==)" ( == ) id id wrap_bool);
    ("%noteq", prim2 "(!=)" ( != ) id id wrap_bool);
    ("%identity", new_vtrace @@ Prim ("identity", fun x -> x));
    ("caml_register_named_value",
      new_vtrace @@ Prim ("caml_register_named_value", fun _ -> new_vtrace @@ Prim ("const_unit", fun _ -> unit)));
    ( "caml_int64_float_of_bits",
      prim1 "caml_int64_float_of_bits" Int64.float_of_bits unwrap_int64 wrap_float );
    ( "caml_ml_open_descriptor_out",
      prim1 "caml_ml_open_descriptor_out" open_descriptor_out unwrap_int wrap_out_channel );
    ( "caml_ml_open_descriptor_in",
      prim1 "caml_ml_open_descriptor_in" open_descriptor_in unwrap_int wrap_in_channel );
    ( "caml_sys_open",
      prim3
        "caml_sys_open"
        open_desc
        unwrap_string
        (unwrap_list unwrap_open_flag)
        unwrap_int
        wrap_int );
    ( "caml_sys_close",
      prim1
        "caml_sys_close"
        close_desc
        unwrap_int
        wrap_unit );
    ( "caml_sys_system_command",
      prim1 "caml_sys_system_command" caml_sys_system_command unwrap_string wrap_int  );
    ( "caml_ml_set_channel_name",
      prim2
        "caml_ml_set_channel_name"
        (fun { v_; _ } s ->
          match v_ with
          | InChannel ic -> set_in_channel_name ic s
          | OutChannel oc -> set_out_channel_name oc s
          | _ -> assert false)
        id
        unwrap_string
        wrap_unit );
    ( "caml_ml_close_channel",
      prim1
        "caml_ml_close_channel"
        (fun { v_; _ } -> match v_ with
          | InChannel ic -> close_in ic
          | OutChannel oc -> close_out oc
          | _ -> assert false)
        id
        wrap_unit );
    ( "caml_ml_out_channels_list",
      prim1 "caml_ml_out_channels_list" out_channels_list unwrap_unit (wrap_list wrap_out_channel) );
    ( "caml_ml_output_bytes",
      prim4
        "caml_ml_output_bytes"
        unsafe_output
        unwrap_out_channel
        unwrap_bytes
        unwrap_int
        unwrap_int
        wrap_unit );
    ( "caml_ml_output",
      prim4
        "caml_ml_output_bytes"
        unsafe_output_string
        unwrap_out_channel
        unwrap_string
        unwrap_int
        unwrap_int
        wrap_unit );
    ( "caml_ml_output_int",
      prim2 "caml_ml_output_int" output_binary_int unwrap_out_channel unwrap_int wrap_unit );
    ( "caml_ml_output_char",
      prim2 "caml_ml_output_char" output_char unwrap_out_channel unwrap_char wrap_unit );
    ("caml_ml_flush", prim1 "caml_ml_flush" flush unwrap_out_channel wrap_unit);
    ("caml_ml_input_char", prim1 "caml_ml_input_char" input_char unwrap_in_channel wrap_char);
    ("caml_ml_input_int", prim1 "caml_ml_input_int" input_binary_int unwrap_in_channel wrap_int);
    ("caml_ml_input_scan_line",
      prim1 "caml_ml_input_scan_line" input_scan_line unwrap_in_channel wrap_int );
    ("caml_ml_input",
      prim4
        "caml_ml_input"
        unsafe_input
        unwrap_in_channel
        unwrap_bytes
        unwrap_int
        unwrap_int
        wrap_int );
    ("caml_ml_seek_in", prim2 "caml_ml_seek_in" seek_in unwrap_in_channel unwrap_int wrap_unit);
    ("caml_ml_pos_out", prim1 "caml_ml_pos_out" pos_out unwrap_out_channel wrap_int);
    ("caml_ml_pos_in", prim1 "caml_ml_pos_in" pos_in unwrap_in_channel wrap_int);
    ("caml_ml_seek_out", prim2 "caml_ml_seek_out" seek_out unwrap_out_channel unwrap_int wrap_unit);
    ("%makemutable",
      new_vtrace @@ Prim ("makemutable", fun v -> new_vtrace @@ Record (SMap.singleton "contents" (ref v))));
    ( "%field0",
      new_vtrace @@ Prim
        ( "field0"
        , fun { v_; _ } -> match v_ with
        | Record r -> !(SMap.find "contents" r)
        | Tuple l -> List.hd l
        | _ -> assert false) );
    ( "%field1",
      new_vtrace @@ Prim
        ( "field1"
        , fun { v_; _ } -> match v_ with
        | Tuple l -> List.hd (List.tl l)
        | _ -> assert false) );
    ( "%setfield0",
      new_vtrace @@ Prim
        ( "setfield0"
        , fun { v_; _ } -> match v_ with
        | Record r ->
          new_vtrace @@ Prim
            ("setfield0", fun v ->
              SMap.find "contents" r := v;
              unit)
        | _ -> assert false) );
    ( "%incr",
      new_vtrace @@ Prim
        ( "incr"
        , fun { v_; _ } -> match v_ with
        | Record r ->
          let z = SMap.find "contents" r in
          z := wrap_int (unwrap_int !z + 1);
          unit
        | _ -> assert false) );
    ( "%decr",
      new_vtrace @@ Prim
        ( "decr"
        , fun { v_; _ } -> match v_ with
        | Record r ->
          let z = SMap.find "contents" r in
          z := wrap_int (unwrap_int !z - 1);
          unit
        | _ -> assert false) );
    ("%ignore", new_vtrace @@ Prim ("ignore", fun _ -> unit));
    ("caml_format_int", prim2 "caml_format_int" format_int unwrap_string unwrap_int wrap_string);
    ("caml_format_float",
      prim2 "caml_format_float" format_float unwrap_string unwrap_float wrap_string );
    ("caml_int32_format",
     prim2 "caml_int32_format" caml_int32_format unwrap_string unwrap_int32 wrap_string);
    ("caml_int64_format",
     prim2 "caml_int64_format" caml_int64_format unwrap_string unwrap_int64 wrap_string);
    ("caml_nativeint_format",
     prim2 "caml_nativeint_format" caml_nativeint_format unwrap_string unwrap_nativeint wrap_string);
    ("caml_int_of_string", prim1 "caml_int_of_string" int_of_string unwrap_string wrap_int);
    ("caml_float_of_string", prim1 "caml_float_of_string" float_of_string unwrap_string wrap_float);
    ( "caml_output_value",
      prim3
        "caml_output_value"
        marshal_to_channel
        unwrap_out_channel
        id
        (unwrap_list unwrap_unit)
        wrap_unit );
    ( "caml_output_value_to_buffer",
      prim5
        "caml_output_value_to_buffer"
        Marshal.to_buffer
        unwrap_bytes
        unwrap_int
        unwrap_int
        id
        (unwrap_list unwrap_marshal_flag)
        wrap_int );
    ( "caml_output_value_to_string",
      prim2
        "caml_output_value_to_string"
        caml_output_value_to_string
        id
        (unwrap_list unwrap_marshal_flag)
        wrap_string );
    ("caml_input_value", prim1 "caml_input_value" input_value unwrap_in_channel id);
    ("caml_sys_exit", prim1 "caml_sys_exit" exit unwrap_int wrap_unit);
    ("caml_parse_engine", parse_engine_prim);
    ("caml_lex_engine", lex_engine_prim);
    ("caml_new_lex_engine", new_lex_engine_prim);
    (* Sys *)
    ( "caml_sys_get_argv",
      new_vtrace @@ Prim
        ("caml_sys_get_argv", fun _ ->
          new_vtrace @@ Tuple [ wrap_string "";
                  new_vtrace @@ Array (Array.map wrap_string Sys.argv) ]) );
    ( "caml_sys_get_config",
      new_vtrace @@ Prim
      ("caml_sys_get_config", fun _ -> new_vtrace @@ Tuple [ wrap_string "Unix"; wrap_int 0; wrap_bool true ]) );
    ("%big_endian", new_vtrace @@ Prim ("big_endian", fun _ -> wrap_bool Sys.big_endian));
    ("%word_size", new_vtrace @@ Prim ("word_size", fun _ -> new_vtrace @@ Int 64));
    ("%int_size", new_vtrace @@ Prim ("int_size", fun _ -> new_vtrace @@ Int 64));
    ("%max_wosize", new_vtrace @@ Prim ("max_wosize", fun _ -> new_vtrace @@ Int 1000000));
    ("%ostype_unix", new_vtrace @@ Prim ("ostype_unix", fun _ -> wrap_bool false));
    ("%ostype_win32", new_vtrace @@ Prim ("ostype_win32", fun _ -> wrap_bool false));
    ("%ostype_cygwin", new_vtrace @@ Prim ("ostype_cygwin", fun _ -> wrap_bool false));
    ( "%backend_type",
      new_vtrace @@ Prim ("backend_type",  fun _ ->
          new_vtrace @@ Constructor ("Other", 0, Some (wrap_string "Interpreter")))
    );
    ("caml_sys_getenv", prim1 "caml_sys_getenv" Sys.getenv unwrap_string wrap_string);
    ("caml_sys_file_exists", prim1 "caml_sys_file_exists" Sys.file_exists unwrap_string wrap_bool);
    ("caml_sys_getcwd", prim1 "caml_sys_getcwd" Sys.getcwd unwrap_unit wrap_string);
    ("caml_sys_rename", prim2 "caml_sys_rename" Sys.rename unwrap_string unwrap_string wrap_unit);
    ("caml_sys_remove", prim1 "caml_sys_remove" Sys.remove unwrap_string wrap_unit);
    (* Bytes *)
    ("caml_create_bytes", prim1 "caml_create_bytes" Bytes.create unwrap_int wrap_bytes);
    ( "caml_fill_bytes",
      prim4
        "caml_fill_bytes"
        Bytes.unsafe_fill
        unwrap_bytes
        unwrap_int
        unwrap_int
        unwrap_char
        wrap_unit );
    ("%bytes_to_string", new_vtrace @@ Prim ("bytes_to_string", fun v -> v));
    ("%bytes_of_string", new_vtrace @@ Prim ("bytes_of_string", fun v -> v));
    ("%string_length", prim1 "string_length" Bytes.length unwrap_bytes wrap_int);
    ("%bytes_length", prim1 "bytes_length" Bytes.length unwrap_bytes wrap_int);
    ("%string_safe_get", prim2 "string_safe_get" Bytes.get unwrap_bytes unwrap_int wrap_char);
    ( "%string_unsafe_get",
      prim2 "string_unsafe_get" Bytes.unsafe_get unwrap_bytes unwrap_int wrap_char );
    ("%bytes_safe_get", prim2 "bytes_safe_get" Bytes.get unwrap_bytes unwrap_int wrap_char);
    ( "%bytes_unsafe_get",
      prim2 "bytes_unsafe_get" Bytes.unsafe_get unwrap_bytes unwrap_int wrap_char );
    ( "%bytes_safe_set",
      prim3 "bytes_safe_set" Bytes.set unwrap_bytes unwrap_int unwrap_char wrap_unit );
    ( "%bytes_unsafe_set",
      prim3 "bytes_unsafe_set" Bytes.unsafe_set unwrap_bytes unwrap_int unwrap_char wrap_unit );
    ( "caml_blit_string",
      prim5
        "caml_blit_string"
        String.blit
        unwrap_string
        unwrap_int
        unwrap_bytes
        unwrap_int
        unwrap_int
        wrap_unit );
    ( "caml_blit_bytes",
      prim5
        "caml_blit_bytes"
        Bytes.blit
        unwrap_bytes
        unwrap_int
        unwrap_bytes
        unwrap_int
        unwrap_int
        wrap_unit );
    (* Lazy *)
    ( "%lazy_force",
    new_vtrace @@ Prim
        ("lazy_force", fun { v_; _ } -> match v_ with
        | Lz f ->
          let v = !f () in
          (f := fun () -> v);
          v
        | _ -> assert false) );
    (* Int64 *)
    ("%int64_neg", prim1 "int64_neg" Int64.neg unwrap_int64 wrap_int64);
    ("%int64_add", prim2 "int64_add" Int64.add unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_sub", prim2 "int64_sub" Int64.sub unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_mul", prim2 "int64_mul" Int64.mul unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_div", prim2 "int64_div" Int64.div unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_mod", prim2 "int64_mod" Int64.rem unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_and", prim2 "int64_and" Int64.logand unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_or", prim2 "int64_or" Int64.logor unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_xor", prim2 "int64_xor" Int64.logxor unwrap_int64 unwrap_int64 wrap_int64);
    ("%int64_lsl", prim2 "int64_lsl" Int64.shift_left unwrap_int64 unwrap_int wrap_int64);
    ( "%int64_lsr",
      prim2 "int64_lsr" Int64.shift_right_logical unwrap_int64 unwrap_int wrap_int64 );
    ("%int64_asr", prim2 "int64_asr" Int64.shift_right unwrap_int64 unwrap_int wrap_int64);
    ("%int64_of_int", prim1 "int64_of_int" Int64.of_int unwrap_int wrap_int64);
    ("%int64_to_int", prim1 "int64_to_int" Int64.to_int unwrap_int64 wrap_int);
    ("%int64_to_int32", prim1 "int64_to_int32" Int64.to_int32 unwrap_int64 wrap_int32);
    ("%int64_of_int32", prim1 "int64_of_int32" Int64.of_int32 unwrap_int32 wrap_int64);
    ("%int64_of_nativeint", prim1 "int64_of_nativeint" Int64.of_nativeint unwrap_nativeint wrap_int64);
    ("%int64_to_nativeint", prim1 "int64_to_nativeint" Int64.to_nativeint unwrap_int64 wrap_nativeint);
    ("caml_int64_of_string", prim1 "caml_int64_of_string" Int64.of_string unwrap_string wrap_int64);
    (* Int32 *)
    ("caml_int32_of_string", prim1 "caml_int32_of_string" int_of_string unwrap_string wrap_int);
    ("%int32_neg", prim1 "(~-)" ( ~- ) unwrap_int wrap_int);
    (* Nativeint *)
    ("%nativeint_neg", prim1 "nativeint_neg" Nativeint.neg unwrap_nativeint wrap_nativeint);
    ("%nativeint_add", prim2 "nativeint_add" Nativeint.add unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_sub", prim2 "nativeint_sub" Nativeint.sub unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_mul", prim2 "nativeint_mul" Nativeint.mul unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_div", prim2 "nativeint_div" Nativeint.div unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_mod", prim2 "nativeint_mod" Nativeint.rem unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_and", prim2 "nativeint_and" Nativeint.logand unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_or", prim2 "nativeint_or" Nativeint.logor unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ("%nativeint_xor", prim2 "nativeint_xor" Nativeint.logxor unwrap_nativeint unwrap_nativeint wrap_nativeint);
    ( "%nativeint_lsl",
      prim2 "nativeint_lsl" Nativeint.shift_left unwrap_nativeint unwrap_int wrap_nativeint );
    ( "%nativeint_lsr",
      prim2 "nativeint_lsr" Nativeint.shift_right_logical unwrap_nativeint unwrap_int wrap_nativeint );
    ( "%nativeint_asr",
      prim2 "nativeint_asr" Nativeint.shift_right unwrap_nativeint unwrap_int wrap_nativeint );
    ("%nativeint_of_int", prim1 "nativeint_of_int" Nativeint.of_int unwrap_int wrap_nativeint);
    ("%nativeint_to_int", prim1 "nativeint_to_int" Nativeint.to_int unwrap_nativeint wrap_int);
    ("caml_nativeint_of_string", prim1 "caml_nativeint_of_string" Nativeint.of_string unwrap_string wrap_nativeint);
    (* Array *)
    ("caml_make_vect", prim2 "caml_make_vect"Array.make unwrap_int id wrap_array_id);
    ("%array_length", prim1 "array_length" Array.length unwrap_array_id wrap_int);
    ( "caml_array_sub",
      prim3 "caml_array_sub" Array.sub unwrap_array_id unwrap_int unwrap_int wrap_array_id );
    ( "caml_array_concat",
      prim1 "caml_array_concat" Array.concat (unwrap_list unwrap_array_id) wrap_array_id );
    ("%array_safe_get", prim2 "array_safe_get"Array.get unwrap_array_id unwrap_int id);
    ("%array_unsafe_get", prim2 "array_unsafe_get"Array.unsafe_get unwrap_array_id unwrap_int id);
    ("%array_safe_set", prim3 "array_safe_set" Array.set unwrap_array_id unwrap_int id wrap_unit);
    ( "%array_unsafe_set",
      prim3 "array_unsafe_set" Array.unsafe_set unwrap_array_id unwrap_int id wrap_unit );
    ( "caml_array_blit",
      prim5
        "caml_array_blit"
        Array.blit
        unwrap_array_id
        unwrap_int
        unwrap_array_id
        unwrap_int
        unwrap_int
        wrap_unit );
    ( "caml_array_append",
      prim2 "caml_array_append" append_prim unwrap_array_id unwrap_array_id wrap_array_id );
    (* Hashtbl *)
    ( "caml_hash",
      prim4 "caml_hash" seeded_hash_param unwrap_int unwrap_int unwrap_int id wrap_int );
    (* TODO: records defined in different order... *)

    (* Weak *)
    ( "caml_weak_create",
      prim1
        "caml_weak_create"
        (fun n -> Array.make n (new_vtrace @@ Constructor ("None", 0, None)))
        unwrap_int
        wrap_array_id );
    ("caml_weak_get", prim2 "caml_weak_get" (fun a n -> a.(n)) unwrap_array_id unwrap_int id);
    ( "caml_weak_get_copy",
      prim2 "caml_weak_get_copy" (fun a n -> a.(n)) unwrap_array_id unwrap_int id );
    ( "caml_weak_set",
      prim3 "caml_weak_set" (fun a n v -> a.(n) <- v) unwrap_array_id unwrap_int id wrap_unit
    );
    ( "caml_weak_check",
      prim2
        "caml_weak_check"
        (fun a n -> a.(n).v_ <> Constructor ("None", 0, None))
        unwrap_array_id
        unwrap_int
        wrap_bool );
    ( "caml_weak_blit",
      prim5
        "caml_weak_blit"
        Array.blit
        unwrap_array_id
        unwrap_int
        unwrap_array_id
        unwrap_int
        unwrap_int
        wrap_unit );
    (* Random *)
    ( "caml_sys_random_seed",
      prim1 "caml_sys_random_seed"random_seed unwrap_unit (wrap_array wrap_int) );
    (* Spacetime *)
    ( "caml_spacetime_enabled",
      let module Prim = struct
        external spacetime_enabled : unit -> bool = "caml_spacetime_enabled"
          [@@noalloc]
      end
      in
      prim1 "caml_spacetime_enabled" Prim.spacetime_enabled unwrap_unit wrap_bool );
    (* Gc *)
    ("caml_gc_quick_stat", prim1 "caml_gc_quick_stat" Gc.quick_stat unwrap_unit wrap_gc_stat);
    (* utils/profile.ml *)
    ( "caml_sys_time_include_children",
      let module Prim = struct
        external time_include_children
          :  bool ->
          float
          = "caml_sys_time_include_children"
      end
      in
      prim1 "caml_sys_time_include_children" Prim.time_include_children unwrap_bool wrap_float );
    (* utils/misc.ml *)
    ( "caml_sys_isatty",
      let module Prim = struct
        external isatty : out_channel -> bool = "caml_sys_isatty"
      end
      in
      prim1 "caml_sys_isatty" Prim.isatty unwrap_out_channel wrap_bool );
    (* Digest *)
    ( "caml_md5_string",
      prim3
        "caml_md5_string"
        digest_unsafe_string
        unwrap_string
        unwrap_int
        unwrap_int
        wrap_string );
    ( "caml_md5_chan",
      prim2 "caml_md5_chan" Digest.channel unwrap_in_channel unwrap_int wrap_string );
    (* Ugly *)
    ( "%obj_size",
      prim1
        "obj_size"
        (fun { v_; _ } -> match v_ with
          | Array a -> Array.length a + 2
          | _ -> 4)
        id
        wrap_int );
    ( "caml_obj_block",
      prim2
        "caml_obj_block"
        (fun tag size ->
          let block = new_vtrace @@ Array (Array.init size (fun _ -> new_vtrace @@ Int 0)) in
          new_vtrace @@ Constructor ("", tag, Some block))
        unwrap_int
        unwrap_int
        id );
    ( "%obj_set_field",
      prim3 "obj_set_field" (fun data idx v ->
          let err () =
            Format.eprintf "obj_set_field (%a).(%d) <- (%a)@."
              pp_print_value data
              idx
              pp_print_value v in
          match data.v_ with
            | Array arr -> arr.(idx) <- v
            | Constructor(_, _, Some { v_ = arg_; _ }) ->
               begin match arg_ with
                 | Array arr -> arr.(idx) <- v
                 | _ -> err (); assert false
               end
            | _ -> err (); assert false
        )
        id
        unwrap_int
        id
        wrap_unit );
  ]

let prims =
  List.fold_left (fun env (name, v) -> SMap.add name v env) SMap.empty prims

let () = Runtime_compiler.apply_ref := Eval.apply Shared.Loc_map.empty prims (fun _ -> None) (Trace.new_trace_state ())
