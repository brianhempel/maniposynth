let counts =
  [ ("!", 1470)
  ; ("Parsing.peek_val", 1282)
  ; ("+", 1180)
  ; ("=", 852)
  ; ("Obj.repr", 848)
  ; (":=", 832)
  ; ("ref", 742)
  ; ("List.map", 591)
  ; (">=", 587)
  ; ("-", 549)
  ; ("invalid_arg", 536)
  ; ("Array.get", 499)
  ; ("raise", 492)
  ; (">", 453)
  ; ("&&", 414)
  ; ("||", 383)
  ; ("^", 377)
  ; ("not", 351)
  ; ("<", 346)
  ; ("List.iter", 322)
  ; ("<>", 264)
  ; ("Format.fprintf", 212)
  ; ("Array.length", 206)
  ; ("@", 185)
  ; ("String.length", 166)
  ; ("List.length", 165)
  ; ("Array.set", 150)
  ; ("List.fold_left", 138)
  ; ("List.rev", 125)
  ; ("Seq.fold_left", 119)
  ; ("Printf.sprintf", 119)
  ; ("*", 116)
  ; ("fst", 110)
  ; ("String.get", 97)
  ; ("incr", 92)
  ; ("Format.asprintf", 91)
  ; ("<=", 82)
  ; ("Array.make", 74)
  ; ("lsl", 73)
  ; ("List.fold_right", 73)
  ; ("==", 67)
  ; ("List.sort_uniq", 64)
  ; ("snd", 63)
  ; ("Printf.fprintf", 62)
  ; ("String.sub", 59)
  ; ("land", 58)
  ; ("ignore", 57)
  ; ("Hashtbl.create", 54)
  ; ("Hashtbl.find", 52)
  ; ("@@", 51)
  ; ("string_of_int", 46)
  ; ("List.exists", 46)
  ; ("output_string", 44)
  ; ("compare", 44)
  ; ("List.mem", 41)
  ; ("Bytes.unsafe_set", 41)
  ; ("Char.code", 40)
  ; ("Hashtbl.add", 39)
  ; ("List.filter", 38)
  ; ("*.", 38)
  ; ("~-", 37)
  ; ("Array.map", 36)
  ; ("Format.eprintf", 35)
  ; ("Array.of_list", 34)
  ; ("|>", 33)
  ; ("Buffer.add_char", 33)
  ; ("/", 32)
  ; ("List.for_all", 30)
  ; ("close_in", 29)
  ; ("String.concat", 29)
  ; ("Char.unsafe_chr", 29)
  ; ("max_int", 27)
  ; ("Obj.magic", 27)
  ; ("Buffer.add_string", 27)
  ; ("+.", 27)
  ; ("exit", 26)
  ; ("Hashtbl.clear", 26)
  ; ("failwith", 25)
  ; ("Buffer.create", 25)
  ; ("lor", 24)
  ; ("Filename.check_suffix", 23)
  ; ("mod", 22)
  ; ("List.iter2", 22)
  ; ("List.assoc", 22)
  ; ("Bytes.create", 22)
  ; ("Buffer.contents", 22)
  ; ("Array.unsafe_get", 22)
  ; ("Pervasives.compare", 21)
  ; ("Lazy.force", 21)
  ; ("lsr", 20)
  ; ("/.", 20)
  ; ("min", 19)
  ; ("max", 19)
  ; ("output_char", 17)
  ; ("Bytes.length", 17)
  ; ("int_of_char", 16)
  ; ("Sys.max_string_length", 16)
  ; ("List.sort", 16)
  ; ("float_of_int", 15)
  ; ("Nativeint.of_int", 15)
  ; ("Hashtbl.mem", 15)
  ; ("Format.pp_print_text", 15)
  ; ("Format.err_formatter", 15)
  ; ("Filename.quote", 15)
  ; ("Array.sub", 15)
  ; ("stdout", 14)
  ; ("close_out", 14)
  ; ("Sys.getenv", 14)
  ; ("Obj.obj", 14)
  ; ("List.map2", 14)
  ; ("Hashtbl.iter", 14)
  ; ("-.", 14)
  ; ("stderr", 13)
  ; ("prerr_endline", 13)
  ; ("open_in_bin", 13)
  ; ("input_value", 13)
  ; ("Bytes.unsafe_to_string", 13)
  ; ("really_input_string", 12)
  ; ("print_string", 12)
  ; ("flush", 12)
  ; ("asr", 12)
  ; ("Sys.word_size", 12)
  ; ("Sys.argv", 12)
  ; ("String.make", 12)
  ; ("List.rev_map", 12)
  ; ("Hashtbl.hash", 12)
  ; ("Filename.basename", 12)
  ; ("Bytes.get", 12)
  ; ("output_value", 11)
  ; ("List.memq", 11)
  ; ("List.find", 11)
  ; ("lxor", 10)
  ; ("float_of_string", 10)
  ; ("abs", 10)
  ; ("Sys.os_type", 10)
  ; ("Sys.file_exists", 10)
  ; ("String.index", 10)
  ; ("String.compare", 10)
  ; ("Printf.eprintf", 10)
  ; ("Nativeint.shift_left", 10)
  ; ("Char.chr", 10)
  ; ("Bytes.set", 10)
  ; ("Array.iter", 10)
  ; ("int_of_string", 9)
  ; ("String.blit", 9)
  ; ("Obj.tag", 9)
  ; ("Obj.field", 9)
  ; ("List.split", 9)
  ; ("Filename.temp_file", 9)
  ; ("Array.to_list", 9)
  ; ("sqrt", 8)
  ; ("prerr_string", 8)
  ; ("min_int", 8)
  ; ("Printf.printf", 8)
  ; ("Parsing.symbol_start_pos", 8)
  ; ("Obj.set_field", 8)
  ; ("List.tl", 8)
  ; ("List.rev_append", 8)
  ; ("List.nth", 8)
  ; ("Format.pp_print_string", 8)
  ; ("Format.pp_print_char", 8)
  ; ("Filename.remove_extension", 8)
  ; ("Bytes.sub_string", 8)
  ; ("Array.init", 8)
  ; ("decr", 7)
  ; ("abs_float", 7)
  ; ("Printexc.to_string", 7)
  ; ("Parsing.yyparse", 7)
  ; ("Parsing.symbol_end_pos", 7)
  ; ("Parsing.rhs_start_pos", 7)
  ; ("Parsing.rhs_end_pos", 7)
  ; ("Obj.object_tag", 7)
  ; ("Obj.lazy_tag", 7)
  ; ("Obj.forward_tag", 7)
  ; ("List.hd", 7)
  ; ("List.combine", 7)
  ; ("Format.str_formatter", 7)
  ; ("Filename.chop_extension", 7)
  ; ("Bytes.make", 7)
  ; ("!=", 7)
  ; ("float", 6)
  ; ("String.split_on_char", 6)
  ; ("String.capitalize_ascii", 6)
  ; ("Seq.iter", 6)
  ; ("Printf.bprintf", 6)
  ; ("Printexc.raw_backtrace_to_string", 6)
  ; ("Printexc.get_callstack", 6)
  ; ("Nativeint.to_string", 6)
  ; ("Nativeint.logor", 6)
  ; ("List.flatten", 6)
  ; ("Lexing.lexeme_char", 6)
  ; ("Hashtbl.replace", 6)
  ; ("Hashtbl.remove", 6)
  ; ("Hashtbl.fold", 6)
  ; ("Bytes.blit", 6)
  ; ("Array.iteri", 6)
  ; ("Array.fold_left", 6)
  ; ("Array.blit", 6)
  ; ("~-.", 5)
  ; ("succ", 5)
  ; ("pred", 5)
  ; ("open_out_bin", 5)
  ; ("input_line", 5)
  ; ("char_of_int", 5)
  ; ("Queue.create", 5)
  ; ("Obj.size", 5)
  ; ("Obj.new_block", 5)
  ; ("Nativeint.add", 5)
  ; ("List.fold_left2", 5)
  ; ("Int64.of_nativeint", 5)
  ; ("Int64.of_int", 5)
  ; ("Int64.compare", 5)
  ; ("Int64.bits_of_float", 5)
  ; ("Hashtbl.reset", 5)
  ; ("Format.pp_print_list", 5)
  ; ("Format.pp_print_int", 5)
  ; ("Filename.concat", 5)
  ; ("Filename.chop_suffix", 5)
  ; ("seek_in", 4)
  ; ("print_newline", 4)
  ; ("open_in", 4)
  ; ("lnot", 4)
  ; ("int_of_float", 4)
  ; ("String.lowercase_ascii", 4)
  ; ("Queue.add", 4)
  ; ("Obj.double_tag", 4)
  ; ("Obj.custom_tag", 4)
  ; ("Lexing.lexeme", 4)
  ; ("Int64.to_int32", 4)
  ; ("Int64.of_int32", 4)
  ; ("Format.printf", 4)
  ; ("Format.pp_print_cut", 4)
  ; ("Format.flush_str_formatter", 4)
  ; ("Filename.is_implicit", 4)
  ; ("Char.uppercase_ascii", 4)
  ; ("Buffer.clear", 4)
  ; ("Array.copy", 4)
  ; ("string_of_float", 3)
  ; ("print_char", 3)
  ; ("open_out", 3)
  ; ("input", 3)
  ; ("in_channel_length", 3)
  ; ("__LOC__", 3)
  ; ("Weak.set", 3)
  ; ("Uchar.to_int", 3)
  ; ("Sys.ocaml_version", 3)
  ; ("String.unsafe_get", 3)
  ; ("String.uncapitalize_ascii", 3)
  ; ("String.map", 3)
  ; ("String.escaped", 3)
  ; ("Pervasives.close_in", 3)
  ; ("Obj.string_tag", 3)
  ; ("Obj.infix_tag", 3)
  ; ("Obj.double_array_tag", 3)
  ; ("Obj.closure_tag", 3)
  ; ("Nativeint.to_int32", 3)
  ; ("List.partition", 3)
  ; ("List.mem_assoc", 3)
  ; ("List.for_all2", 3)
  ; ("List.concat", 3)
  ; ("List.assq", 3)
  ; ("Int64.shift_left", 3)
  ; ("Int64.one", 3)
  ; ("Int64.neg", 3)
  ; ("Int32.of_int", 3)
  ; ("Filename.open_temp_file", 3)
  ; ("Filename.dirname", 3)
  ; ("Filename.current_dir_name", 3)
  ; ("Digest.file", 3)
  ; ("Buffer.reset", 3)
  ; ("Array.mapi", 3)
  ; ("Array.append", 3)
  ; ("Arg.current", 3)
  ; ("**", 3)
  ; ("sin", 2)
  ; ("pos_out", 2)
  ; ("output_substring", 2)
  ; ("output_binary_int", 2)
  ; ("input_binary_int", 2)
  ; ("format_of_string", 2)
  ; ("cos", 2)
  ; ("classify_float", 2)
  ; ("atan2", 2)
  ; ("at_exit", 2)
  ; ("Weak.get", 2)
  ; ("Sys.remove", 2)
  ; ("Sys.getcwd", 2)
  ; ("Sys.executable_name", 2)
  ; ("Sys.command", 2)
  ; ("String.unsafe_blit", 2)
  ; ("String.iter", 2)
  ; ("String.equal", 2)
  ; ("String.contains", 2)
  ; ("Seq.map", 2)
  ; ("Random.make_self_init", 2)
  ; ("Random.bits", 2)
  ; ("Queue.push", 2)
  ; ("Pervasives.stdin", 2)
  ; ("Pervasives.float", 2)
  ; ("Parsing.is_current_lookahead", 2)
  ; ("Obj.set_tag", 2)
  ; ("Obj.is_block", 2)
  ; ("Nativeint.to_int", 2)
  ; ("Nativeint.size", 2)
  ; ("Nativeint.shift_right_logical", 2)
  ; ("Nativeint.of_int32", 2)
  ; ("Nativeint.neg", 2)
  ; ("Nativeint.logxor", 2)
  ; ("Lexing.from_channel", 2)
  ; ("Int64.to_string", 2)
  ; ("Int64.to_nativeint", 2)
  ; ("Int64.to_int", 2)
  ; ("Int64.sub", 2)
  ; ("Int64.shift_right_logical", 2)
  ; ("Int64.shift_right", 2)
  ; ("Int64.logand", 2)
  ; ("Int32.to_string", 2)
  ; ("Int32.neg", 2)
  ; ("Format.std_formatter", 2)
  ; ("Format.pp_open_box", 2)
  ; ("Format.pp_close_box", 2)
  ; ("Format.formatter_of_buffer", 2)
  ; ("Char.uppercase", 2)
  ; ("Char.lowercase_ascii", 2)
  ; ("Char.lowercase", 2)
  ; ("Char.escaped", 2)
  ; ("Bytes.to_string", 2)
  ; ("Bytes.empty", 2)
  ; ("Bytes.blit_string", 2)
  ; ("Buffer.output_buffer", 2)
  ; ("Buffer.length", 2)
  ; ("Array.fold_right", 2)
  ; ("Array.concat", 2)
  ; ("Arg.read_arg0", 2)
  ; ("Arg.read_arg", 2)
  ; ("string_of_bool", 1)
  ; ("really_input", 1)
  ; ("print_endline", 1)
  ; ("print_bytes", 1)
  ; ("prerr_newline", 1)
  ; ("output", 1)
  ; ("map", 1)
  ; ("log", 1)
  ; ("iter", 1)
  ; ("input_char", 1)
  ; ("floor", 1)
  ; ("exp", 1)
  ; ("bool_of_string_opt", 1)
  ; ("bool_of_string", 1)
  ; ("Weak.create", 1)
  ; ("Uchar.unsafe_of_int", 1)
  ; ("Uchar.is_valid", 1)
  ; ("Sys.rename", 1)
  ; ("Sys.readdir", 1)
  ; ("Sys.max_array_length", 1)
  ; ("Sys.int_size", 1)
  ; ("Sys.getenv_opt", 1)
  ; ("Sys.backend_type", 1)
  ; ("String.uppercase_ascii", 1)
  ; ("String.init", 1)
  ; ("String.index_from", 1)
  ; ("Stream.from", 1)
  ; ("Scanf.from_channel", 1)
  ; ("Scanf.bscanf", 1)
  ; ("Queue.pop", 1)
  ; ("Queue.is_empty", 1)
  ; ("Printf.kprintf", 1)
  ; ("Pervasives.string_of_float", 1)
  ; ("Pervasives.stdout", 1)
  ; ("Pervasives.stderr", 1)
  ; ("Pervasives.open_in_bin", 1)
  ; ("Pervasives.open_in", 1)
  ; ("Pervasives.neg_infinity", 1)
  ; ("Pervasives.nan", 1)
  ; ("Pervasives.min_float", 1)
  ; ("Pervasives.max_float", 1)
  ; ("Pervasives.infinity", 1)
  ; ("Pervasives.float_of_string_opt", 1)
  ; ("Pervasives.epsilon_float", 1)
  ; ("Pervasives.do_at_exit", 1)
  ; ("Parsing.clear_parser", 1)
  ; ("Obj.is_int", 1)
  ; ("Obj.dup", 1)
  ; ("Obj.abstract_tag", 1)
  ; ("Nativeint.succ", 1)
  ; ("Nativeint.sub", 1)
  ; ("Nativeint.shift_right", 1)
  ; ("Nativeint.rem", 1)
  ; ("Nativeint.of_string", 1)
  ; ("Nativeint.mul", 1)
  ; ("Nativeint.logand", 1)
  ; ("Nativeint.equal", 1)
  ; ("Nativeint.div", 1)
  ; ("Nativeint.compare", 1)
  ; ("Marshal.total_size", 1)
  ; ("Marshal.to_string", 1)
  ; ("Marshal.to_bytes", 1)
  ; ("Marshal.to_buffer", 1)
  ; ("Marshal.from_bytes", 1)
  ; ("List.to_seq", 1)
  ; ("List.stable_sort", 1)
  ; ("List.iteri", 1)
  ; ("List.init", 1)
  ; ("List.fold_right2", 1)
  ; ("List.fast_sort", 1)
  ; ("Lexing.lexeme_start", 1)
  ; ("Lexing.lexeme_end", 1)
  ; ("Int64.succ", 1)
  ; ("Int64.rem", 1)
  ; ("Int64.of_string", 1)
  ; ("Int64.mul", 1)
  ; ("Int64.logxor", 1)
  ; ("Int64.logor", 1)
  ; ("Int64.float_of_bits", 1)
  ; ("Int64.equal", 1)
  ; ("Int64.div", 1)
  ; ("Int64.add", 1)
  ; ("Int32.to_int", 1)
  ; ("Int32.succ", 1)
  ; ("Int32.sub", 1)
  ; ("Int32.shift_right_logical", 1)
  ; ("Int32.shift_right", 1)
  ; ("Int32.shift_left", 1)
  ; ("Int32.rem", 1)
  ; ("Int32.of_string", 1)
  ; ("Int32.mul", 1)
  ; ("Int32.logxor", 1)
  ; ("Int32.logor", 1)
  ; ("Int32.logand", 1)
  ; ("Int32.equal", 1)
  ; ("Int32.div", 1)
  ; ("Int32.compare", 1)
  ; ("Int32.bits_of_float", 1)
  ; ("Int32.add", 1)
  ; ("Hashtbl.length", 1)
  ; ("Hashtbl.find_opt", 1)
  ; ("Hashtbl.find_all", 1)
  ; ("Gc.quick_stat", 1)
  ; ("Gc.minor", 1)
  ; ("Format.sprintf", 1)
  ; ("Format.set_mark_tags", 1)
  ; ("Format.pp_print_space", 1)
  ; ("Format.pp_print_newline", 1)
  ; ("Format.pp_print_flush", 1)
  ; ("Format.pp_print_float", 1)
  ; ("Format.pp_print_as", 1)
  ; ("Format.kasprintf", 1)
  ; ("Format.formatter_of_out_channel", 1)
  ; ("Digest.string", 1)
  ; ("Digest.output", 1)
  ; ("Digest.input", 1)
  ; ("Bytes.unsafe_of_string", 1)
  ; ("Bytes.unsafe_get", 1)
  ; ("Bytes.unsafe_blit", 1)
  ; ("Bytes.sub", 1)
  ; ("Bytes.of_string", 1)
  ; ("Buffer.sub", 1)
  ; ("Buffer.add_utf_8_uchar", 1)
  ; ("Buffer.add_substring", 1)
  ; ("Array.unsafe_set", 1)
  ; ("Array.map2", 1)
  ; ("Array.make_matrix", 1)
  ; ("Array.for_all", 1)
  ; ("Array.fill", 1)
  ; ("Arg.usage", 1)
  ; ("Arg.parse_and_expand_argv_dynamic", 1)
  ]