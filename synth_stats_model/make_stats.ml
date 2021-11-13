(* open Maniposynth_lib *)
open Shared.Ast
open Shared.Util
open Camlboot_interpreter_for_stats.Data

let make_counts to_string things =
  things
  |> List.fold_left begin fun counts thing ->
    let key = to_string thing in
    let count = SMap.find_opt key counts ||& 0 in
    SMap.add key (count + 1)  counts
  end SMap.empty

let counts_str counts =
  "let counts =\n  [ " ^ begin
    SMap.bindings counts
    |> List.sort_by snd
    |> List.rev
    |> List.map begin fun (key, count) ->
      Exp.tuple [Exp.string_lit key; Exp.int_lit count] |> Exp.to_string
    end
    |> String.concat "\n  ; "
  end ^ "\n  ]"

let general_counts_str stats =
  "let counts =
  { local_ident_count    = " ^ string_of_int stats.local_ident_count ^ "
  ; external_ident_count = " ^ string_of_int stats.external_ident_count ^ "
  ; tup2_count           = " ^ string_of_int stats.tup2_count ^ "
  ; tup3_count           = " ^ string_of_int stats.tup3_count ^ "
  ; tup4_count           = " ^ string_of_int stats.tup4_count ^ "
  ; tup5_count           = " ^ string_of_int stats.tup5_count ^ "
  ; const_str_count      = " ^ string_of_int stats.const_str_count ^ "
  ; const_int_count      = " ^ string_of_int stats.const_int_count ^ "
  ; const_char_count     = " ^ string_of_int stats.const_char_count ^ "
  ; const_float_count    = " ^ string_of_int stats.const_float_count ^ "
  ; let_count            = " ^ string_of_int stats.let_count ^ "
  ; fun_count            = " ^ string_of_int stats.fun_count ^ "
  ; app_count            = " ^ string_of_int stats.app_count ^ "
  ; match_count          = " ^ string_of_int stats.match_count ^ "
  ; ite_count            = " ^ string_of_int stats.ite_count ^ "
  ; stdlib_ctor_count    = " ^ string_of_int stats.stdlib_ctor_count ^ "
  ; nonstdlib_ctor_count = " ^ string_of_int stats.nonstdlib_ctor_count ^ " (* include polymorphic variants *)
  ; record_count         = " ^ string_of_int stats.record_count ^ "
  ; field_count          = " ^ string_of_int stats.field_count ^ "
  }"

let use_to_string = function
  | FirstUse (n, _name) -> "First " ^ string_of_int n
  | Reuse (n, _name)    -> "Reuse " ^ string_of_int n
  | External lid        -> Exp.to_string (Exp.ident (Loc.mk lid))

let use2_to_string = function
  | NthInEnv (n, _name) -> "NthInEnv " ^ string_of_int n
  | External2 lid       -> Exp.to_string (Exp.ident (Loc.mk lid))

let dump key_to_string stuff_to_count title_str =
  let path = "output/" ^ title_str ^ ".ml" in
  print_endline @@ "Writing output/" ^ path;
  write_file (counts_str (make_counts key_to_string stuff_to_count)) path

let main =
  let stats = Camlboot_interpreter_for_stats.Interp.get_stats () in
  (* write_file (stats.constants |>@ Exp.to_string |> List.sort compare |> String.concat "\n") "constants.txt"; *)
  print_endline "Copy paste into stats_model.ml";
  dump use_to_string       stats.local_idents  "local_idents";
  dump use2_to_string      stats.local_idents2 "local_idents2";
  dump Longident.to_string stats.stdlib_idents "stdlib_idents";
  dump Exp.to_string       stats.const_strs    "const_strs";
  dump Exp.to_string       stats.const_ints    "const_ints";
  dump Exp.to_string       stats.const_chars   "const_chars";
  dump Exp.to_string       stats.const_floats  "const_floats";
  dump Longident.to_string stats.stdlib_ctors  "stdlib_ctors";
  print_endline "Writing output/general_counts.ml";
  write_file (general_counts_str stats) "output/general_counts.ml";
