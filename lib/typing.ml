open Shared.Ast
open Shared.Util


module LocMap = struct
  include Map.Make(Loc)

  let all_at_loc loc   map = find_opt loc map ||& []
  let add_to_loc loc v map = add loc (v :: all_at_loc loc map) map
end

let formatter = Format.std_formatter

let inital_env =
  (* Need to add (??) to the Stdlib typing environment *)
  let fake_filename = "type_prelude.ml" in
  let buf = Lexing.from_string
    "let (??) = failwith \"should never hit this; this is just so the type checker doesn't croak on (??)\""
  in
  Compmisc.init_path false; (* This line makes Compmisc.initial_env magically work. *)
  Env.set_unit_name @@ Compenv.module_of_filename formatter fake_filename fake_filename;
  let (_, _, env_with_hole) =
    Typemod.type_structure
      (Compmisc.initial_env ()) (* Stdlib *)
      (Location.init buf fake_filename; Parse.implementation buf)
      (Location.in_file fake_filename)
  in
  env_with_hole


(* Returns (typedtree_structure, signature, env) *)
let typedtree_sig_env_of_file path =
  let parsed = Camlboot_interpreter.Interp.parse path in
  let (typed_struct, signature, env) =
    Env.set_unit_name @@ Compenv.module_of_filename formatter path path;
    (* print_endline @@ Compenv.module_of_filename formatter path path; *)
    try Typemod.type_structure inital_env parsed (Location.in_file path)
    with Typetexp.Error (_loc, env, err) ->
      Typetexp.report_error env formatter err;
      print_endline "";
      failwith "typedtree conversion failed"
  in
  (* Printtyped.implementation formatter typedtree;
  Printtyp.signature formatter signature;
  Format.pp_print_newline formatter (); *)
  (typed_struct, signature, env)


let exp_typed_lookup_of_file path =
  let (typed_struct, _, _) = typedtree_sig_env_of_file path in
  let locmap = ref LocMap.empty in
  let module Iter = TypedtreeIter.MakeIterator(struct
    include TypedtreeIter.DefaultIteratorArgument
    let enter_expression exp =
      locmap := LocMap.add_to_loc exp.Typedtree.exp_loc exp !locmap
  end) in
  Iter.iter_structure typed_struct;
  let locmap = !locmap in
  begin fun exp ->
    match LocMap.all_at_loc exp.Parsetree.pexp_loc locmap with
    | []       -> None
    | [tt_exp] -> Some tt_exp
    | _        -> print_endline @@ "multiple typedtree nodes at loc " ^ Loc.to_string exp.pexp_loc; None
  end
