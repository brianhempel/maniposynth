open Parsetree
open Shared.Ast
open Shared.Util

let gen_ctor_cases ~avoid_names type_path tenv : case list =
  let ctor_descs, _ = Env.find_type_descrs type_path tenv in
  let new_names = ref [] in
  ctor_descs
  |>@ (fun ctor_desc ->
    (* Tag_name (typ1, typ2) -> Ctor ("Tag_name", "type", [value_of_typ typ1, value_of_typ typ2]) *)
    let arg_names =
      ctor_desc.Types.cstr_args
      |>@ begin fun arg_type ->
          let arg_name = Name.gen_ ~avoid:(!new_names @ avoid_names) ~base_name:(Name.from_type arg_type) in
          new_names := arg_name :: !new_names;
          arg_name
      end
    in
    let case_pat =
      (* Tag_name (typ1, typ2) *)
      let args_pat_opt =
        (match arg_names with
        | []         -> None
        | [arg_name] -> Some (Pat.var arg_name)
        | arg_names  -> Some (Pat.tuple (List.map Pat.var arg_names))
        )
      in
      (* Assuming constructors don't need path prefixes .. see https://github.com/ocaml/merlin/blob/v3.3.8/src/analysis/destruct.ml.new for how to change that when the time comes *)
      Pat.construct (Longident.lident ctor_desc.cstr_name) args_pat_opt
    in
    Exp.case case_pat Exp.hole
  )

let gen_ctor_cases_from_ctor_name ~avoid_names ctor_name tenv =
  begin match Env.lookup_constructor (Longident.Lident ctor_name) tenv with
  | { cstr_res = { desc = Types.Tconstr (type_path, _, _); _ } ; _ } -> gen_ctor_cases ~avoid_names type_path tenv
  | _ -> []
  end
