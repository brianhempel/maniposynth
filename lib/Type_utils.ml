(* It is possible that if we replace (??) with (failwith "") we do not need to use merlin *)

let final_env_and_typed_structure_of_file path =
  (* ocamlc -bin-annot simple.ml ... but this prodcues partial implemenations, merlin instead produces a single structure *)
  (* ../custom_merlin/ocamlmerlin single dump -what typedtree -filename "simple.ml" < simple.ml *)
  let merlin_output_path = 
    let cmd = "../custom_merlin/ocamlmerlin single dump -what typedtree -filename '" ^ path ^ "' < " ^ path in
    (* {"class":"return","value":"simple.ml.merlin.cmt","notifications":[],"timing":{"clock":21,"cpu":20,"query":3,"pp":0,"reader":11,"ppx":0,"typer":6,"error":0}} *)
    let open Yojson.Basic.Util in 
    (* Sys_utils.command ~verbose:true cmd *)
    Sys_utils.command ~verbose:false cmd
    |> Yojson.Basic.from_string
    |> member "value"
    |> to_string
  in
  let open Cmt_format in
  let cmt = read_cmt merlin_output_path in
  match cmt.cmt_annots with
  | Implementation structure ->
      (* https://discuss.ocaml.org/t/getting-the-environment-from-the-ast-in-cmt/4287/2 *)
      (* and  https://github.com/ocaml/ocaml/blob/4.11/tools/read_cmt.ml *)
      Envaux.reset_cache ();
      List.iter Load_path.add_dir (List.rev cmt.cmt_loadpath);
      (Envaux.env_of_only_summary (List_utils.last structure.str_items).str_env, structure)
  | Partial_implementation _ -> failwith "Cmt_format.Partial_implementation"
  | Packed (_, _)            -> failwith "Cmt_format.Packed"
  | Interface _              -> failwith "Cmt_format.Interface"
  | Partial_interface _      -> failwith "Cmt_format.Partial_interface"


(* Btype.fold_type_expr only applys f to the immediate children. *)
let deep_fold_type_expr f init typ =
  let rec f' acc typ =
    let acc' = Btype.fold_type_expr f' acc typ in
    f acc' typ
  in
  f' init typ


let rec arrow_types_flat (typ : Types.type_expr) : Types.type_expr list =
  let typ = Btype.repr typ in
  match typ.desc with
  | Types.Tarrow (_label, l_type, r_type, _commutable) ->
    Btype.repr l_type :: arrow_types_flat r_type
  | _ -> [typ]

let flatten_type_expr (typ : Types.type_expr) : Types.type_expr list =
  deep_fold_type_expr (Fun.flip List.cons) [] typ