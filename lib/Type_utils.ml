let typed_structure_of_file path =
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
  match (read_cmt merlin_output_path).cmt_annots with
  | Implementation structure -> structure
  | Partial_implementation _ -> failwith "Cmt_format.Partial_implementation"
  | Packed (_, _)            -> failwith "Cmt_format.Packed"
  | Interface _              -> failwith "Cmt_format.Interface"
  | Partial_interface _      -> failwith "Cmt_format.Partial_interface"

