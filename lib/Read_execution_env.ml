open Yojson.Basic.Util
open Ocamlformat_lib.Migrate_ast.Parsetree

let callable_opt_of_ctor_dec { pcd_name; pcd_args; _ } : (string * int) option =
  match pcd_args with
  | Pcstr_tuple types -> Some (pcd_name.txt, List.length types)
  | Pcstr_record _    -> None

let callables_of_type_dec { ptype_kind; _ } : (string * int) list =
  match ptype_kind with
  | Ptype_variant ctor_decs ->
      List.filter_map callable_opt_of_ctor_dec ctor_decs
  | _ -> 
      []

let callable_opt_of_value_desc { pval_name; pval_type = { ptyp_desc; _ }; _ } : (string * int) option =
  let rec count_args = function
    | Ptyp_arrow (_arg_label, l_type, r_type) ->
        count_args l_type.ptyp_desc + count_args r_type.ptyp_desc
    | _ ->
        1
  in
  match ptyp_desc with
  | Ptyp_arrow _ ->
      Some (pval_name.txt, count_args ptyp_desc - 1)
  | _ ->
      None
      
let callables_of_sig_item { psig_desc; _ } : (string * int) list =
  match psig_desc with
  | Psig_type (_rec_flag, type_decs) ->
      List.concat_map callables_of_type_dec type_decs
  | Psig_value value_desc ->
      Option.to_list (callable_opt_of_value_desc value_desc)
  | _ ->
      []

let callables_of_string str : (string * int) list =
  let lexbuf = Lexing.from_string str in
  Parse.interface lexbuf
  |> List.concat_map callables_of_sig_item

(* List the callable functions/ctors in a file, along with the number of arguments each expects. *)
let callables_of_file (path : string) : (string * int) list=
  let cmd = "../custom_merlin/ocamlmerlin single dump -what env < " ^ path in
  let merlin_json = Sys_utils.command cmd |> Yojson.Basic.from_string in
  (* {
    "class":"return",
    "value":["type nonrec nat = Z | S of nat","val plus : 'a -> 'b -> 'c"],
    "notifications":[],
    "timing":{"clock":12,"cpu":6,"query":2,"pp":0,"reader":2,"ppx":0,"typer":2,"error":0}
  } *)
  let type_and_function_strs = merlin_json |> member "value" |> to_list |> List.map to_string in
  List.concat_map callables_of_string type_and_function_strs
