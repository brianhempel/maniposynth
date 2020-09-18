open Utils

(*
  Actions generated from the browser and set to server.
  Need to keep format in sync in maniposynth.js
*)

type t =
  | AddCodeToScopeBindings of string * string (* code str and scope id str *)
  | ReplaceCodeAtExpr of string * string (* code str and ast id str *)
  | DeleteExpr of string (* ast id str *)
  | DestructAndReplaceCodeAtExpr of string * string (* destruct path str and ast id str *)
  [@@deriving yojson]

type destruction =
  { type_str  : string
  ; ctor_name : string
  ; arg_n     : int
  } [@@deriving yojson]

type destruct_path = (string * destruction list) (* scrutinee_code, destructions *)
  [@@deriving yojson]

module Parsetree   = Ocamlformat_lib.Migrate_ast.Parsetree
module Ast_helper  = Ocamlformat_lib.Migrate_ast.Selected_version.Ast_helper

let string_of_destruct_path = yojson_of_destruct_path %> Yojson.Safe.to_string
let destruct_path_of_string = Yojson.Safe.from_string %> destruct_path_of_yojson


let unique_var_name toplevel_phrases =
  let names_ref = ref [] in
  let open Ast_iterator in
  let iterator =
    let iter_pat iter pat =
      default_iterator.pat iter pat;
      match Ast_utils.Pat.get_var_name_opt pat with
      | Some name -> names_ref := name :: !names_ref
      | None      -> () 
    in
    let iter_expr iter expr =
      default_iterator.expr iter expr;
      match expr.pexp_desc with
      | Parsetree.Pexp_ident { txt = longident; _ } ->
          names_ref := Longident.last longident :: !names_ref
      | _ ->
          ()
    in
    { default_iterator with pat = iter_pat; expr = iter_expr }
  in
  Ast_utils.apply_iterator_to_toplevel_phrases iterator toplevel_phrases;
  let used_names = List.sort_uniq String.compare !names_ref in
  fun ?(more_names = []) -> fun base_name ->
    let rec loop n =
      let candidate = base_name ^ string_of_int n in
      if List.mem candidate used_names || List.mem candidate more_names
      then loop (n + 1)
      else candidate
    in
    loop 1


let suggested_name_for_expr expr =
  expr
  |> (Utils.formatter_to_stringifyer Pprintast.expression)
  |> String.trim
  |> String.lowercase_ascii
  |> String_utils.parameterize
  |> String.split_on_char '_'
  |> List.filter (fun str -> String.length str > 0 && Char_utils.is_letter str.[0])
  |> String.concat "_"
  |> (function | "" -> "var" | str -> str)


let add_exp_to_scope_bindings ~expr' ~scope_id toplevel_phrases =
  let open Parsetree in
  let name = unique_var_name toplevel_phrases (suggested_name_for_expr expr') in
  let pat    = Ast_utils.Pat.var name in
  let new_vb = Ast_helper.Vb.mk pat expr' in
  let rec f expr =
    match expr.pexp_desc with
    | Pexp_let (Recursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Recursive, vbs @ [new_vb], body_expr) }
    | Pexp_let (Nonrecursive, vbs, body_expr) ->
        { expr with pexp_desc = Pexp_let (Nonrecursive, vbs, f body_expr) }
    | _ ->
        Ast_helper.Exp.let_ Recursive [new_vb] expr
  in
  Ast_utils.map_expr_by_id ~expr_id:scope_id ~f toplevel_phrases

exception Found

let insert_match file_path (scrutinee_code, destructions) expr_id toplevel_phrases =
  let (env, _typed_structure) = Type_utils.final_env_and_typed_structure_of_file file_path in
  (* find pattern match insert location *)
  let scope_expr_ref = ref None in
  begin
    toplevel_phrases
    |> Ast_utils.iterate_exprs (fun iterate_deeper expr ->
      match expr with
      | [%expr fun [%p? _arg] -> [%e? body]] ->
          (try iterate_deeper () with Found -> scope_expr_ref := Some body)
      | _ ->
          if Ast_id.has_id ~expr expr_id
          then raise Found
          else iterate_deeper ()
    )
  end;
  let scope_expr = match !scope_expr_ref with Some expr -> expr | None -> failwith "expr_id to replace not found inside any function" in
  let scope_id = Ast_id.of_expr scope_expr in
  (* build patterns *)
  match destructions with
  | [{ type_str; ctor_name = destruct_ctor_name; arg_n }] ->
      (* find type of scrutinee *)
      let (type_path, _type_dec) = Env.find_type_by_name (Name_utils.longident type_str) env in
      let ctor_descs = fst (Env.find_type_descrs type_path env) in
      let choose_name = unique_var_name toplevel_phrases in
      let cases =
        let open Name_utils in
        let more_names_ref = ref [] in
        ctor_descs
        |> List.map (fun ctor_desc ->
          (* Tag_name (typ1, typ2) -> Ctor ("Tag_name", "type", [value_of_typ typ1, value_of_typ typ2]) *)
          let arg_names =
            ctor_desc.Types.cstr_args
            |> List.map (fun arg_type ->
                let arg_name = choose_name ~more_names:!more_names_ref (name_from_type arg_type) in
                more_names_ref := arg_name :: !more_names_ref;
                arg_name
            )
          in
          let case_pat =
            (* Tag_name (typ1, typ2) *)
            let args_pat_opt =
              (match arg_names with
              | []         -> None
              | [arg_name] -> Some (Ast_utils.Pat.var arg_name)
              | arg_names  -> Some (Ast_helper.Pat.tuple (List.map Ast_utils.Pat.var arg_names))
              )
            in
            (* Assuming constructors don't need path prefixes .. see https://github.com/ocaml/merlin/blob/v3.3.8/src/analysis/destruct.ml.new for how to change that when the time comes *)
            Ast_helper.Pat.construct (longident_loced ctor_desc.cstr_name) args_pat_opt
          in
          let case_expr =
            if ctor_desc.Types.cstr_name = destruct_ctor_name then
              let var' = Ast_utils.Exp.var (List.nth arg_names arg_n) in
              scope_expr
              |> Ast_utils.Exp.replace_by_id ~expr_id ~expr':var'
            else
              Ast_utils.Exp.var "??"
          in
          Ast_helper.Exp.case case_pat case_expr
        )
      in
      let match_exp = Ast_helper.Exp.match_ (Ast_utils.Exp.of_string scrutinee_code) cases in
      Ast_utils.replace_expr_by_id ~expr_id:scope_id ~expr':match_exp toplevel_phrases

  | _ ->
      print_endline "Only single destruction supported for now.";
      toplevel_phrases


  (* let typ = Btype.repr typ in (* Remove Tlink, shallow *)
  let fun_expr =
    let open Types in
    let param_name = name_from_type typ in
    (match typ.desc with
    | Tconstr (path, _type_parameters, _abbrev_memo_ref) ->
      (* Path.print Format.std_formatter path;
      Format.pp_print_newline Format.std_formatter ();
      !Env.print_path Format.std_formatter path;
      Format.pp_print_newline Format.std_formatter (); *)
      (match fst (Env.find_type_descrs path env) with
      | [] -> failwith "no constructors"
      | ctor_descs ->
 *)

  (* let scope_id = scope_id_of_expr_id in *)

(* If expr_id is the RHS of a binding, delete the binding. *)
let delete_binding expr_id ({ Parsetree.pexp_desc; _ } as expr) =
  let open Parsetree in
  match pexp_desc with
  | Parsetree.Pexp_let (rec_flag, vbs, body) ->
      (match
        vbs
        |> List.filter (fun ({ pvb_expr; _ }) -> not (Ast_id.has_id ~expr:pvb_expr expr_id))
      with
      | [] ->
          body
      | new_vbs ->
          { expr with pexp_desc = Parsetree.Pexp_let (rec_flag, new_vbs, body) }
      )
  | _ -> expr





let f file_path action =
  let parsed_with_comments = Parse_unparse.parse_file file_path in
  let ast' = 
    match action with
    | AddCodeToScopeBindings (new_code, scope_id_str) ->
      let expr' = Ast_utils.Exp.of_string new_code in
      let scope_id = Ast_id.t_of_string scope_id_str in
      add_exp_to_scope_bindings ~expr' ~scope_id parsed_with_comments.ast
    | ReplaceCodeAtExpr (new_code, expr_id_str) ->
      let expr' = Ast_utils.Exp.of_string new_code in
      let expr_id = Ast_id.t_of_string expr_id_str in
      Ast_utils.replace_expr_by_id ~expr_id ~expr' parsed_with_comments.ast
    | DestructAndReplaceCodeAtExpr (destruct_path_str, expr_id_str) ->
      let destruct_path = destruct_path_of_string destruct_path_str in
      let expr_id = Ast_id.t_of_string expr_id_str in
      insert_match file_path destruct_path expr_id parsed_with_comments.ast
    | DeleteExpr expr_id_str ->
      let expr_id = Ast_id.t_of_string expr_id_str in
      parsed_with_comments.ast
      |> Ast_utils.map_exprs (delete_binding expr_id)
      |> Ast_utils.replace_expr_by_id ~expr_id ~expr':(Ast_utils.Exp.var "??")
in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let new_file_code = Parse_unparse.unparse file_path parsed_with_comments' in
  Sys_utils.save_file file_path new_file_code

