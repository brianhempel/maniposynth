open Parsetree
open Utils

(* 
  Tracepoints:

  1. Just inside fun bodies:
      - setting the frame number
      - emitting the argument values
  2. Var uses (skeletonized as Apply's)
  3. Apply returns
  4. Construct returns (basically Apply returns)
*)

type value =
  | Ctor of string * string * value list (* name, type name, args *)
  | Failure of int (* frame_n *)
  [@@deriving yojson]

type tracesnap =
  | Tracesnap of int * string * value (* frame_n, id str, value *)
  [@@deriving yojson]

type trace = tracesnap list

(* let value_of_nat nat =
  match nat with
  | Z      -> Ctor ("Z", "nat", [])
  | S nat1 -> Ctor ("S", "nat", [value_of_nat nat1]) *)

let loc = Location.none (* For metaquote *)

let code = Ast_utils.Exp.of_string

let name_from_type = Name_utils.name_from_type


let tracepoint_placeholder ?(id : Ast_id.t option) (expr : expression) =
  let id = Option.value id ~default:(Ast_id.of_expr expr) in
  let id_str_exp = Ast_utils.Exp.string (Ast_id.string_of_t id) in
  [%expr try tracepoint frame_n [%e id_str_exp] [%e expr] with Hole failure_frame_n -> tracepoint_failure frame_n [%e id_str_exp] failure_frame_n]

let rec map_first_non_fun f expr =
  match expr with
  | [%expr fun [%p? param] -> [%e? body]] ->
      let body' = map_first_non_fun f body in
      let loc = expr.pexp_loc in
      [%expr fun [%p param] -> [%e body']]
  | _ ->
      f expr


(* Provide a .ml file path. It will be mutated in place. *)
let add_tracepoint_placeholders trace_file_path toplevel_phrases =
  let open Ast_mapper in
  let add_tracepoints mapper expr =
    match expr with
    | [%expr fun [%p? param] -> [%e? body]] ->
      (match Ast_utils.Pat.get_var_name_opt param with
      | Some name ->
          let body' = mapper.expr mapper body in
          let body'' =
            body'
            |> map_first_non_fun (fun real_body ->
              let tp_expr = tracepoint_placeholder ~id:(Ast_id.of_pat param) (Ast_utils.Exp.var name) in
              [%expr ignore [%e tp_expr] ; [%e real_body]]
            )
          in
          let loc = expr.pexp_loc in
          [%expr fun [%p param] -> [%e body'']]          
      | None ->
          default_mapper.expr mapper expr
      )

    | { pexp_desc = (Pexp_ident _ | Pexp_apply _ | Pexp_construct _); _ } ->
        let deeper = default_mapper.expr mapper expr in
        tracepoint_placeholder deeper
  
    | _ ->
      default_mapper.expr mapper expr
  in
  let add_frame_counters mapper expr =
    match expr with
    | [%expr fun [%p? param] -> [%e? body]] ->
        if not (Ast_utils.Exp.is_fun body) then
          let loc = expr.pexp_loc in
          let body' = mapper.expr mapper body in
          [%expr fun [%p param] -> let frame_n = next_frame_n () in [%e body']]
        else
          default_mapper.expr mapper expr
    | _ ->
      default_mapper.expr mapper expr
  in
  let tp_mapper    = { default_mapper with expr = add_tracepoints } in
  let frame_mapper = { default_mapper with expr = add_frame_counters } in
  (*
    Put the top matter before the first let-binding so that we are (hopefully)
    after all the types. Monomorphization will get stuck in a loop if we are not
    after all the types (it will use a type not in frame and keep trying to monomorphize to infinity)
  *)
  let top_matter : structure_item list =
    [ [%stri type value = Ctor of string * string * value list (* name, type name, args *) | Failure of int (* frame_n *)]
    ; [%stri exception Hole of int (* frame_n *)]
    ; [%stri let serialize_str str : string = [%e code {|"\"" ^ String.escaped str ^ "\""|}]] (* metaquote croaks on string literals so we have to parse our own expr. *)
    ; [%stri let rec serialize_value value : string = [%e code {|
               match value with
               | Ctor (ctor_name, type_name, args) ->
                 "[" ^ serialize_str "Ctor" ^
                 "," ^ serialize_str ctor_name ^
                 "," ^ serialize_str type_name ^
                 "," ^ "[" ^ String.concat "," (List.map serialize_value args) ^ "]" ^
                 "]"
               | Failure frame_n ->
                 "[" ^ serialize_str "Failure" ^
                 "," ^ string_of_int frame_n ^
                 "]"
      |}]] (* metaquote croaks on string literals so we have to parse our own expr. *)
    ; [%stri let insert_value_of_type_functions_here = ()]
    ; [%stri let frame_n_ref = ref 0]
    ; [%stri let next_frame_n () = incr frame_n_ref; !frame_n_ref]
    ; [%stri let frame_n = 0]
    ; [%stri let trace_out = open_out_bin [%e Ast_utils.Exp.string trace_file_path]]
    ; [%stri let tracepoint_failure frame_n id_str failure_frame_n = [%e code {|
               output_string trace_out "[";
               output_string trace_out begin
                 [ serialize_str "Tracesnap"
                 ; string_of_int frame_n
                 ; serialize_str id_str
                 ; serialize_value (Failure failure_frame_n)
                 ] |> String.concat ","
               end;
               output_string trace_out "]\n";
               flush trace_out;
               raise (Hole failure_frame_n)
      |}]]
    ; [%stri let tracepoint _frame_n _id_str x = x]
    ]
  in
  let rec add_top_matter structure_items =
    match structure_items with
    | structure_item::rest ->
        (match structure_item.pstr_desc with
        | Pstr_primitive _ | Pstr_type _ | Pstr_typext _
        | Pstr_exception _ | Pstr_open _ | Pstr_include _ ->
            structure_item :: add_top_matter rest
        | _ ->
            top_matter @ structure_items   
        )
    | [] ->
      top_matter
  in
  toplevel_phrases
  |> Ast_utils.apply_mapper_to_toplevel_phrases tp_mapper
  |> Ast_utils.apply_mapper_to_toplevel_phrases frame_mapper
  |> Ast_utils.structure_of_toplevel_phrases
  |> add_top_matter 
  |> Ast_utils.toplevel_phrases_of_structure



(* let rec serialize_value value : string =
  let serialize_str str = "\"" ^ String.escaped str ^ "\"" in
  match value with
  | Ctor (ctor_name, type_name, args) ->
    "[" ^ serialize_str ctor_name ^
    "," ^ serialize_str type_name ^
    "," ^ "[" ^ String.concat "," (List.map serialize_value args) ^ "]" ^
    "]" *)

let top_level_value_bindings_of_structure (structure : Typedtree.structure) : Typedtree.value_binding list =
  let vbs = ref [] in
  let iterator =
    let gather_vbs _iterator (structure_item : Typedtree.structure_item) =
      (match structure_item.str_desc with
      | Typedtree.Tstr_value (_rec_flag, item_vbs) ->
          vbs := item_vbs @ !vbs;
          (* Don't iterate deeper. Top level only. *)
          ()
      | _ ->
          (* Don't iterate deeper. Top level only. *)
          ()
      )
    in
    { Tast_iterator.default_iterator with structure_item = gather_vbs }
  in
  iterator.structure iterator structure;
  !vbs

let tracepoint_mono_name_and_type_opt_of_value_binding (vb : Typedtree.value_binding) : (string * Types.type_expr) option =
  match Typedtree.pat_bound_idents_full vb.vb_pat with
  | [(_, str_loced, _)] when String_utils.starts_with str_loced.txt "tracepoint_mono" ->
      let fun_type_expr = vb.vb_expr.exp_type in
      (match Type_utils.arrow_types_flat fun_type_expr  with
      | [_; _; third_arg_type_expr; _] ->
          (* Printtyp.raw_type_expr Format.std_formatter third_arg_type_expr;
          Format.pp_print_newline Format.std_formatter (); *)
          Some (str_loced.txt, third_arg_type_expr)
      | _ ->
          None
      )
  | _ ->
      None

let mk_value_of_type_vb (env : Env.t) (typ : Types.type_expr) =
  let typ = Btype.repr typ in (* Remove Tlink, shallow *)
  let fun_name = "value_of_" ^ name_from_type typ in
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
          let cases =
            ctor_descs
            |> List.map (fun ctor_desc ->
              (* Tag_name (typ1, typ2) -> Ctor ("Tag_name", "type", [value_of_typ typ1, value_of_typ typ2]) *)
              let arg_names =
                ctor_desc.cstr_args
                |> List.mapi (fun i arg_type -> name_from_type arg_type ^ string_of_int i)
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
                Ast_helper.Pat.construct (Name_utils.longident_loced ctor_desc.cstr_name) args_pat_opt
              in
              let case_expr =
                (* Ctor ("Tag_name", "type", [value_of_typ typ1, value_of_typ typ2]) *)
                let ctor_name_expr = Ast_utils.Exp.string ctor_desc.cstr_name in
                let type_name_expr = Ast_utils.Exp.string ((Utils.formatter_to_stringifyer Printtyp.type_expr) typ) in
                let arg_exprs_list =
                  List.map2 (fun arg_type arg_name -> code ("value_of_" ^ name_from_type arg_type ^ " " ^ arg_name))
                    ctor_desc.cstr_args
                    arg_names
                  |> Ast_utils.Exp.list
                in
                [%expr Ctor ([%e ctor_name_expr], [%e type_name_expr], [%e arg_exprs_list])]
              in
              Ast_helper.Exp.case case_pat case_expr
            )
          in
          let match_exp = Ast_helper.Exp.match_ (Ast_utils.Exp.var param_name) cases in
          [%expr fun [%p Ast_utils.Pat.var param_name] -> [%e match_exp]]      
      )
    | _ -> failwith "not a ctor :("
    )
  in
  Ast_helper.Vb.mk (Ast_utils.Pat.var fun_name) fun_expr


(*
Goal:

let tracepoint_mono1 = fun frame_n -> fun id_str -> fun x ->
  output_string trace_out "[";
  output_string trace_out begin
    [ serialize_str "Tracesnap"
    ; string_of_int frame_n
    ; serialize_str id_str
    ; serialize_value (value_of_TYPE x)
    ] |> String.concat ","
  end;
  output_string trace_out "]\n";
  flush trace_out;
  x

*)

let filled_tracepoint_mono_fun_expr (mono_type : Types.type_expr) : Parsetree.expression =
  (* let tracepoint_mono1 frame_n id_str x = ... *)
  code @@ {|
    fun frame_n -> fun id_str -> fun x ->
      output_string trace_out "[";
      output_string trace_out begin
        [ serialize_str "Tracesnap"
        ; string_of_int frame_n
        ; serialize_str id_str
        ; serialize_value (value_of_|} ^ name_from_type mono_type ^ {| x)
        ] |> String.concat ","
      end;
      output_string trace_out "]\n";
      flush trace_out;
      x
  |}


(* Based on https://github.com/ocaml/merlin/blob/v3.3.8/src/analysis/destruct.ml.new *)
let fill_tracepoint_placeholders (env : Env.t) (typed_structure : Typedtree.structure) toplevel_phrases =
  (* let open Types in *)
  (* 1. Find all tracepoint_monoNNN functions and required types, based on their type annotations *)
  let mono_names_and_types =
    typed_structure
    |> top_level_value_bindings_of_structure
    |> List.filter_map tracepoint_mono_name_and_type_opt_of_value_binding
  in
  let types_needed =
    List.map snd mono_names_and_types
    |> List.concat_map Type_utils.flatten_type_expr
  in
  (* 2. Make value_of_type serializer for each type *)
  let value_of_type_value_bindings =
    types_needed
    |> List.map (mk_value_of_type_vb env)
  in
  (* 3. Fill in each tracepoint_monoNNN to use the value_of_type *)
  let fill_tracepoint_monos_mapper =
    let open Ast_mapper in
    let map_vb _mapper (vb : Parsetree.value_binding) =
      match begin
        let (let*) = Option.bind in
        let* fun_name = Ast_utils.Pat.get_var_name_opt vb.pvb_pat in
        let* mono_type = List.assoc_opt fun_name mono_names_and_types in
        Some { vb with pvb_expr = filled_tracepoint_mono_fun_expr mono_type }
      end with
      | None     -> vb  (* No need to recurse, mono functions are all top level *)
      | Some vb' -> vb' (* No need to recurse, mono functions are all top level *)
    in
    { default_mapper with value_binding = map_vb }
  in
  let add_value_of_type_functions_mapper =
    let open Ast_mapper in
    let map_structure_item _mapper (structure_item : Parsetree.structure_item) =
      (* No need to recurse. *)
      match structure_item.pstr_desc with
      | Pstr_value (_is_rec, [vb]) ->
        (match Ast_utils.Pat.get_var_name_opt vb.pvb_pat with
        | Some "insert_value_of_type_functions_here" ->
            { structure_item with pstr_desc = Pstr_value (Recursive, value_of_type_value_bindings) }
        | _ ->
            structure_item
        )
      | _ -> structure_item
    in
    { default_mapper with structure_item = map_structure_item }
  in
  toplevel_phrases
  |> Ast_utils.apply_mapper_to_toplevel_phrases fill_tracepoint_monos_mapper
  |> Ast_utils.apply_mapper_to_toplevel_phrases add_value_of_type_functions_mapper

let fill_holes =
  Ast_utils.map_exprs (function
    | [%expr (??)] -> code {|raise (Hole frame_n)|}
    | expr       -> expr
  )


let run_with_tracing file_path : trace =
  let parsed_with_comments = Parse_unparse.parse_file file_path in
  let trace_file_path = file_path ^ ".trace" in
  let ast' = add_tracepoint_placeholders trace_file_path parsed_with_comments.ast in
  let parsed_with_comments' = { parsed_with_comments with ast = ast'; comments = [] } in
  let out_str = Parse_unparse.unparse file_path parsed_with_comments' in
  (* print_string @@ out_str; *)
  let tp_file_path = file_path ^ ".tp_placeholders" in
  let mono_file_path = tp_file_path ^ ".mono.ml" in
  (* Sys_utils.save_file tp_file_path out_str;
  Sys_utils.copy_file tp_file_path mono_file_path; *)
  Sys_utils.save_file mono_file_path out_str;
  Monomorphize.f mono_file_path;
  let parsed_with_comments = Parse_unparse.parse_file mono_file_path in
  let (env, typed_structure) = Type_utils.final_env_and_typed_structure_of_file mono_file_path in
  let ast' =
    parsed_with_comments.ast
    |> fill_tracepoint_placeholders env typed_structure
    |> fill_holes
  in
  let parsed_with_comments' = { parsed_with_comments with ast = ast' } in
  let out_str = Parse_unparse.unparse file_path parsed_with_comments' in
  (* print_string @@ out_str; *)
  let with_tracing_file_path = file_path ^ ".with_tracing.ml" in
  Sys_utils.save_file with_tracing_file_path out_str;
  (* print_string @@ Sys_utils.command ("ocaml " ^ with_tracing_file_path); *)
  ignore @@ Sys_utils.command ("ocaml " ^ with_tracing_file_path);
  let trace =
    Sys_utils.string_of_file trace_file_path
    |> String.trim
    |> String.split_on_char '\n'
    |> List.filter (not % String.equal "") (* Split on empty string produces [""] *)
    |> List.map (Yojson.Safe.from_string %> tracesnap_of_yojson)
  in
  trace
;;
