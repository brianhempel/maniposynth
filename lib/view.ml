open Camlboot_interpreter
open Ast
open Vis
open Util

let sprintf = Printf.sprintf

let rec print_attrs attrs  =
  match attrs with
  | (name, value)::rest -> sprintf " %s=\"%s\"%s" name value (print_attrs rest)
  | []                  -> ""

let tag name ?(attrs = []) inners =
  sprintf "<%s%s>%s</%s>" name (print_attrs attrs) (String.concat "" inners) name

let lone_tag name ?(attrs = []) () =
  sprintf "<%s%s />" name (print_attrs attrs)

let html ?(attrs = []) inners = tag "html" ~attrs inners
let head ?(attrs = []) inners = tag "head" ~attrs inners

let title ?(attrs = []) str = tag "title" ~attrs [str]
let meta attrs = lone_tag "meta" ~attrs ()
let stylesheet href =
  lone_tag "link" ~attrs:[("rel", "stylesheet"); ("href", href)] ()

let script ?src ?(attrs = []) str =
  match src with
  | Some src_str -> tag "script" ~attrs:(("src", src_str)::attrs) [str]
  | None         -> tag "script" ~attrs                                [str]


let body  ?(attrs = [])       inners = tag "body" ~attrs inners
let div   ?(attrs = [])       inners = tag "div" ~attrs inners
let span  ?(attrs = [])       inners = tag "span" ~attrs inners
let table ?(attrs = [])       inners = tag "table" ~attrs inners
let tr    ?(attrs = [])       inners = tag "tr" ~attrs inners
let td    ?(attrs = [])       inners = tag "td" ~attrs inners
let box   ?(attrs = []) klass inners =
  let attrs = ("class", ("box " ^ klass))::attrs in
  div ~attrs inners

let string_of_pat = Formatter_to_stringifier.f Pprintast.pattern
let string_of_exp = Pprintast.string_of_expression
let string_of_arg_label =
  let open Asttypes in function
  | Nolabel        -> ""
  | Labelled label -> "~" ^ label ^ ":"
  | Optional label -> "?" ^ label ^ ":"


let html_box ?(attrs = []) label content =
  table
    ~attrs
    [ tr [td ~attrs:[("class", "label")] [label]]
    ; tr [td ~attrs:[("class", "values")] [content]]
    ]

let rec apply_visualizers visualizers env (value : Data.value) =
  if visualizers = [] then "" else
  let result_htmls =
    visualizers
    |>@@ begin fun { typ; exp } ->
      match value.type_opt with
      | Some vtype ->
        if Type.does_unify typ vtype then
          let exp_to_run = Exp.apply exp [(Nolabel, Exp.var "teeeeeeeeeeeeeeemp")] in
          let env = Envir.env_set_value "teeeeeeeeeeeeeeemp" value env in
          let result_value = Eval.eval_expr Primitives.prims env (fun _ -> None) Trace.new_trace_state 0 exp_to_run in
          [result_value]
        else
          []
      | None -> []
    end
    |>@ html_of_value [] Envir.empty_env Env.empty
  in
  span ~attrs:[("class", "derived-vis-values")]
    (result_htmls |>@ begin fun result_html -> span ~attrs:[("class", "derived-vis-value")] [result_html] end)


and html_of_value visualizers env type_env ({ v_ = value_; _} as value : Data.value) =
  let recurse = html_of_value visualizers env type_env in
  let open Data in
  let active_vises = visualizers |>@ Vis.to_string in
  let possible_vises =
    (* Right now, possible visualizers are of type 'a -> 'b where 'a unifies with the runtime type of the value, and 'a is non-trivial. *)
    let f _name path value_desc out =
      (* e.g. string_of_float Stdlib.string_of_float : float -> string *)
      (* print_endline @@ name ^ "\t" ^ Path.name path ^ " : " ^ Type.to_string value_desc.Types.val_type; *)
      match (value.type_opt, Type.flatten_arrows value_desc.Types.val_type) with
      | (Some val_type, [arg_type; _]) ->
        begin try
          if Type.does_unify val_type arg_type && Type.to_string arg_type <> "'a" (* ignore trivial functions *)
          then Vis.to_string { typ = arg_type; exp = Exp.from_string @@ String.drop_prefix "Stdlib." (Path.name path) } :: out
          else out
        with _exn ->
          (* Parse.expression fails to parse certain operators like Stdlib.~- *)
          out
          (* begin match Location.error_of_exn exn with
          | Some (`Ok err) -> print_endline (Path.name path); Location.report_error Format.std_formatter err; out
          | _              -> out
          end *)
        end
      | _ -> out in
    let modules = [None; Some (Longident.parse "Stdlib.List")] in
    modules
    |>@@ fun module_lid_opt -> Env.fold_values f module_lid_opt type_env []
    (* |>@@ begin fun (fname, (_, value_or_lvar)) -> match value_or_lvar with Value v -> [(fname, v)] | _ -> [] end *)
    (* |>@ begin fun (fname, fval) -> fval.type_opt |>& Type.to_string |>& (^) (fname ^ " : ") ||& "" |> print_endline end *) in
  let perhaps_type_attr = match value.type_opt with Some typ -> [("data-type", Ast.Type.to_string typ)] | _ -> [] in
  let wrap_value str =
    span
      ~attrs:(
        [("data-active-vises", String.concat "  " active_vises)] @
        [("data-possible-vises", String.concat "  " possible_vises)] @
        perhaps_type_attr @
        [("class", "value"); ("data-value", Serialize.string_of_value value)]
      )
      [str] in
  wrap_value @@
  apply_visualizers visualizers env value ^
  match value_ with
  | Bomb                                     -> "💣"
  | Int int                                  -> string_of_int int
  | Int32 int32                              -> Int32.to_string int32
  | Int64 int64                              -> Int64.to_string int64
  | Nativeint nativeint                      -> Nativeint.to_string nativeint
  | Fun (_, _, _, _, _)                      -> "func"
  | Function (_, _)                          -> "func"
  | String bytes                             -> Exp.to_string (Exp.string_lit (Bytes.to_string bytes)) (* Make sure string is quoted & escaped *)
  | Float float                              -> string_of_float float
  | Tuple values                             -> "(" ^ String.concat ", " (List.map recurse values) ^ ")"
  | Constructor (ctor_name, _, None)         -> ctor_name
  | Constructor (ctor_name, _, Some arg_val) -> ctor_name ^ " " ^ recurse arg_val
  | Prim _                                   -> "prim"
  | Fexpr _                                  -> "fexpr"
  | ModVal _                                 -> "modval"
  | InChannel _                              -> "inchannel"
  | OutChannel _                             -> "outchannel"
  | Record entry_map                         -> entry_map |> SMap.bindings |> List.map (fun (field_name, value_ref) -> field_name ^ " = " ^ recurse !value_ref) |> String.concat "; " |> (fun entries_str -> "{ " ^ entries_str ^ " }")
  | Lz _                                     -> "lazy"
  | Array values_arr                         -> "[! " ^ (values_arr |> Array.to_list |> List.map recurse |> String.concat "; ") ^ " !]"
  | Fun_with_extra_args (_, _, _)            -> "funwithextraargs"
  | Object _                                 -> "object"


let html_of_values_for_loc trace type_env visualizers loc =
  trace
  |> Trace.entries_for_loc loc
  |> List.map begin fun (_, _, value, env) -> html_of_value visualizers env type_env value end
  |> String.concat "\n"


(* let html_box_of_vb (vb : Parsetree.value_binding) =
  html_box
    (string_of_pat vb.pvb_pat ^ " = " ^ string_of_exp vb.pvb_expr)
    "" *)


let html_box_of_exp trace lookup_exp_typed (exp : Parsetree.expression) =
  let type_env =
    lookup_exp_typed exp |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs type_env exp.pexp_attributes in
  html_box
    ~attrs:[ ("data-loc", Serialize.string_of_loc exp.pexp_loc) ]
    (string_of_exp exp)
    (html_of_values_for_loc trace type_env visualizers exp.pexp_loc)


let rec fun_rows trace lookup_exp_typed (param_label : Asttypes.arg_label) param_exp_opt param_pat body_exp =
  let default_exp_str =
    match param_exp_opt with
    | None             -> ""
    | Some default_exp -> " = " ^ string_of_exp default_exp
  in
  ( tr
    [ td [string_of_arg_label param_label ^ string_of_pat param_pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
    ; td [html_of_values_for_loc trace Env.empty [] param_pat.ppat_loc]
    ]
  ) :: rows_ensure_vbs_canvas_of_exp trace lookup_exp_typed body_exp

and rows_ensure_vbs_canvas_of_exp trace lookup_exp_typed (exp : Parsetree.expression) =
  let single_exp () =
    [ tr [td ~attrs:[("colspan", "2")] [""]]
    ; tr [td ~attrs:[("colspan", "2")] [html_box_of_exp trace lookup_exp_typed exp]]
    ]
  in
  let unhandled node_kind_str =
    [ tr [td ~attrs:[("colspan", "2")] [""]]
    ; tr [td ~attrs:[("colspan", "2")] ["don't know how to handle nodes of kind " ^ node_kind_str]]
    ]
  in
  let open Parsetree in
  match exp.pexp_desc with
  | Pexp_let (_, _, _)        -> unhandled "let"
  | Pexp_letmodule (_, _, _)  -> unhandled "letmodule"
  | Pexp_letexception (_, _)  -> unhandled "letexception"
  | Pexp_open (_, _, _)       -> unhandled "open"
  | Pexp_function _           -> unhandled "function"
  | Pexp_fun ( param_label
             , param_exp_opt
             , param_pat
             , body_exp)      -> fun_rows trace lookup_exp_typed param_label param_exp_opt param_pat body_exp
  | Pexp_match (_, _)         -> unhandled "match"
  | Pexp_ifthenelse (_, _, _) -> unhandled "if then else"
  | _                         -> single_exp ()

let html_ensure_vbs_canvas_of_exp trace lookup_exp_typed (exp : Parsetree.expression) =
  table (rows_ensure_vbs_canvas_of_exp trace lookup_exp_typed exp)

let htmls_of_top_level_value_binding trace lookup_exp_typed (vb : Parsetree.value_binding) =
  let drop_target_before_vb (vb : Parsetree.value_binding) =
    div ~attrs:
      [ ("data-before-vb-id", Serialize.string_of_loc vb.pvb_loc)
      ; ("style", "height: 2em")
      ] []
  in
  [ drop_target_before_vb vb
  ; box "value_binding"
      @@ [ string_of_pat vb.pvb_pat ^ " =" ]
      @  [ html_ensure_vbs_canvas_of_exp trace lookup_exp_typed vb.pvb_expr ]
  ]

let html_of_structure_item trace lookup_exp_typed (item : Parsetree.structure_item) =
  let open Parsetree in
  match item.pstr_desc with
  | Pstr_eval (_, _)            -> failwith "can't handle Pstr_eval"
  | Pstr_value (_rec_flag, vbs) -> String.concat "" (List.concat @@ List.map (htmls_of_top_level_value_binding trace lookup_exp_typed) vbs)
  | Pstr_primitive _            -> failwith "can't handle Pstr_primitive"
  | Pstr_type (_, _)            -> "" (* failwith "can't handle Pstr_type" *)
  | Pstr_typext _               -> failwith "can't handle Pstr_typext"
  | Pstr_exception _            -> failwith "can't handle Pstr_exception"
  | Pstr_module _               -> failwith "can't handle Pstr_module"
  | Pstr_recmodule _            -> failwith "can't handle Pstr_recmodule"
  | Pstr_modtype _              -> failwith "can't handle Pstr_modtype"
  | Pstr_open _                 -> failwith "can't handle Pstr_open"
  | Pstr_class _                -> failwith "can't handle Pstr_class"
  | Pstr_class_type _           -> failwith "can't handle Pstr_class_type"
  | Pstr_include _              -> failwith "can't handle Pstr_include"
  | Pstr_attribute _            -> failwith "can't handle Pstr_attribute"
  | Pstr_extension (_, _)       -> failwith "can't handle Pstr_extension"


let html_str (structure_items : Parsetree.structure) (trace : Trace.t) lookup_exp_typed =
  html
    [ head
        [ title "Maniposynth"
        ; meta [("charset", "UTF-8")]
        ; stylesheet "/assets/maniposynth.css"
        ; script ~src:"/assets/maniposynth.js" ""
        ; script ~src:"/assets/reload_on_file_changes.js" ""
        ]
    ; body begin
        [ div ~attrs:[("id", "inspector")] [div ~attrs:[("id", "type-of-selected")] []; div ~attrs:[("id", "vises-for-selected")] []] ]
        @ List.map (html_of_structure_item trace lookup_exp_typed) structure_items
      end
    ]
