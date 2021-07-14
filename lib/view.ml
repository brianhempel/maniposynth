open Camlboot_interpreter
open Vis
open Shared
open Shared.Ast
open Shared.Util

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


let body   ?(attrs = [])       inners = tag "body" ~attrs inners
let div    ?(attrs = [])       inners = tag "div" ~attrs inners
let span   ?(attrs = [])       inners = tag "span" ~attrs inners
let table  ?(attrs = [])       inners = tag "table" ~attrs inners
let tr     ?(attrs = [])       inners = tag "tr" ~attrs inners
let td     ?(attrs = [])       inners = tag "td" ~attrs inners
let button ?(attrs = [])       inners = tag "button" ~attrs inners
let box    ?(attrs = []) klass inners =
  let attrs = ("class", ("box " ^ klass))::attrs in
  div ~attrs inners

let string_of_pat ?(editable = true) pat =
  let code = Pat.to_string pat in
  if editable
  then span ~attrs:[("data-in-place-edit-loc", Serialize.string_of_loc pat.ppat_loc)] [code]
  else code
let string_of_exp ?(editable = true) exp =
  let code = Exp.to_string exp in
  if editable
  then span ~attrs:[("data-in-place-edit-loc", Serialize.string_of_loc exp.pexp_loc)] [code]
  else code

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





let rec apply_visualizers assert_results visualizers env type_env (value : Data.value) =
  if visualizers = [] then "" else
  let result_htmls =
    visualizers
    |>@@ begin fun { exp } ->
      match value.type_opt with
      | Some vtype ->
        (* print_endline @@ "1 " ^ Type.to_string typ; *)
        (* if (let r = Type.does_unify typ vtype in print_endline @@ "2 " ^ Type.to_string vtype; r) then begin *)
        let vis_type = Type.of_exp ~type_env exp in
        (* Does the first argument of the vis function unify with the runtime value's type? *)
        let vis_type_parts = Type.flatten_arrows vis_type in
        (* print_endline @@ "3 " ^ Type.to_string vis_type ^ " ~ " ^ Type.to_string vtype; *)
        if List.length vis_type_parts >= 1 && Type.does_unify (List.hd vis_type_parts) vtype then begin
          (* print_endline @@ "3 " ^ Type.to_string vis_type ^ " ~ " ^ Type.to_string vtype; *)
          let (fval, _) =
            Eval.with_gather_asserts begin fun () ->
              let exp_to_run = Exp.from_string @@ "try (" ^ Exp.to_string exp ^ ") with _ -> (??)" in
              Eval.eval_expr Loc_map.empty Primitives.prims env (fun _ -> None) Trace.new_trace_state 0 exp_to_run
            end in
          let matching_asserts =
            assert_results
            |>@? begin fun Data.{ f; arg; _ } ->
              (* print_endline @@ string_of_bool @@ values_equal_for_assert value arg; *)
              (* Data.pp_print_value Format.std_formatter fval; *)
              (* Data.pp_print_value Format.std_formatter f; *)
              (* Format.pp_print_bool Format.std_formatter (values_equal_for_assert fval f); *)
              (* Format.pp_print_bool Format.std_formatter (values_equal_for_assert value arg); *)
              (* Format.pp_force_newline Format.std_formatter (); *)
              (* print_endline @@ string_of_bool @@ values_equal_for_assert fval f; *)
              Assert_comparison.values_equal_for_assert value arg && Assert_comparison.values_equal_for_assert fval f
            end in
          (* print_endline @@ string_of_int (List.length assert_results); *)
          let all_passed = List.for_all (fun Data.{ passed; _ } -> passed) matching_asserts in
          let any_failures = List.exists (fun Data.{ passed; _ } -> not passed) matching_asserts in
          (* START HERE *)
          let exp_to_run =
            Exp.from_string @@ "try teeeeeeeeeeeeeeempf teeeeeeeeeeeeeeemp with _ -> (??)" in
          let env = Envir.env_set_value "teeeeeeeeeeeeeeempf" fval env in
          let env = Envir.env_set_value "teeeeeeeeeeeeeeemp" value env in
          let (result_value, _) =
            Eval.with_gather_asserts begin fun () ->
              Eval.eval_expr Loc_map.empty Primitives.prims env (fun _ -> None) Trace.new_trace_state 0 exp_to_run
            end in
          let wrap html =
            if any_failures then
              span ~attrs:[("class", "failing")] [html]
            else if all_passed && matching_asserts <> [] then
              span ~attrs:[("class", "passing")] [html]
            else
              html in
          let assert_results =
            if all_passed then [] else
            matching_asserts
            |>@ begin fun Data.{ expected; expected_exp; _} ->
              span ~attrs:[("data-in-place-edit-loc", Serialize.string_of_loc expected_exp.pexp_loc)]
                [html_of_value [] [] Envir.empty_env Env.empty expected]
            end in
          let code_to_assert_on = Exp.apply exp [(Nolabel, exp_of_value value)] |> Exp.to_string in
          [ span ~attrs:[("class", "derived-vis-value")] @@
              assert_results @
              [wrap @@ html_of_value ~code_to_assert_on [] [] Envir.empty_env Env.empty result_value]
          ]
        end else
          []
      | None -> []
    end
  in
  span ~attrs:[("class", "derived-vis-values")] result_htmls


and html_of_value ?code_to_assert_on assert_results visualizers env type_env ({ v_ = value_; _} as value : Data.value) =
  let recurse = html_of_value assert_results visualizers env type_env in
  let open Data in
  let active_vises = visualizers |>@ Vis.to_string in
  let possible_vises =
    match value.type_opt with
    | Some val_typ -> Vis.possible_vises_for_type val_typ type_env |>@ Vis.to_string
    | None -> [] in
  let perhaps_type_attr         = match value.type_opt    with Some typ               -> [("data-type", Shared.Ast.Type.to_string typ)]  | _ -> [] in
  let perhaps_code_to_assert_on = match code_to_assert_on with Some code_to_assert_on -> [("data-code-to-assert-on", code_to_assert_on)] | _ -> [] in
  let wrap_value str =
    span
      ~attrs:(
        [("data-active-vises", String.concat "  " active_vises)] @
        [("data-possible-vises", String.concat "  " possible_vises)] @
        perhaps_type_attr @
        perhaps_code_to_assert_on @
        [("class", "value"); ("data-value", Serialize.string_of_value value)]
      )
      [str] in
  wrap_value @@
  apply_visualizers assert_results visualizers env type_env value ^
  match value_ with
  | Bomb                                     -> "💣"
  | Hole _                                   -> "??"
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
  | ExCall _                                 -> "ExCall ShouldntSeeThis"
  | ExDontCare                               -> "ExDontCare ShouldntSeeThis"


let html_of_values_for_loc trace assert_results type_env visualizers loc =
  span
    ~attrs:[ ("data-loc", Serialize.string_of_loc loc) ] (* View root for visualizers, also for determining where to place new asserts before *)
    begin
      trace
      |> Trace.entries_for_loc loc
      |> List.map begin fun (_, _, value, env) -> html_of_value assert_results visualizers env type_env value end
    end

(* Labels and values may be displayed in different ways (standalone box, or as table cells) *)
let label_and_values trace assert_results lookup_exp_typed (exp : Parsetree.expression) =
  let type_env =
    lookup_exp_typed exp.pexp_loc |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs exp.pexp_attributes in
  ( string_of_exp exp
  , html_of_values_for_loc trace assert_results type_env visualizers exp.pexp_loc
  )

let html_box_of_exp  trace assert_results lookup_exp_typed (exp : Parsetree.expression) =
  let (label, values_html) = label_and_values trace assert_results lookup_exp_typed exp in
  html_box label values_html

let rec fun_rows trace assert_results lookup_exp_typed (param_label : Asttypes.arg_label) param_exp_opt param_pat body_exp =
  let default_exp_str =
    match param_exp_opt with
    | None             -> ""
    | Some default_exp -> " = " ^ string_of_exp default_exp
  in
  ( tr
    [ td
        ~attrs:[("class", "label")]
        [string_of_arg_label param_label ^ string_of_pat param_pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
    ; td [html_of_values_for_loc trace assert_results Env.empty [] param_pat.ppat_loc]
    ]
  ) :: rows_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed body_exp

(* I was thinking of ensuring there's space for bindings before even simple expressions...:/ *)
and rows_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed (exp : Parsetree.expression) =
  let open Parsetree in
  let rec gather_vbs exp =
    match exp.pexp_desc with
    | Pexp_let (_, vbs, e)   -> vbs @ gather_vbs e
    | Pexp_sequence (e1, e2) -> [Vb.mk (Pat.any ()) e1] @ gather_vbs e2
    | _                      -> []
  in
  let rec terminal_exp exp = (* Dual of gather_vbs *)
    match exp.pexp_desc with
    | Pexp_let (_, _, e)    -> terminal_exp e
    | Pexp_sequence (_, e2) -> terminal_exp e2
    | _                     -> exp
  in
  let html_of_vb vb =
    box "value_binding" @@
      match vb.pvb_pat.ppat_desc with
      | Ppat_any -> [ html_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed vb.pvb_expr ]
      | _ ->
        [ string_of_pat vb.Parsetree.pvb_pat
        ; html_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed vb.pvb_expr
        ] in
  let single_exp () =
    let (label, values_html) = label_and_values trace assert_results lookup_exp_typed exp in
    [ tr [td ~attrs:[("colspan", "2")] [""]]
    ; tr [td ~attrs:[("colspan", "2"); ("class", "label")] [label]]
    ; tr [td ~attrs:[("colspan", "2"); ("class", "values")] [values_html]]
    ]
  in
  let unhandled node_kind_str =
    [ tr [td ~attrs:[("colspan", "2")] [""]]
    ; tr [td ~attrs:[("colspan", "2")] ["don't know how to handle nodes of kind " ^ node_kind_str]]
    ]
  in
  match exp.pexp_desc with
  | Pexp_let (_, _, _)
  | Pexp_sequence (_, _)      ->
    let (label, values_html) = label_and_values trace assert_results lookup_exp_typed (terminal_exp exp) in
    [ tr [td ~attrs:[("colspan", "2")] (gather_vbs exp |>@ html_of_vb)]
    ; tr [td ~attrs:[("colspan", "2"); ("class", "label")] [label]]
    ; tr [td ~attrs:[("colspan", "2"); ("class", "values")] [values_html]]
    ]
  | Pexp_letmodule (_, _, _)  -> unhandled "letmodule"
  | Pexp_letexception (_, _)  -> unhandled "letexception"
  | Pexp_open (_, _, _)       -> unhandled "open"
  | Pexp_function _           -> unhandled "function"
  | Pexp_fun ( param_label
             , param_exp_opt
             , param_pat
             , body_exp)      -> fun_rows trace assert_results lookup_exp_typed param_label param_exp_opt param_pat body_exp
  | Pexp_match (_, _)         -> unhandled "match"
  | Pexp_ifthenelse (_, _, _) -> unhandled "if then else"
  | _                         -> single_exp ()

and html_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed (exp : Parsetree.expression) =
  table (rows_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed exp)

let htmls_of_top_level_value_binding trace assert_results lookup_exp_typed (vb : Parsetree.value_binding) =
  let drop_target_before_vb (vb : Parsetree.value_binding) =
    div ~attrs:
      [ ("data-before-vb-id", Serialize.string_of_loc vb.pvb_loc)
      ; ("style", "height: 2em")
      ] []
  in
  [ drop_target_before_vb vb
  ; box "value_binding"
      @@ [ string_of_pat vb.pvb_pat ]
      @  [ html_ensure_vbs_canvas_of_exp trace assert_results lookup_exp_typed vb.pvb_expr ]
  ]

let html_of_structure_item trace assert_results lookup_exp_typed (item : Parsetree.structure_item) =
  let open Parsetree in
  match item.pstr_desc with
  | Pstr_eval (_, _)            -> failwith "can't handle Pstr_eval"
  | Pstr_value (_rec_flag, vbs) -> String.concat "" (List.concat @@ List.map (htmls_of_top_level_value_binding trace assert_results lookup_exp_typed) vbs)
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


let drawing_tools tenv =
  let ctors_folder ({Types.cstr_res; _} as ctor_desc) out =
    if Type.is_exn_type cstr_res then out else (* Exclude exceptions. *)
    (* let ctor_type =
      match cstr_args with
      | []      -> cstr_res
      | [arg_t] -> Type.unflatten_arrows [arg_t; cstr_res]
      | args    -> Type.unflatten_arrows [Type.tuple args; cstr_res]
    in *)
    let type_str = Type.to_string cstr_res in
    let existing = SMap.find_opt type_str out ||& [] in
    SMap.add type_str (ctor_desc :: existing) out
  in
  let ctors_by_type_str = Env.fold_constructors ctors_folder None(* not looking in a nested module *) tenv SMap.empty in
  let lits =
    [ (Predef.type_int,  List.init 10 (fun n -> Exp.int_lit n))
    ; (Predef.type_bool, [Exp.simple_var "true"; Exp.simple_var "false"])
    ]
  in
  let examples depth_limit {Types.cstr_name; cstr_args; cstr_res = _; _} =
    (* START HERE: need to do standard pick arg + unify & repeat as in Synth.ml *)
    [Exp.ctor cstr_name (cstr_args |>@ (fun _ -> Exp.hole))]
    |>@ Exp.to_string
  in
  span
    ~attrs:[("class", "tools")]
    begin
      ctors_by_type_str
      |> SMap.bindings
      |>@ begin fun (type_str, ctors) ->
        let ctor_tools = ctors |>@ (fun ctor_desc -> span ~attrs:[("class", "tool")] (examples SMap.empty ctor_desc)) in
        span ~attrs:[("class", "tool")] [type_str ^ " ▾"; span ~attrs:[("class", "tools")] ctor_tools]
      end
    end


let html_str (structure_items : Parsetree.structure) (trace : Trace.t) (assert_results : Data.assert_result list) lookup_exp_typed final_tenv =
  html
    [ head
        [ title "Maniposynth"
        ; meta [("charset", "UTF-8")]
        ; stylesheet "/assets/maniposynth.css"
        ; script ~src:"/assets/maniposynth.js" ""
        ; script ~src:"/assets/reload_on_file_changes.js" ""
        ]
    ; body begin
        [ div ~attrs:[("id", "topbar")] ([span ~attrs:[("class","undo tool")] ["Undo"]; span ~attrs:[("class","redo tool")] ["Redo"]] @ [drawing_tools final_tenv])
        ; div ~attrs:[("id", "inspector")] [div ~attrs:[("id", "type-of-selected")] []; div ~attrs:[("id", "vises-for-selected")] []]
        ; button ~attrs:[("id", "synth-button")] ["Synth"]
        ]
        @ List.map (html_of_structure_item trace assert_results lookup_exp_typed) structure_items
      end
    ]
