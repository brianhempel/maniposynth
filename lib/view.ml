open Parsetree
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

let loc_attr loc = ("data-loc", Serialize.string_of_loc loc)

let body    ?(attrs = [])       inners = tag "body" ~attrs inners
let nav     ?(attrs = [])       inners = tag "nav" ~attrs inners
let div     ?(attrs = [])       inners = tag "div" ~attrs inners
let h1      ?(attrs = [])       inners = tag "h1" ~attrs inners
let h2      ?(attrs = [])       inners = tag "h2" ~attrs inners
let span    ?(attrs = [])       inners = tag "span" ~attrs inners
let img     ~attrs                     = tag "img" ~attrs []
let table   ?(attrs = [])       inners = tag "table" ~attrs inners
let tr      ?(attrs = [])       inners = tag "tr" ~attrs inners
let td      ?(attrs = [])       inners = tag "td" ~attrs inners
let button  ?(attrs = [])       inners = tag "button" ~attrs inners
let textbox ?(attrs = [])       inners = tag "input" ~attrs:(attrs @ [("type","text")]) inners
let box     ?(attrs = []) ~loc ~parsetree_attrs klass inners =
  let perhaps_pos_attr =
    match Pos.from_attrs parsetree_attrs with
    | Some { x; y } -> [("style", "left:" ^ string_of_int x ^ "px;top:" ^ string_of_int y ^ "px;")]
    | None          -> []
  in
  let attrs = ("class", ("box " ^ klass)) :: loc_attr loc:: perhaps_pos_attr @ attrs in
  div ~attrs inners

let html_of_pat ?(editable = true) pat =
  let code = Pat.to_string { pat with ppat_attributes = [] } in (* Don't show vis attrs. *)
  if editable
  then span ~attrs:[("data-in-place-edit-loc", Serialize.string_of_loc pat.ppat_loc);("class","pat")] [code]
  else code
let html_of_exp ?(editable = true) ?(type_lookups = Typing.empty_lookups) exp =
  let code = Exp.to_string { exp with pexp_attributes = [] } in (* Don't show pos/vis attrs. *)
  if editable
  then
    let perhaps_type_attr = type_lookups.lookup_exp exp.pexp_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.exp_type)]) ||& [] in
    let perhaps_suggestions_attr = if Exp.is_hole exp then [("data-suggestions", String.concat "  " Hole_suggestions.suggestions)] else [] in
    span ~attrs:([("data-in-place-edit-loc", Serialize.string_of_loc exp.pexp_loc);("class","exp")] @ perhaps_type_attr @ perhaps_suggestions_attr) [code]
  else code

let string_of_arg_label =
  let open Asttypes in function
  | Nolabel        -> ""
  | Labelled label -> "~" ^ label ^ ":"
  | Optional label -> "?" ^ label ^ ":"





let rec apply_visualizers assert_results visualizers env type_env (value : Data.value) =
  if visualizers = [] then "" else
  let result_htmls =
    visualizers
    |>@@ begin fun { exp } ->
      match (value.type_opt, Type.of_exp_opt ~type_env exp) with
      | (Some vtype, Some vis_type) ->
        (* print_endline @@ "1 " ^ Type.to_string typ; *)
        (* if (let r = Type.does_unify typ vtype in print_endline @@ "2 " ^ Type.to_string vtype; r) then begin *)
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
              (* Data.value_to_string fval; *)
              (* Data.value_to_string f; *)
              (* Format.pp_print_bool Format.std_formatter (values_equal_for_assert fval f); *)
              (* Format.pp_print_bool Format.std_formatter (values_equal_for_assert value arg); *)
              (* Format.pp_force_newline Format.std_formatter (); *)
              (* print_endline @@ string_of_bool @@ values_equal_for_assert fval f; *)
              Assert_comparison.values_equal_for_assert value arg && Assert_comparison.values_equal_for_assert fval f
            end in
          (* print_endline @@ string_of_int (List.length assert_results); *)
          let all_passed = List.for_all (fun Data.{ passed; _ } -> passed) matching_asserts in
          let any_failures = List.exists (fun Data.{ passed; _ } -> not passed) matching_asserts in
          let exp_to_run =
            Exp.from_string @@ "try teeeeeeeeeeeeeeempf teeeeeeeeeeeeeeemp with _ -> (??)" in
          let env = Envir.env_set_value "teeeeeeeeeeeeeeempf" fval env in
          let env = Envir.env_set_value "teeeeeeeeeeeeeeemp" value env in
          let (result_value, _) =
            (* "with_gather_asserts" so failed asserts don't crash execution *)
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
      | _ ->
        []
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
  let perhaps_type_attr         = match value.type_opt    with Some typ               -> [("data-type", Type.to_string typ)]  | _ -> [] in
  let perhaps_code_to_assert_on = match code_to_assert_on with Some code_to_assert_on -> [("data-code-to-assert-on", code_to_assert_on)] | _ -> [] in
  let wrap_value str =
    span
      ~attrs:(
        [("data-active-vises", String.concat "  " active_vises)] @
        [("data-possible-vises", String.concat "  " possible_vises)] @
        perhaps_type_attr @
        perhaps_code_to_assert_on @
        [("class", "value"); ("data-vtrace", Serialize.string_of_vtrace value.vtrace)]
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
  | Fun (arg_label, e_opt, pat, body, _)     -> Exp.to_string (Exp.fun_ arg_label e_opt pat body)
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


let html_of_values_for_loc (trace : Trace.t) assert_results type_env visualizers loc =
  div
    ~attrs:[ ("data-loc", Serialize.string_of_loc loc) ] (* View root for visualizers, also for determining where to place new asserts before *)
    begin
      trace
      |> Trace.entries_for_loc loc
      |> List.sort_by (fun (_, frame_no, _, _) -> frame_no)
      |> List.map begin fun (_, frame_no, value, env) ->
        span ~attrs:[("class","root-value-holder"); ("data-frame-no", string_of_int frame_no)] [html_of_value assert_results visualizers env type_env value]
      end
    end

let html_of_values_for_exp trace assert_results type_lookups exp =
  let type_env = type_lookups.Typing.lookup_exp exp.pexp_loc |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs exp.pexp_attributes in
  html_of_values_for_loc trace assert_results type_env visualizers exp.pexp_loc

let html_of_values_for_pat trace assert_results type_lookups pat =
  let type_env = type_lookups.Typing.lookup_pat pat.ppat_loc |>& (fun tpat -> tpat.Typedtree.pat_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs pat.ppat_attributes in
  html_of_values_for_loc trace assert_results type_env visualizers pat.ppat_loc

let rec terminal_exps exp = (* Dual of gather_vbs *)
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> terminal_exps e
  | Pexp_sequence (_, e2)    -> terminal_exps e2
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ terminal_exps
  | Pexp_letmodule (_, _, e) -> terminal_exps e
  | _                        -> [exp]

let rec gather_vbs exp = (* Dual of terminal_exp *)
  match exp.pexp_desc with
  | Pexp_let (_, vbs, e)     -> vbs @ gather_vbs e
  | Pexp_sequence (e1, e2)   -> [Vb.mk ~loc:e1.pexp_loc ~attrs:e1.pexp_attributes (Pat.unit) e1] @ gather_vbs e2 (* Need to put the loc/attrs on the vb so the view code that sets up position works. *)
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ gather_vbs
  | Pexp_letmodule (_, _, e) -> gather_vbs e
  | _                        -> []

let rec html_of_vb trace assert_results type_lookups vb =
  let show_pat    = not (Pat.is_unit vb.pvb_pat) in
  let show_output = show_pat && not (Exp.is_funlike vb.pvb_expr) in
  let exp_with_vbs_html = render_exp_ensure_vbs ~show_output trace assert_results type_lookups vb.pvb_expr in
  box ~loc:vb.pvb_loc ~parsetree_attrs:vb.pvb_attributes "vb" @@
    (if show_pat then [html_of_pat vb.pvb_pat] else []) @
    [exp_with_vbs_html](*  @
    (if show_results then [html_of_values_for_exp trace assert_results type_lookups (terminal_exp vb.pvb_expr)] else []) *)

and render_exp_ensure_vbs ?(show_output = true) trace assert_results type_lookups exp =
  let html_of_vb = html_of_vb trace assert_results type_lookups in
  let vbs = gather_vbs exp in
  let terminal_exps = terminal_exps exp in
  let show_vbs_box = vbs <> [] || not (Exp.is_fun exp) in
  let ret_exp_htmls   = terminal_exps |>@ (render_exp trace assert_results type_lookups) in
  let values_htmls () = terminal_exps |>@ (html_of_values_for_exp trace assert_results type_lookups) in
  div begin
    (if show_vbs_box then [div ~attrs:[("class", "vbs"); loc_attr exp.pexp_loc] (vbs |>@ html_of_vb)] else []) @
    [table ~attrs:[("class", "returns")] begin
      [ tr (ret_exp_htmls |>@ fun exp_html    -> td [exp_html]) ] @
      (if show_output then [tr (values_htmls () |>@ fun values_html -> td [values_html])] else [])
    end]
  end

and render_exp trace assert_results type_lookups exp =
  match exp.pexp_desc with
  (* | Pexp_apply (fexp, labeled_args) -> *)
  | Pexp_fun _ ->
    let rec get_param_rows_and_body exp =
      match exp.pexp_desc with
      | Pexp_fun (label, default_opt, pat, body) ->
        let later_rows, final_body = get_param_rows_and_body body in
        let default_exp_str = default_opt |>& (fun default_exp -> " = " ^ html_of_exp ~type_lookups default_exp) ||& "" in
        let row =
          tr
            [ td ~attrs:[("class", "pat_label")] [string_of_arg_label label ^ html_of_pat pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
            ; td [html_of_values_for_pat trace assert_results type_lookups pat]
            ]
        in
        (row::later_rows, final_body)
      | _ -> ([], exp)
    in
    let param_rows, body = get_param_rows_and_body exp in
    div ~attrs:[("class", "fun")]
      [ table param_rows
      ; render_exp_ensure_vbs trace assert_results type_lookups body
      ]
  | _ ->
    div ~attrs:[("class", "exp_label")] [html_of_exp ~type_lookups exp]

let html_of_structure_item trace assert_results type_lookups (item : structure_item) =
  match item.pstr_desc with
  | Pstr_eval (_exp, _)         -> failwith "can't handle Pstr_eval" (* JS wants all top-level DOM nodes to be vbs, for now at least *)
  | Pstr_value (_rec_flag, vbs) -> String.concat "" (List.map (html_of_vb trace assert_results type_lookups) vbs)
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
  let ctors_folder {Types.cstr_res; _} out =
    if Type.is_exn_type cstr_res then out else (* Exclude exceptions. *)
    if List.exists (Type.equal_ignoring_id_and_scope cstr_res) out then out else cstr_res::out
  in
  let ctors_types = Env.fold_constructors ctors_folder None(* not looking in a nested module *) tenv [] in
  span
    ~attrs:[("class", "tools")]
    begin
      ctors_types
      |> List.sort_by Type.to_string
      |>@ begin fun typ ->
        let tools =
          Example_gen.examples 12 tenv typ
          |>@ begin fun (example_exp, _) ->
            let code = Exp.to_string example_exp in
            span ~attrs:[("class", "tool"); ("data-insert-code", code)] [code]
          end
        in
        span ~attrs:[("class", "tool")] [Type.to_string typ ^ " ▾"; span ~attrs:[("class", "tools")] tools]
      end
    end


let html_str (structure_items : structure) (trace : Trace.t) (assert_results : Data.assert_result list) type_lookups final_tenv =
  let top_level_vbs_loc = structure_items |> List.last_opt |>& StructItem.loc ||& Location.none in
  html
    [ head
      [ title "Maniposynth"
      ; meta [("charset", "UTF-8")]
      ; stylesheet "/assets/maniposynth.css"
      ; script ~src:"/assets/maniposynth.js" ""
      ; script ~src:"/assets/reload_on_file_changes.js" ""
      ]
    ; body @@
      [ nav @@
        [ img ~attrs:[("src", "/assets/maniposynth.svg")]
        ; span ~attrs:[("class","undo tool")] ["Undo"]
        ; span ~attrs:[("class","redo tool")] ["Redo"]
        ] @ [drawing_tools final_tenv]
      ; div ~attrs:[("class", "top-level vbs"); loc_attr top_level_vbs_loc] @@
        List.map (html_of_structure_item trace assert_results type_lookups) structure_items
      ; div ~attrs:[("id", "inspector")]
        [ h2 ["Type"]
        ; div ~attrs:[("id", "type-of-selected")] []
        ; div ~attrs:[("id", "suggestions-pane")]
          [ h2 ["Suggestions"]
          ; div ~attrs:[("id", "suggestions-for-selected")] []
          ]
        ; div ~attrs:[("id", "vis-pane")]
          [ h2 ["Visualize"]
          ; div ~attrs:[("id", "vises-for-selected")] []
          ; div ["Custom: "; textbox ~attrs:[("id", "add-vis-textbox")] []]
          ]
        ]
      ; button ~attrs:[("id", "synth-button")] ["Synth"]
      ]
    ]
