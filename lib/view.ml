open Parsetree
open Camlboot_interpreter
open Vis
open Shared
open Shared.Ast
open Shared.Util

type stuff =
  { trace          : Trace.t
  ; prog           : program
  ; assert_results : Data.assert_result list
  ; type_lookups   : Typing.lookups
  ; names_in_prog  : string list
  }

let empty_stuff =
  { trace          = Trace.empty
  ; prog           = []
  ; assert_results = []
  ; type_lookups   = Typing.empty_lookups
  ; names_in_prog  = []
  }

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
let label ?(attrs = [])         inners = tag "label" ~attrs inners
let textbox ?(attrs = [])       inners = tag "input" ~attrs:(attrs @ [("type","text")]) inners
let fancyTextbox ?(attrs = [])  inners = tag "div" ~attrs:(attrs @ [("class","textbox");("contenteditable","true")]) inners
let checkbox ?(attrs = [])      ()     = tag "input" ~attrs:(attrs @ [("type","checkbox")]) []
let box     ?(attrs = []) ~loc ~parsetree_attrs klass inners =
  let perhaps_pos_attr =
    match Pos.from_attrs parsetree_attrs with
    | Some { x; y } -> [("data-left", string_of_int x); ("data-top", string_of_int y)]
    | None          -> []
  in
  let attrs = ("class", ("box " ^ klass)) :: loc_attr loc:: perhaps_pos_attr @ attrs in
  div ~attrs inners

let html_of_pat ?(attrs = []) stuff pat =
  let code = Pat.to_string { pat with ppat_attributes = [] } in (* Don't show vis attrs. *)
  let perhaps_type_attr = stuff.type_lookups.lookup_pat pat.ppat_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.pat_type)]) ||& [] in
  let perhaps_extraction_attr = if Pat.is_single_name pat then [("data-extraction-code", code)] else [] in
  span ~attrs:(attrs @ [("data-in-place-edit-loc", Serialize.string_of_loc pat.ppat_loc);("class","pat")] @ perhaps_type_attr @ perhaps_extraction_attr)
    [code]

let string_of_arg_label =
  let open Asttypes in function
  | Nolabel        -> ""
  | Labelled label -> "~" ^ label ^ ":"
  | Optional label -> "?" ^ label ^ ":"

(* "(+)" -> "+" *)
let uninfix =  String.drop_prefix "(" %> String.drop_suffix ")"

let exp_in_place_edit_attrs ?(infix = false) exp =
  let code = Exp.to_string { exp with pexp_attributes = [] } in (* Don't show pos/vis attrs. *)
  let code' = if infix then uninfix code else code in   (* Remove parens around ops rendered infix. *)
  [ ("data-in-place-edit-loc", Serialize.string_of_loc exp.pexp_loc)
  ; ("data-in-place-edit-code", code')
  ]

let exp_gunk ?(infix = false) stuff exp =
  let code = Exp.to_string { exp with pexp_attributes = [] } in (* Don't show pos/vis attrs. *)
  let code' = if infix then uninfix code else code in (* Remove parens around ops rendered infix. *)
  let perhaps_type_attr = stuff.type_lookups.lookup_exp exp.pexp_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.exp_type)]) ||& [] in
  let attrs =
    exp_in_place_edit_attrs ~infix exp @
    [ ("data-extraction-code", code)
    ] @ perhaps_type_attr
  in
  (code', attrs)


let rec apply_visualizers (prog : program) assert_results visualizers env type_env value_extraction_exp_opt (value : Data.value) =
  if visualizers = [] then "" else
  let html_of_value ?code_to_assert_on extraction_exp_opt value = html_of_value ~single_line_only:true ~code_to_assert_on { empty_stuff with prog = prog } (-1) [] Envir.empty_env Env.empty extraction_exp_opt value in
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
              Eval.eval_expr_with_fuel_or_bomb 1000 Loc_map.empty Primitives.prims env (fun _ -> None) Trace.new_trace_state 0 exp_to_run
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
              Eval.eval_expr_with_fuel_or_bomb 1000 Loc_map.empty Primitives.prims env (fun _ -> None) Trace.new_trace_state 0 exp_to_run
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
                [html_of_value None expected]
            end in
          let code_to_assert_on = Exp.apply exp [(Nolabel, exp_of_value value)] |> Exp.to_string in
          let extraction_exp_opt = value_extraction_exp_opt |>& (fun e -> Exp.apply exp [(Asttypes.Nolabel, e)]) in
          [ span ~attrs:[("class", "derived-vis-value")] @@
              assert_results @
              [wrap @@ html_of_value ~code_to_assert_on extraction_exp_opt result_value]
          ]
        end else
          []
      | _ ->
        []
    end
  in
  span ~attrs:[("class", "derived-vis-values")] result_htmls

and html_of_value ?(code_to_assert_on = None) ?(in_list = false) ~single_line_only (stuff : stuff) frame_no visualizers env type_env (extraction_exp_opt : expression option) ({ v_ = value_; _} as value : Data.value) =
  let recurse ?(in_list = false) = html_of_value ~single_line_only ~in_list stuff frame_no visualizers env type_env in
  let open Data in
  let active_vises = visualizers |>@ Vis.to_string in
  let possible_vises =
    match value.type_opt with
    | Some val_typ -> Suggestions.possible_function_names_on_type val_typ type_env
    | None -> [] in
  let perhaps_type_attr         = match value.type_opt    with Some typ               -> [("data-type", Type.to_string typ)]  | _ -> [] in
  let perhaps_code_to_assert_on = match code_to_assert_on with Some code_to_assert_on -> [("data-code-to-assert-on", code_to_assert_on)] | _ -> [] in
  let extraction_code = extraction_exp_opt |>& Exp.to_string ||& "" in
  let perhaps_edit_code_attrs =
    value.vtrace
    |> List.rev
    |> List.findmap_opt begin function
      | ((_, loc), (Use | Ret | Intro)) -> Exp.find_opt loc stuff.prog
      | _                               -> None
    end
    |>& exp_in_place_edit_attrs ||& []
  in
  let wrap_value str =
    let perhaps_extraction_code =
      extraction_exp_opt |>& begin fun _ ->
        ("data-extraction-code", extraction_code)
      end |> Option.to_list
    in
    span
      ~attrs:(
        [("data-active-vises", String.concat "  " active_vises)] @
        [("data-possible-vises", String.concat "  " possible_vises)] @
        perhaps_edit_code_attrs @
        perhaps_extraction_code @
        perhaps_type_attr @
        perhaps_code_to_assert_on @
        [("class", "value"); ("data-value-id", string_of_int value.id); ("data-vtrace", Serialize.string_of_vtrace value.vtrace)]
      )
      [str]
  in
  let tuple_or_array_children ?(in_list = false) vs =
    extraction_exp_opt |>& begin fun extraction_exp ->
      let prior_extraction_names = (Exp.everything extraction_exp).pats |>@& Pat.name in
      let child_pat_names =
        vs
        |> List.fold_left begin fun names v ->
          let name = Name.gen_ ~avoid:(names @ prior_extraction_names @ stuff.names_in_prog) ~base_name:(Name.base_name_from_val ~type_env v) in
          names @ [name]
        end []
      in
      let pat = Pat.tuple (child_pat_names |>@ Pat.var) in
      let children =
        List.combine child_pat_names vs |> List.mapi begin fun i (name, v) ->
          recurse ~in_list:(in_list && i = 1 (* tail position *)) (Some (Exp.match_ extraction_exp [Exp.case pat (Exp.var name)])) v
        end
      in
      children
    end
    ||&~ (fun () -> vs |> List.mapi (fun i v -> recurse ~in_list:(i = 1 && in_list (* tail position *)) None v))
  in
  let extracted_subvalue_names =
    let rec is_descendent candidate_vtrace ancestor_vtrace =
      candidate_vtrace == ancestor_vtrace ||
      match candidate_vtrace with
      | _::rest -> is_descendent rest ancestor_vtrace
      | []      -> false
    in
    Trace.entries_in_frame frame_no stuff.trace
    |>@ Trace.Entry.value
    |>@? (fun { v_; _ }     -> v_ == value_)
    |>@? (fun { vtrace; _ } -> is_descendent vtrace value.vtrace)
    |>@@ (fun { vtrace; _ } -> match vtrace with ((_, loc), PatMatch _)::_ -> [loc] | _ -> [] )
    |>@& (fun loc -> Pat.find_opt loc stuff.prog)
    |>@? (Pat.name %>& ((<>) extraction_code) %||& false) (* A name pat but not trival. If = extraction_code that means we're at the root of pat that's likely labeled elsewhere. *)
    |>@  html_of_pat ~attrs:[("class","subvalue-name pat")] stuff
    |> String.concat ""
  in
  wrap_value @@
  table ~attrs:[("class","subvalue-annotations")]
    [ tr [td [apply_visualizers stuff.prog stuff.assert_results visualizers env type_env extraction_exp_opt value]]
    ; tr [td [extracted_subvalue_names]]
    ] ^
  match value_ with
  | Bomb                                     -> "💣"
  | Hole _                                   -> "??"
  | Int int                                  -> string_of_int int
  | Int32 int32                              -> Int32.to_string int32
  | Int64 int64                              -> Int64.to_string int64
  | Nativeint nativeint                      -> Nativeint.to_string nativeint
  | Fun _ | Function _ ->
    value.vtrace
    |> List.rev
    |> List.findmap_opt begin function
      | ((_, loc), Use)              -> Exp.find_opt loc stuff.prog |>& Exp.to_string
      | ((_, loc), PatMatch (_, [])) -> Pat.find_opt loc stuff.prog |>& Pat.to_string
      | _                            -> None
    end
    ||&~ begin fun _ ->
      match value_ with
      | Fun (arg_label, e_opt, pat, body, _)     -> Exp.to_string (Exp.fun_ arg_label e_opt pat body)
      | Function (_, _)                          -> "func"
      | _                                        -> failwith "impossible"
    end
  | String bytes                             -> Exp.to_string (Exp.string_lit (Bytes.to_string bytes)) (* Make sure string is quoted & escaped *)
  | Float float                              -> string_of_float float
  | Tuple vs                                 ->
    begin match (tuple_or_array_children ~in_list vs, in_list) with
    | ([head; tail], true) -> head ^ tail
    | (children, _)        -> "(" ^ String.concat ", " children ^ ")"
    end
  | Constructor ("[]", _, None)          -> if in_list then "]" else "[]"
  | Constructor (ctor_name, _, None)     -> ctor_name
  | Constructor (ctor_name, _, Some arg) ->
    let ctor_name_to_show = if ctor_name = "::" then (if in_list then "; " else "[") else ctor_name ^ " " in
    extraction_exp_opt |>&& begin fun extraction_exp ->
      let prior_extraction_names = (Exp.everything extraction_exp).pats |>@& Pat.name in
      Case_gen.gen_ctor_cases_from_ctor_name ~avoid_names:(prior_extraction_names @ stuff.names_in_prog) ctor_name type_env
      |> List.findmap_opt begin fun case ->
        match case.pc_lhs.ppat_desc with
        | Ppat_construct ({ txt = Longident.Lident pat_ctor_name; _}, Some arg_pat) when pat_ctor_name = ctor_name ->
          Some (case.pc_lhs, arg_pat)
        | _ -> None
      end
      |>& begin fun (pat, arg_pat) ->
        match (arg_pat.ppat_desc, arg.v_) with
        (* Multi arg ctor *)
        | Ppat_tuple arg_pats, Tuple vs ->
          let arg_children =
            List.combine arg_pats vs |> List.mapi begin fun i (arg_pat, v)->
              Pat.single_name arg_pat
              |>& begin fun name ->
                (v, recurse ~in_list:(ctor_name = "::" && i = 1 (* tail position *)) (Some (Exp.match_ extraction_exp [Exp.case pat (Exp.var name)])) v)
              end
              ||&~ (fun () -> (v, recurse ~in_list:(ctor_name = "::") None v))
            end
          in
          let _, children_htmls = List.split arg_children in
          if ctor_name = "::"
          then ctor_name_to_show ^ String.concat "" children_htmls
          else
            begin match value.type_opt with
            | Some typ when not single_line_only ->
              let (same_type_children, other_children) = arg_children |> List.partition (fun ({ Data.type_opt; _ }, _) -> type_opt |>& Type.equal_ignoring_id_and_scope typ ||& false) in
              let _, same_type_children_htmls = List.split same_type_children in
              let _, other_children_htmls     = List.split other_children in
              if List.length same_type_children >= 2 then
                span ~attrs:[("class","tree-node")] [ctor_name_to_show ^ String.concat " " other_children_htmls] ^
                table ~attrs:[("class","tree-kids")]
                  [ tr (same_type_children_htmls |>@ fun child_html -> td [child_html]) ]
              else
                ctor_name_to_show ^ "(" ^ String.concat ", " children_htmls ^ ")"
            | _ ->
              ctor_name_to_show ^ "(" ^ String.concat ", " children_htmls ^ ")"
            end
        (* Single arg ctor, should also be a var with our current case generator *)
        | Ppat_var { txt = name; _ }, _ ->
          ctor_name_to_show ^ recurse ~in_list:(ctor_name = "::") (Some (Exp.match_ extraction_exp [Exp.case pat (Exp.var name)])) arg
        | _ ->
          failwith "a;lsdkvoabviavwassvd why oh why"
      end
    end
    ||&~ (fun () -> ctor_name_to_show ^ recurse ~in_list:(ctor_name = "::") None arg)
  | Prim _                                   -> "prim"
  | Fexpr _                                  -> "fexpr"
  | ModVal _                                 -> "modval"
  | InChannel _                              -> "inchannel"
  | OutChannel _                             -> "outchannel"
  | Record entry_map                         ->
    entry_map
    |> SMap.bindings
    |> List.map begin fun (field_name, value_ref) ->
      let field_extraction_exp_opt =
        extraction_exp_opt |>& begin fun extraction_exp ->
          let prior_extraction_names = (Exp.everything extraction_exp).pats |>@& Pat.name in
          let name = Name.gen_ ~avoid:(prior_extraction_names @ stuff.names_in_prog) ~base_name:field_name in
          Exp.match_ extraction_exp [Exp.case (Pat.record [(Longident.lident field_name, Pat.var name)] Asttypes.Open) (Exp.var name)]
        end
      in
      field_name ^ " = " ^ recurse field_extraction_exp_opt !value_ref
    end
    |> String.concat "; "
    |> (fun entries_str -> "{ " ^ entries_str ^ " }")
  | Lz _                                     -> "lazy"
  | Array values_arr                         -> "[! " ^ String.concat "; " (tuple_or_array_children @@ Array.to_list values_arr) ^ " !]"
  | Fun_with_extra_args (_, _, _)            -> "funwithextraargs"
  | Object _                                 -> "object"
  | ExCall _                                 -> "ExCall ShouldntSeeThis"
  | ExDontCare                               -> "ExDontCare ShouldntSeeThis"


let value_htmls_for_loc ~single_line_only stuff type_env root_exp_opt visualizers loc =
  let entries = stuff.trace |> Trace.entries_for_loc loc |> List.sort_by (fun (_, frame_no, _, _) -> frame_no) in
  let html_of_entry (_, frame_no, value, env) =
    span
      (* data-loc is view root for visualizers, also for determining where to place new asserts before. *)
      ~attrs:[("class","root-value-holder"); ("data-loc", Serialize.string_of_loc loc); ("data-frame-no", string_of_int frame_no)]
      [html_of_value ~single_line_only stuff frame_no visualizers env type_env root_exp_opt value]
  in
  let max_shown = 7 in (* Should be odd. *)
  if List.length entries >= max_shown then
    (List.prefix (max_shown/2) entries |>@ html_of_entry) @
    [span ~attrs:[("class","ellipses")] ["..." ^ string_of_int (List.length entries - 2*(max_shown/2)) ^ " more..."]] @
    (List.suffix (max_shown/2) entries |>@ html_of_entry)
  else
    entries |>@ html_of_entry

(* This is a separate function because the table view for function params needs the value htmls separately *)
let html_of_values_for_loc ~single_line_only stuff type_env root_exp_opt visualizers loc =
  let inners = value_htmls_for_loc ~single_line_only stuff type_env root_exp_opt visualizers loc in
  div ~attrs:[("class","values")] inners

let html_of_values_for_exp ?(single_line_only = false) stuff vb_pat_opt exp =
  let type_env = stuff.type_lookups.Typing.lookup_exp exp.pexp_loc |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs exp.pexp_attributes in
  (* If this is a return that's bound to a vb pat, use that pat var as the extraction root rather than the exp. *)
  let root_exp = vb_pat_opt |>&& Pat.single_name |>& Exp.var ||& exp in
  html_of_values_for_loc ~single_line_only stuff type_env (Some root_exp) visualizers exp.pexp_loc

let value_htmls_for_pat ?(single_line_only = false) stuff pat =
  let type_env = stuff.type_lookups.Typing.lookup_pat pat.ppat_loc |>& (fun tpat -> tpat.Typedtree.pat_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs pat.ppat_attributes in
  let root_exp_opt = Pat.single_name pat |>& Exp.var in
  value_htmls_for_loc ~single_line_only stuff type_env root_exp_opt visualizers pat.ppat_loc


type parens_context = NoParens | NormalArg | NextToInfixOp

(* For exp labels *)
let rec html_of_exp ?(tv_root_exp = false) ?(show_result = true) ?(infix = false) ?(parens_context = NoParens) ?(in_list = false) (stuff : stuff) exp =
  let recurse ?(show_result = true) ?(infix = false) ?(parens_context = NoParens) ?(in_list = false) = html_of_exp ~show_result ~infix ~parens_context ~in_list stuff in
  let (code', attrs) = exp_gunk ~infix stuff exp in
  let wrap inner =
    let needs_parens =
      parens_context != NoParens &&
      match exp.pexp_desc with
      | Pexp_tuple _ -> false
      | Pexp_array _ -> false
      | Pexp_construct ({ txt = Longident.Lident "[]"; _ }, _) -> false
      | Pexp_construct ({ txt = Longident.Lident "::"; _ }, _) -> not @@ String.starts_with "[" code' && String.ends_with "]" code'
      | _ ->
        let has_infix_app () = Exp.flatten exp |>@& Exp.fexp_of_apply |>@& Exp.simple_name |> List.exists Name.is_infix in
        begin match parens_context with
        | NoParens      -> false
        | NormalArg     -> String.includes " " code'
        | NextToInfixOp -> has_infix_app ()
        end
    in
    span ~attrs:([("class","exp")] @ attrs) [if needs_parens then "(" ^ inner ^ ")" else inner]
  in
  (if show_result && not tv_root_exp && Bindings.free_unqualified_names exp <> [] then html_of_values_for_exp ~single_line_only:true stuff None exp else "") ^
  wrap @@
  match exp.pexp_desc with
  | Pexp_apply (fexp, labeled_args) ->
    let html_of_labeled_arg ~parens_context (label, arg) =
      let label_str, parens_context =
        let open Asttypes in
        match label with Nolabel -> ("", parens_context) | Labelled str -> ("~" ^ str, NormalArg) | Optional str -> ("?" ^ str, NormalArg)
      in
      label_str ^ recurse ~parens_context arg
    in
    let is_infix = fexp |> Exp.simple_name |>& Name.is_infix ||& false in
    (* When fexp is a variable, don't render an exp for the fexp, let the fexp represent the whole call *)
    begin match is_infix, labeled_args with
    | true, [la1; la2] -> html_of_labeled_arg ~parens_context:NextToInfixOp la1 ^ (if Exp.is_ident fexp then uninfix (Exp.to_string fexp) ^ " " else recurse ~show_result:false ~infix:true ~parens_context:NormalArg fexp) ^ html_of_labeled_arg ~parens_context:NextToInfixOp la2
    | _                -> (if Exp.is_ident fexp then Exp.to_string fexp ^ " " else recurse ~parens_context:NormalArg ~show_result:false fexp) ^ (labeled_args |>@ html_of_labeled_arg ~parens_context:NormalArg |> String.concat " ")
    end
  | Pexp_construct ({ txt = Longident.Lident "[]"; _ }, None) -> if in_list then "]" else "[]"
  | Pexp_construct ({ txt = Longident.Lident "::"; _ }, Some { pexp_desc = Pexp_tuple [head; tail]; _}) ->
    if String.starts_with "[" code' && String.ends_with "]" code' then (* Have to make sure this list is suitable to render sugared *)
      (if in_list then "; " else "[ ") ^ recurse head ^ recurse ~in_list:true tail
    else
      (* Render infix *)
      recurse ~parens_context:NextToInfixOp head ^ " :: " ^ recurse ~parens_context:NextToInfixOp tail
  | Pexp_construct ({ txt = lid; _ }, Some arg) ->
    Longident.to_string lid ^ " " ^ recurse ~parens_context:NormalArg arg
  | Pexp_tuple exps ->
    "(" ^ String.concat ", " (exps |>@ recurse) ^ ")"
  | Pexp_ifthenelse (e1, e2, e3_opt) ->
    "if " ^ recurse e1 ^ " then " ^ recurse e2 ^ (e3_opt |>& (fun e3 -> " else " ^ recurse e3) ||& "")
  | _ ->
    code' ^ " "


(* let rec terminal_exps exp = (* Dual of gather_vbs *)
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> terminal_exps e
  | Pexp_sequence (_, e2)    -> terminal_exps e2
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ terminal_exps
  | Pexp_letmodule (_, _, e) -> terminal_exps e
  | _                        -> [exp] *)

(* Gather list of (scrutinee, case pat, guard opt) for each terminal exp
let rec terminal_match_paths exp =
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> terminal_match_paths e
  | Pexp_sequence (_, e2)    -> terminal_match_paths e2
  | Pexp_letmodule (_, _, e) -> terminal_match_paths e
  | Pexp_match (scrutinee, cases) ->
    cases
    |>@@ begin fun {pc_lhs; pc_guard; pc_rhs } ->
      terminal_match_paths pc_rhs |>@ (fun path -> (scrutinee, pc_lhs, pc_guard)::path)
    end
  | _                        -> [[]] *)

let rec gather_vbs exp = (* Dual of ret_tree_html *)
  let tag_rec recflag vb = (recflag, vb) in
  match exp.pexp_desc with
  | Pexp_let (recflag, vbs, e) -> (vbs |>@ tag_rec recflag) @ gather_vbs e
  | Pexp_sequence (e1, e2)     -> [(Asttypes.Nonrecursive, Vb.mk ~loc:e1.pexp_loc ~attrs:e1.pexp_attributes (Pat.unit) e1)] @ gather_vbs e2 (* Need to put the loc/attrs on the vb so the view code that sets up position works. *)
  | Pexp_match (_, cases)      -> cases |>@ Case.rhs |>@@ gather_vbs
  | Pexp_letmodule (_, _, e)   -> gather_vbs e
  | _                          -> []

let should_show_vbs { pexp_desc; _ } =
  match pexp_desc with
  | Pexp_let _ | Pexp_sequence _ | Pexp_match _ | Pexp_letmodule _ -> true
  | _ -> false

let rec html_of_vb stuff recflag vb =
  let is_rec_perhaps_checked = if recflag = Asttypes.Recursive then [("checked","true")] else [] in
  let show_pat               = not (Pat.is_unit vb.pvb_pat) in
  let show_pat_on_top        = Exp.is_funlike vb.pvb_expr || should_show_vbs vb.pvb_expr in
  let show_output            = show_pat && not (Exp.is_funlike vb.pvb_expr) in
  let perhaps_type_attr      = stuff.type_lookups.lookup_exp vb.pvb_expr.pexp_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.exp_type)]) ||& [] in
  let attrs                  = [("data-in-place-edit-loc", Serialize.string_of_loc vb.pvb_loc); ("data-in-place-edit-code", Vb.to_string vb)] @ perhaps_type_attr in
  box ~loc:vb.pvb_loc ~parsetree_attrs:vb.pvb_attributes ~attrs "vb" @@
    (if show_pat && show_pat_on_top then [html_of_pat stuff vb.pvb_pat] else []) @
    (if show_pat && Exp.is_funlike vb.pvb_expr then [label ~attrs:[("class","is-rec")] [checkbox ~attrs:(is_rec_perhaps_checked @ [loc_attr vb.pvb_loc]) (); "rec"]] else []) @
    [render_tv ~show_output stuff (if show_pat then Some vb.pvb_pat else None) vb.pvb_expr] @
    (if show_pat && not show_pat_on_top then [html_of_pat stuff vb.pvb_pat] else [])

(* Shows value bindings *)
and local_canvas_vbs_and_returns_htmls stuff exp =
  let html_of_vb (recflag, vb) = html_of_vb stuff recflag vb in
  let vbs = gather_vbs exp in
  (* let terminal_exps = terminal_exps exp in *)
  (* let ret_tv_path_descs = terminal_match_paths exps |>@ fun (_, pat, _) -> Pat.to_string pat in *)
  (* let ret_tv_htmls  = terminal_exps |>@ render_tv stuff None in *)
  [ div ~attrs:[("class", "vbs"); loc_attr exp.pexp_loc] (vbs |>@ html_of_vb)
  ; div ~attrs:[("class", "returns")] [ret_tree_html stuff exp]
  ]

and ret_tree_html stuff exp =
  let recurse = ret_tree_html stuff in
  match exp.pexp_desc with
  | Pexp_let (_, _, e)            -> recurse e
  | Pexp_sequence (_, e2)         -> recurse e2
  | Pexp_letmodule (_, _, e)      -> recurse e
  | Pexp_match (scrutinee, cases) ->
    let (_, attrs) = exp_gunk stuff exp in
    let html_of_case case =
      span ~attrs:[("class","case")] [html_of_pat stuff case.pc_lhs; recurse case.pc_rhs]
    in
    div ~attrs:[("class","match")]
      [ div ~attrs:(attrs @ [("class","scrutinee")]) ["⇠ "; html_of_exp ~show_result:false stuff scrutinee; " ⇢"]
      ; div ~attrs:[("class","cases")] (cases |>@ html_of_case)
      ]
  | _ -> div ~attrs:[("class", "return")] [render_tv stuff None exp]


(* Actually renders all values, but only one is displayed at a time (via Javascript). *)
and render_tv ?(show_output = true) stuff vb_pat_opt exp =
  let _ = show_output in
  match exp.pexp_desc with
  | Pexp_fun _ ->
    let rec get_param_rows_and_body exp =
      match exp.pexp_desc with
      | Pexp_fun (label, default_opt, pat, body) ->
        let later_rows, final_body = get_param_rows_and_body body in
        let default_exp_str = default_opt |>& (fun default_exp -> " = " ^ html_of_exp stuff default_exp) ||& "" in
        let row =
          tr ~attrs:[("class", "pat fun-param")] @@
            [ td ~attrs:[("class", "pat_label")] [string_of_arg_label label ^ html_of_pat stuff pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
            ] @ (value_htmls_for_pat stuff pat |>@ List.singleton |>@ td)
        in
        (row::later_rows, final_body)
      | _ -> ([], exp)
    in
    let param_rows, body = get_param_rows_and_body exp in
    (* Technically, a function is value and one can argue the above code should be in html_of_values_for_exp *)
    (* Don't remember why I double wrapped this. But when I do, hovering over a top level value causes other top level functions to gray out because there's no child element that has the same frameNo as the top level. So let's try not double wrapping and see what happens... *)
    (* div ~attrs:[("class", "tv")] [ *)
      div ~attrs:[("class", "fun exp tv")] begin
        [ table param_rows ] @
        local_canvas_vbs_and_returns_htmls stuff body
      end
    (* ] *)
  | Pexp_assert e ->
    let matching_asserts =
      begin match Eval.parse_assert e with
      | Some (lhs, _fexp, _argexp, expected) ->
        stuff.assert_results
        |>@? (fun Data.{ lhs_exp; expected_exp; _ } -> (lhs_exp, expected_exp) = (lhs, expected))
      | None -> []
      end
    in
    (* print_endline @@ string_of_int (List.length assert_results); *)
    let all_passed = List.for_all (fun Data.{ passed; _ } -> passed) matching_asserts in
    let any_failures = List.exists (fun Data.{ passed; _ } -> not passed) matching_asserts in
    let pass_fail_class, pass_fail_icon =
      if any_failures then (" failing", "✘")
      else if all_passed && matching_asserts <> [] then (" passing", "✔︎")
      else ("", "")
    in
    div ~attrs:[("class", "exp_label exp" ^ pass_fail_class)] [pass_fail_icon; " "; html_of_exp ~tv_root_exp:true stuff e]
  | _ ->
    div ~attrs:[("class", "tv")] begin
      if should_show_vbs exp then
        local_canvas_vbs_and_returns_htmls stuff exp
      else
        [ div ~attrs:[("class", "exp_label exp")] [html_of_exp ~tv_root_exp:true stuff exp]
        ; html_of_values_for_exp stuff vb_pat_opt exp
        ]
    end

let html_of_top_matter_structure_item (item : structure_item) =
  match item.pstr_desc with
  | Pstr_eval (_exp, _)   -> failwith "can't handle Pstr_eval" (* JS wants all top-level DOM nodes to be vbs, for now at least *)
  | Pstr_value (_, _)     -> ""
  | Pstr_primitive _      -> failwith "can't handle Pstr_primitive"
  | Pstr_type (_, _)      -> div ~attrs:[("class", "type-def");("data-in-place-edit-loc", Serialize.string_of_loc item.pstr_loc)] [StructItem.to_string item]
  | Pstr_typext _         -> failwith "can't handle Pstr_typext"
  | Pstr_exception _      -> failwith "can't handle Pstr_exception"
  | Pstr_module _         -> failwith "can't handle Pstr_module"
  | Pstr_recmodule _      -> failwith "can't handle Pstr_recmodule"
  | Pstr_modtype _        -> failwith "can't handle Pstr_modtype"
  | Pstr_open _           -> failwith "can't handle Pstr_open"
  | Pstr_class _          -> failwith "can't handle Pstr_class"
  | Pstr_class_type _     -> failwith "can't handle Pstr_class_type"
  | Pstr_include _        -> failwith "can't handle Pstr_include"
  | Pstr_attribute _      -> failwith "can't handle Pstr_attribute"
  | Pstr_extension (_, _) -> failwith "can't handle Pstr_extension"

let html_of_vb_structure_item stuff (item : structure_item) =
  match item.pstr_desc with
  | Pstr_eval (_exp, _)       -> failwith "can't handle Pstr_eval" (* JS wants all top-level DOM nodes to be vbs, for now at least *)
  | Pstr_value (recflag, vbs) -> String.concat "" (List.map (html_of_vb stuff recflag) vbs)
  | Pstr_primitive _          -> failwith "can't handle Pstr_primitive"
  | Pstr_type (_, _)          -> "" (* failwith "can't handle Pstr_type" *)
  | Pstr_typext _             -> failwith "can't handle Pstr_typext"
  | Pstr_exception _          -> failwith "can't handle Pstr_exception"
  | Pstr_module _             -> failwith "can't handle Pstr_module"
  | Pstr_recmodule _          -> failwith "can't handle Pstr_recmodule"
  | Pstr_modtype _            -> failwith "can't handle Pstr_modtype"
  | Pstr_open _               -> failwith "can't handle Pstr_open"
  | Pstr_class _              -> failwith "can't handle Pstr_class"
  | Pstr_class_type _         -> failwith "can't handle Pstr_class_type"
  | Pstr_include _            -> failwith "can't handle Pstr_include"
  | Pstr_attribute _          -> failwith "can't handle Pstr_attribute"
  | Pstr_extension (_, _)     -> failwith "can't handle Pstr_extension"


let inital_env_ctor_types = Suggestions.ctors_types Typing.initial_env
let drawing_tools tenv prog =
  let ctors_types = Suggestions.ctors_types tenv in
  let tool_and_menu tool_key codes =
    if codes = [] then [] else
    let codes = List.dedup codes in
    let tools =
      codes |>@ begin fun code ->
        span ~attrs:[("class", "tool"); ("data-extraction-code", code)] [code]
      end
    in
    let first_code = List.hd codes in
    [ span ~attrs:[("class", "tool left-of-menu"); ("data-extraction-code", first_code); ("data-tool-key", tool_key)] [first_code]
    ; span ~attrs:[("class", "tool tool-menu")] [" ▾"; span ~attrs:[("class", "tools")] tools]
    ]
  in
  let common_phrases_menu =
    tool_and_menu "common phrases" Suggestions.common_suggestions
  in
  let prog_funcs_menu =
    tool_and_menu "prog functions" (Example_gen.func_calls tenv prog |>@ fst |>@ Exp.to_string)
  in
  let ctor_menus =
    ctors_types
    |> List.sort_by (fun typ -> (List.mem typ inital_env_ctor_types, Type.to_string typ))
    |>@@ begin fun typ ->
      (Example_gen.examples_with_holes tenv typ @ Example_gen.examples 12 tenv typ)
      |>@ fst
      |>@ Exp.to_string
      |> tool_and_menu (Type.to_string typ)
    end
  in
  span
    ~attrs:[("class", "tools")]
    (common_phrases_menu @ prog_funcs_menu @ ctor_menus)


let html_str (structure_items : structure) (trace : Trace.t) (assert_results : Data.assert_result list) type_lookups final_tenv =
  let names_in_prog = StructItems.deep_names structure_items in
  let stuff =
    { trace          = trace
    ; prog           = structure_items
    ; assert_results = assert_results
    ; type_lookups   = type_lookups
    ; names_in_prog  = names_in_prog
    }
  in
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
        ] @ [drawing_tools final_tenv structure_items]
      ; div ~attrs:[("class", "top-matter")] @@
        List.map html_of_top_matter_structure_item structure_items
      ; div ~attrs:[("class", "top-level vbs"); loc_attr top_level_vbs_loc] @@
        List.map (html_of_vb_structure_item stuff) structure_items
      ; div ~attrs:[("id", "inspector")]
        [ div ~attrs:[("id", "text-edit-pane")]
          [ div ~attrs:[("id", "text-edit-node-stuff")]
            [ label ~attrs:[("for","node-textbox");("id", "type-of-selected")] []
            ; fancyTextbox ~attrs:[("id", "node-textbox")] []
            ]
          ; span ~attrs:[("id", "text-edit-root-stuff")]
            [ label ~attrs:[("for","root-node-textbox")] ["Root"]
            ; fancyTextbox ~attrs:[("id", "root-node-textbox")] []
            ]
          ]
        ; div ~attrs:[("id", "assert-pane")]
          [ label ~attrs:[("for","assert-textbox")] ["Assert "; span ~attrs:[("id","assert-on")] []; " ="]
          ; textbox ~attrs:[("id", "assert-textbox")] []
          ]
        (* ; div ~attrs:[("id", "use-pane")]
          [ label ~attrs:[("for","use-textbox")] ["Use"]
          ; fancyTextbox ~attrs:[("id", "use-textbox")] []
          ; button ~attrs:[("id","add-button");("type","submit")] ["Add"]
          ; button ~attrs:[("id","visualize-button");("type","submit")] ["Visualize"]
          ] *)
        ; div ~attrs:[("id", "vis-pane")]
          [ label ~attrs:[("for","vis-textbox")] ["Overlay Visualization"]
          ; div ~attrs:[("id", "vis-list")] []
          ; fancyTextbox ~attrs:[("id", "vis-textbox")] []
          ; button ~attrs:[("id","visualize-button");("type","submit")] ["Visualize"]
          ]
        ]
      ; button ~attrs:[("id", "synth-button")] ["Synth"]
      ; div ~attrs:[("id", "tooltip")] []
      ]
    ]
