open Parsetree
open Camlboot_interpreter
open Vis
open Shared
open Shared.Ast
open Shared.Util

(* https://www.w3.org/International/questions/qa-escapes *)
let needs_escape = Str.regexp "[\"'&<>]"
let html_escape str =
  str |> Str.global_substitute needs_escape begin Str.matched_string %> function
  | "\"" -> "&quot;"
  | "'"  -> "&apos;"
  | "&"  -> "&amp;"
  | "<"  -> "&lt;"
  | ">"  -> "&gt;"
  | str  -> failwith @@ "html_escape: your regex is bad: " ^ str
  end

type stuff =
  { trace                                 : Trace.t
  ; prog                                  : program
  ; assert_results                        : Data.assert_result list
  ; type_lookups                          : Typing.lookups
  ; names_in_prog                         : string list
  ; type_errors                           : (Location.t * Env.t * Typecore.error) list
  ; final_env                             : Data.env
  ; possible_function_names_on_type_cache : (Types.type_expr * Env.t * string list) list ref
  }

let empty_stuff =
  { trace                                 = Trace.empty
  ; prog                                  = []
  ; assert_results                        = []
  ; type_lookups                          = Typing.empty_lookups
  ; names_in_prog                         = []
  ; type_errors                           = []
  ; final_env                             = Envir.empty_env
  ; possible_function_names_on_type_cache = ref []
  }

let sprintf = Printf.sprintf

let rec print_attrs attrs  =
  match attrs with
  | (name, value)::rest -> sprintf " %s=\"%s\"%s" name (html_escape value) (print_attrs rest)
  | []                  -> ""

let tag name ?(attrs = []) inners =
  sprintf "<%s%s>%s</%s>" name (print_attrs attrs) (String.concat "" inners) name

let lone_tag name ?(attrs = []) () =
  sprintf "<%s%s />" name (print_attrs attrs)

let html ?(attrs = []) inners = tag "html" ~attrs inners
let head ?(attrs = []) inners = tag "head" ~attrs inners

let title ?(attrs = []) str = tag "title" ~attrs [str]
let meta attrs = lone_tag "meta" ~attrs ()
let link attrs = lone_tag "link" ~attrs ()
let stylesheet href = link [("rel", "stylesheet"); ("href", href)]

let script ?src ?(attrs = []) str =
  match src with
  | Some src_str -> tag "script" ~attrs:(("src", src_str)::attrs) [str]
  | None         -> tag "script" ~attrs                                [str]

let loc_attr loc = ("data-loc", Serialize.string_of_loc loc)

let body    ?(attrs = [])       inners = tag "body" ~attrs inners
let nav     ?(attrs = [])       inners = tag "nav" ~attrs inners
let div     ?(attrs = [])       inners = tag "div" ~attrs inners
let p       ?(attrs = [])       inners = tag "p" ~attrs inners
let strong  ?(attrs = [])       inners = tag "strong" ~attrs inners
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
(* box is the movable wrapper that contains a TV and makes it positionable. (Return TVs do not have a box.) *)
let box ?(attrs = []) ~loc ~parsetree_attrs klass inners =
  let perhaps_pos_attr =
    match Pos.from_attrs parsetree_attrs with
    | Some { x; y } -> [("data-left", string_of_int x); ("data-top", string_of_int y)]
    | None          -> []
  in
  let attrs = ("class", ("box " ^ klass)) :: loc_attr loc:: perhaps_pos_attr @ attrs in
  div ~attrs inners

let hint str = span ~attrs:[("class","hint")] [str]

let type_error_htmls stuff loc =
  stuff.type_errors
  |>@? (Tup3.fst %> (=) loc)
  |>@ begin fun (_, tenv, err) ->
    span ~attrs:[("class","type-error")] [Typing.string_of_error tenv err]
  end

let html_of_pat ?(attrs = []) stuff pat =
  let code = Pat.to_string @@ Attrs.remove_all_deep_pat pat in (* Don't show vis/pos attrs. *)
  let pat_type_opt = stuff.type_lookups.lookup_pat pat.ppat_loc |>& (fun texp -> texp.Typedtree.pat_type) in
  let perhaps_type_attr = pat_type_opt |>& (fun pat_type -> [("data-type", Type.to_string pat_type)]) ||& [] in
  let perhaps_extraction_attr =
    if Pat.is_single_name pat then
      match pat_type_opt |>& Type.arrow_arg_count with
      | Some n when n >= 1 -> [("data-extraction-code", Exp.apply_with_hole_args (Exp.from_string code) n |> Exp.to_string)]
      | _                  -> [("data-extraction-code", code)]
    else
      []
  in
  let type_error_htmls = type_error_htmls stuff pat.ppat_loc in
  let perhaps_type_error_class = if type_error_htmls <> [] then " has-type-error" else "" in
  span
    ~attrs:(attrs @ [("data-edit-loc", Serialize.string_of_loc pat.ppat_loc);("class","pat" ^ perhaps_type_error_class)] @ perhaps_type_attr @ perhaps_extraction_attr)
    (type_error_htmls @ [code])

let string_of_arg_label =
  let open Asttypes in function
  | Nolabel        -> ""
  | Labelled label -> "~" ^ label ^ ":"
  | Optional label -> "?" ^ label ^ ":"

(* "(+)" -> "+" *)
let uninfix =  String.drop_prefix "(" %> String.drop_suffix ")"

let exp_in_place_edit_attrs ?(infix = false) exp =
  let code = Attrs.remove_all_deep_exp exp |> Exp.to_string in (* Don't show pos/vis attrs. *)
  let code' = if infix then uninfix code else code in   (* Remove parens around ops rendered infix. *)
  [ ("data-edit-loc", Serialize.string_of_loc exp.pexp_loc)
  ; ("data-edit-loc-start-byte", Loc.Pos.byte_in_file exp.pexp_loc.loc_start |> string_of_int)
  ; ("data-edit-code", code')
  ]

let exp_gunk ?(infix = false) stuff exp =
  let code = Attrs.remove_all_deep_exp exp |> Exp.to_string in (* Don't show pos/vis attrs. *)
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
  let html_of_value ?exp_to_assert_on ?is_expectation extraction_exp_opt value = html_of_value ?exp_to_assert_on ?is_expectation  ~single_line_only:true { empty_stuff with prog = prog } (-1) [] Envir.empty_env Env.empty [] extraction_exp_opt value in
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
              Eval.eval_expr_with_fuel_or_bomb 1000 Loc_map.empty Primitives.prims env (fun _ -> None) (Trace.new_trace_state ()) 0 exp_to_run
            end in
          let vis_assert_lhs = Exp.apply exp [(Nolabel, Assert_comparison.exp_of_value value)] in
          let matching_asserts =
            assert_results
            |>@? Assert_comparison.does_lhs_match env vis_assert_lhs
          in
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
              Eval.eval_expr_with_fuel_or_bomb 1000 Loc_map.empty Primitives.prims env (fun _ -> None) (Trace.new_trace_state ()) 0 exp_to_run
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
              span ~attrs:(exp_in_place_edit_attrs expected_exp)
                [html_of_value ~is_expectation:true None expected]
            end in
          let extraction_exp_opt = value_extraction_exp_opt |>& (fun e -> Exp.apply exp [(Asttypes.Nolabel, e)]) in
          [ span ~attrs:[("class", "derived-vis-value")] @@
              assert_results @
              [wrap @@ html_of_value ~exp_to_assert_on:vis_assert_lhs extraction_exp_opt result_value]
          ]
        end else
          []
      | _ ->
        []
    end
  in
  span ~attrs:[("class", "derived-vis-values")] result_htmls

and html_of_value ?exp_to_assert_on ?(in_list = false) ?(is_expectation = false) ~single_line_only (stuff : stuff) frame_no visualizers env type_env locs_editable_in_value (extraction_exp_opt : expression option) ({ v_ = value_; _} as value : Data.value) =
  (* if true then "" else *)
  let recurse ?(in_list = false) = html_of_value ~single_line_only ~in_list stuff frame_no visualizers env type_env locs_editable_in_value in
  let open Data in
  let active_vises = visualizers |>@ Vis.to_string in
  let possible_vises =
    (* if true then [] else *)
    match value.type_opt with
    | Some val_typ -> Suggestions.possible_function_names_on_type ~cache:stuff.possible_function_names_on_type_cache val_typ type_env
    | None -> [] in
  let perhaps_type_attr         = match value.type_opt   with Some typ              -> [("data-type", Type.to_string typ)]  | _ -> [] in
  let perhaps_code_to_assert_on = match exp_to_assert_on with Some exp_to_assert_on -> [("data-code-to-assert-on", Exp.to_string (exp_to_assert_on |> Attrs.remove_all_deep_exp))] | _ -> [] in
  (* let extraction_exp_opt = None in *)
  let extraction_code = extraction_exp_opt |>& Attrs.remove_all_deep_exp |>& Exp.to_string ||& "" in
  let perhaps_edit_code_attrs =
    (* if true then [] else *)
    value.vtrace
    |> List.rev
    |> List.findmap_opt begin function
      | ((_, loc), Intro) when List.mem loc locs_editable_in_value -> Exp.find_opt loc stuff.prog
      | _                                                          -> None
    end
    |>& exp_in_place_edit_attrs ||& []
  in
  let extracted_subvalue_pats =
    (* if true then [] else *)
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
  in
  let extracted_subvalue_names_html =
    extracted_subvalue_pats
    |>@ html_of_pat ~attrs:[("class","subvalue-name pat")] stuff
    |> String.concat ""
  in
  let ctor_destruction_pat_and_ctor_arg_pat_opt =
    (* if true then None else *)
    (* This is a promising place for optimization. *)
    match (value_, extraction_exp_opt) with
    | Constructor (ctor_name, _, _), Some extraction_exp ->
      let prior_extraction_names = (Exp.everything extraction_exp).pats |>@& Pat.name in
      Case_gen.gen_ctor_cases_from_ctor_name ~avoid_names:(prior_extraction_names @ stuff.names_in_prog) ctor_name type_env
      |> List.findmap_opt begin fun case ->
        match case.pc_lhs.ppat_desc with
        | Ppat_construct ({ txt = Longident.Lident pat_ctor_name; _}, arg_pat_opt) when pat_ctor_name = ctor_name ->
          Some (case.pc_lhs, arg_pat_opt)
        | _ -> None
      end
    | _ ->
      None
  in
  let matching_asserts =
    (* if true then [] else *)
    (* [] *)
    (* Envir.env_get_value_or_lvar *)
    exp_to_assert_on |>& begin fun exp_to_assert_on ->
      stuff.assert_results
      |>@? begin fun assert_result ->
        Assert_comparison.does_lhs_match env exp_to_assert_on assert_result
        || Assert_comparison.does_lhs_match stuff.final_env exp_to_assert_on assert_result
      end
    end ||& []
  in
  (* print_endline @@ string_of_int (List.length assert_results); *)
  let all_passed = List.for_all (fun Data.{ passed; _ } -> passed) matching_asserts in
  let any_failures = List.exists (fun Data.{ passed; _ } -> not passed) matching_asserts in
  let is_passing = all_passed && matching_asserts <> [] in
  let wrap_value str =
    let perhaps_extraction_code =
      extraction_exp_opt
      |>& begin fun extraction_exp ->
        (* Add hole args to a function value to make a call. *)
        let arg_count = (* By examing value. We won't always have value.type_opt (in the current implementation). *)
          let rec exp_arg_count exp =
            match exp.pexp_desc with
            | Pexp_fun (Asttypes.Nolabel, _, _, body) -> 1 + exp_arg_count body
            | Pexp_function _                         -> 1
            | _                                       -> 0
          in
          match value_ with
          | Fun (Asttypes.Nolabel, _, _, body, _) -> 1 + exp_arg_count body
          | Function (_, _)                       -> 1
          | _                                     ->
            begin match value.type_opt with
            | Some typ -> Type.arrow_arg_count typ
            | None     -> 0
            end
        in
        if arg_count >= 1
        then ("data-extraction-code", Exp.apply_with_hole_args extraction_exp arg_count |> Attrs.remove_all_deep_exp |> Exp.to_string)
        else ("data-extraction-code", extraction_code)
      end
      |> Option.to_list
    in
    let perhaps_destruction_code =
      let extracted_subvalue_names = extracted_subvalue_pats |>@& Pat.name in
      let scrutinee_name_opt =
        List.hd_opt @@
          (extraction_exp_opt |>&& Exp.simple_name |> Option.to_list)
          @ extracted_subvalue_names
      in
      match scrutinee_name_opt, ctor_destruction_pat_and_ctor_arg_pat_opt with
      | Some scrutinee_name, Some (case_pat, _) ->
        (* By only providing a single case, we signal Bindings.fixup which branch should get the existing code. *)
        (* Bindings.fixups will add missings cases with holes for branches. *)
        [("data-destruction-code", Exp.to_string @@ Exp.match_ (Exp.var scrutinee_name) [Exp.case case_pat Exp.hole])]
      | _ ->
        []
    in
    let value_class =
      match value_ with
      | Bomb          -> "bomb"
      | Hole _        -> "hole"
      | String _      -> "string"
      | Tuple _       -> "tuple"
      | Record _      -> "record"
      | Constructor _ -> "ctor"
      | Array _       -> "array"
      | Float _       -> "float number"
      | Int _         -> "int number" | Int32 _ -> "int32 number" | Int64 _ -> "int64 number" | Nativeint _ -> "nativeint number"
      | Fun _ | Function _ | Fun_with_extra_args (_, _, _) -> "fun"
      | Prim _ -> "prim" | Fexpr _ -> "fexpr" | ModVal _ -> "mod-val" | InChannel _ -> "in-channel" | OutChannel _ -> "out-channel" | Lz _ -> "lazy" | Object _ -> "object" | ExCall _ -> "ex-call" | ExDontCare -> "ex-dont-care"
    in
    let perhaps_assert_class =
      if any_failures then " failing"
      else if is_passing then " passing"
      else ""
    in
    let perhaps_expectation_class = if is_expectation then " expectation" else "" in
    span
      ~attrs:(
        [("data-active-vises", String.concat "  " active_vises)] @
        [("data-possible-vises", String.concat "  " possible_vises)] @
        perhaps_edit_code_attrs @
        perhaps_extraction_code @
        perhaps_type_attr @
        perhaps_code_to_assert_on @
        perhaps_destruction_code @
        [("class", "value " ^ value_class ^ perhaps_assert_class ^ perhaps_expectation_class)(* ; ("data-vtrace", Serialize.string_of_vtrace value.vtrace) *)]
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
  let assert_result_strs =
    if all_passed then [] else
    matching_asserts
    |>@ begin fun Data.{ expected; expected_exp; _ } ->
      span ~attrs:(exp_in_place_edit_attrs expected_exp)
        [html_of_value ~single_line_only ~is_expectation:true { empty_stuff with prog = stuff.prog } (-1) [] Envir.empty_env Env.empty [] None expected]
    end
  in
  wrap_value @@
  table ~attrs:[("class","subvalue-annotations")]
    [ tr [td [apply_visualizers stuff.prog stuff.assert_results visualizers env type_env extraction_exp_opt value]]
    ; tr [td [extracted_subvalue_names_html]]
    ] ^
  String.concat "" assert_result_strs ^
  match value_ with
  | Bomb                -> "💣"
  | Hole _              -> "?"
  | Int int             -> string_of_int int
  | Int32 int32         -> Int32.to_string int32
  | Int64 int64         -> Int64.to_string int64
  | Nativeint nativeint -> Nativeint.to_string nativeint
  | Fun _ | Function _  ->
    value.vtrace
    |> List.rev
    |> List.findmap_opt begin function
      | ((_, loc), Use)              -> Exp.find_opt loc stuff.prog |>& Attrs.remove_all_deep_exp |>& Exp.to_string
      | ((_, loc), PatMatch (_, [])) -> Pat.find_opt loc stuff.prog |>& Pat.to_string
      | _                            -> None
    end
    ||&~ begin fun _ ->
      match value_ with
      | Fun (arg_label, e_opt, pat, body, _) -> Exp.to_string (Attrs.remove_all_deep_exp @@ Exp.fun_ arg_label e_opt pat body)
      | Function (_, _)                      -> "func"
      | _                                    -> failwith "impossible"
    end
  | String bytes -> Exp.to_string (Exp.string_lit (Bytes.to_string bytes)) (* Make sure string is quoted & escaped *)
  | Float float  -> string_of_float float
  | Tuple vs     ->
    begin match (tuple_or_array_children ~in_list vs, in_list) with
    | ([head; tail], true) -> head ^ tail
    | (children, _)        -> "(" ^ String.concat ", " children ^ ")"
    end
  | Constructor ("[]", _, None)          -> if in_list then "]" else "[]"
  | Constructor (ctor_name, _, None)     -> ctor_name
  | Constructor (ctor_name, _, Some arg) ->
    let ctor_name_to_show = if ctor_name = "::" then (if in_list then "; " else "[") else ctor_name ^ " " in
    extraction_exp_opt |>&& begin fun extraction_exp ->
      ctor_destruction_pat_and_ctor_arg_pat_opt
      |>&& begin function
      | (pat,  Some ctor_arg_pat) -> Some (pat, ctor_arg_pat)
      | (_pat, None)              -> None
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
  | Prim (prim_name, _) -> prim_name
  | Fexpr _             -> "fexpr"
  | ModVal _            -> "modval"
  | InChannel _         -> "inchannel"
  | OutChannel _        -> "outchannel"
  | Record entry_map    ->
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
  | Lz _                          -> "lazy"
  | Array values_arr              -> "[! " ^ String.concat "; " (tuple_or_array_children @@ Array.to_list values_arr) ^ " !]"
  | Fun_with_extra_args (_, _, _) -> "funwithextraargs"
  | Object _                      -> "object"
  | ExCall _                      -> "ExCall ShouldntSeeThis"
  | ExDontCare                    -> "ExDontCare ShouldntSeeThis"


(* [a,b,c,d,e,g,h] => ([Some a, Some b, None, Some g, Some h], count_elided) *)
(* Its own function because we use the logic a few different contexts. *)
(* max_shown should be odd. *)
let max_frames_per_function = 7 (* Should be odd. *)
let elide_middle_if_too_many max_shown list =
  if List.length list >= max_shown then
    let list' =
      (List.prefix (max_shown/2) list |>@ Option.some) @
      [None] @
      (List.suffix (max_shown/2) list |>@ Option.some)
    in
    (list', List.length list - 2*(max_shown/2))
  else
    (List.map Option.some list, 0)

(* Sorted by frame_no *)
let entries_for_locs stuff locs = stuff.trace |> Trace.entries_for_locs locs |> List.sort_by Trace.Entry.frame_no
let entries_for_loc  stuff loc  = entries_for_locs stuff [loc]

let html_of_trace_entry ?exp_to_assert_on ~single_line_only stuff visualizers type_env locs_editable_in_value root_exp_opt (loc, frame_no, value, env) =
  span
    (* data-loc is view root for visualizers, also for determining where to place new asserts before. *)
    ~attrs:[("class","root-value-holder"); ("data-loc", Serialize.string_of_loc loc); ("data-frame-no", string_of_int frame_no)]
    [html_of_value ?exp_to_assert_on ~single_line_only stuff frame_no visualizers env type_env locs_editable_in_value root_exp_opt value]

let value_htmls_for_loc ?exp_to_assert_on ~single_line_only stuff type_env associated_exp_label_opt root_exp_opt visualizers loc =
  let entries = entries_for_loc stuff loc in
  let locs_editable_in_value = (associated_exp_label_opt |>& Exp.flatten ||& []) |>@ Exp.loc in
  let (elided_entries, count_elided) = elide_middle_if_too_many max_frames_per_function entries in
  elided_entries |>@ begin function
    | Some entry -> html_of_trace_entry ?exp_to_assert_on ~single_line_only stuff visualizers type_env locs_editable_in_value root_exp_opt entry
    | None       -> span ~attrs:[("class","ellipses")] ["..." ^ string_of_int count_elided ^ " more..."]
  end

(* let value_htmls_for_loc ~single_line_only stuff type_env associated_exp_label_opt root_exp_opt visualizers loc = *)


(* This is a separate function because the table view for function params needs the value htmls separately *)
let html_of_values_for_loc ?exp_to_assert_on ~single_line_only stuff type_env associated_exp_label_opt root_exp_opt visualizers loc =
  let inners = value_htmls_for_loc ?exp_to_assert_on ~single_line_only stuff type_env associated_exp_label_opt root_exp_opt visualizers loc in
  div ~attrs:[("class","values")] inners

let html_of_values_for_exp ?exp_to_assert_on ?(single_line_only = false) stuff vb_pat_opt exp =
  let exp_to_assert_on = exp_to_assert_on ||& exp in
  let type_env = stuff.type_lookups.Typing.lookup_exp exp.pexp_loc |>& (fun texp -> texp.Typedtree.exp_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs exp.pexp_attributes in
  (* If this is a return that's bound to a vb pat, use that pat var as the extraction root rather than the exp. *)
  let root_exp = vb_pat_opt |>&& Pat.single_name |>& Exp.var ||& exp in
  html_of_values_for_loc ~exp_to_assert_on ~single_line_only stuff type_env (Some exp) (Some root_exp) visualizers exp.pexp_loc

let value_htmls_for_pat ?(single_line_only = false) stuff pat =
  let type_env = stuff.type_lookups.Typing.lookup_pat pat.ppat_loc |>& (fun tpat -> tpat.Typedtree.pat_env) ||& Env.empty in
  let visualizers = Vis.all_from_attrs pat.ppat_attributes in
  let root_exp_opt = Pat.single_name pat |>& Exp.var in
  value_htmls_for_loc ~single_line_only stuff type_env None root_exp_opt visualizers pat.ppat_loc

let html_of_values_for_pat ?(single_line_only = false) stuff pat =
  div ~attrs:[("class","values")] (value_htmls_for_pat ~single_line_only stuff pat)


type parens_context = NoParens | NormalArg | NextToInfixOp

let accept_or_reject_options_html ?(item_name = "") prog exp =
  let ast_size_change =
    (* AST size of expression, less any holes or nested expressions that are also pending accept/reject *)
    (* For synth stats for paper. *)
    let with_all_descendents_rejected =
      { exp with pexp_attributes = [] }
      |> Exp.FromNode.replace_by Synth.has_accept_reject_tag Exp.hole
      |> Attrs.remove_all_deep_exp
    in
    let hole_count = with_all_descendents_rejected |> Exp.FromNode.count Exp.is_hole in
    Synth.exp_size with_all_descendents_rejected - hole_count
  in
  (* Only show "try again" button when there's one accept/reject left. *)
  let perhaps_accept_and_try_again =
    if Exp.count Synth.has_accept_reject_tag prog = 1 && Exp.count Exp.is_hole prog >= 1
    then [ button ~attrs:[("data-accept-and-continue-loc", Serialize.string_of_loc exp.pexp_loc); ("data-ast-size-change", string_of_int ast_size_change)] ["✅ Accept & try again"] ]
    else []
  in
  let perhaps_reject_and_try_again =
    if Exp.count Synth.has_accept_reject_tag prog = 1
    then [ button ~attrs:[("data-reject-and-continue-loc", Serialize.string_of_loc exp.pexp_loc)] ["❌ Reject & try again"] ]
    else []
  in
  span ~attrs:[("class","accept-or-reject-options")] @@
    [ button ~attrs:[("data-accept-loc", Serialize.string_of_loc exp.pexp_loc); ("data-ast-size-change", string_of_int ast_size_change)] ["✅ Accept " ^ item_name]
    ] @ perhaps_accept_and_try_again @
    [ button ~attrs:[("data-reject-loc", Serialize.string_of_loc exp.pexp_loc)] ["❌ Reject " ^ item_name]
    ] @ perhaps_reject_and_try_again



(* For exp labels *)
let rec html_of_exp ?(tv_root_exp = false) ?(show_result = true) ?(infix = false) ?(parens_context = NoParens) ?(in_list = false) (stuff : stuff) exp =
  let recurse ?(show_result = true) ?(infix = false) ?(parens_context = NoParens) ?(in_list = false) = html_of_exp ~show_result ~infix ~parens_context ~in_list stuff in
  let (code', attrs) = exp_gunk ~infix stuff exp in
  let perhaps_exp_class = if Exp.is_hole exp then " hole" else if Exp.is_ite exp then " ite" else if Exp.is_ident exp then " ident" else "" in
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
    let type_error_htmls = type_error_htmls stuff exp.pexp_loc in
    let perhaps_type_error_class = if type_error_htmls <> [] then " has-type-error" else "" in
    let (perhaps_accept_reject_class, perhaps_accept_or_reject_html) =
      if Synth.has_accept_reject_tag exp
      then
        ( " accept-or-reject-exp"
        , [ accept_or_reject_options_html stuff.prog exp ]
        )
      else ("", [])
    in
    span
      ~attrs:([("class","exp" ^ perhaps_exp_class ^ perhaps_accept_reject_class ^ perhaps_type_error_class)] @ attrs)
      (type_error_htmls @ [if needs_parens then "(" ^ inner ^ ")" else inner] @ perhaps_accept_or_reject_html)
  in
  let values_for_exp =
    (* if true then "" else *)
    if show_result && not (Exp.is_hole exp) && not tv_root_exp && Scope.free_unqualified_names exp <> [] then html_of_values_for_exp ~single_line_only:true stuff None exp else ""
  in
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
    | true, [la1; la2] -> html_of_labeled_arg ~parens_context:NextToInfixOp la1 ^ " " ^ (values_for_exp ^ if Exp.is_ident fexp then uninfix (Exp.to_string @@ Attrs.remove_all_deep_exp fexp) else recurse ~show_result:false ~infix:true ~parens_context:NormalArg fexp) ^ " " ^ html_of_labeled_arg ~parens_context:NextToInfixOp la2
    | _                -> values_for_exp ^ (if Exp.is_ident fexp then (Exp.to_string @@ Attrs.remove_all_deep_exp fexp) ^ " " else recurse ~parens_context:NormalArg ~show_result:false fexp) ^ (labeled_args |>@ html_of_labeled_arg ~parens_context:NormalArg |> String.concat " ")
    end
  | Pexp_construct ({ txt = Longident.Lident "[]"; _ }, None) -> values_for_exp ^ if in_list then "]" else "[]"
  | Pexp_construct ({ txt = Longident.Lident "::"; _ }, Some { pexp_desc = Pexp_tuple [head; tail]; _}) ->
    if String.starts_with "[" code' && String.ends_with "]" code' then (* Have to make sure this list is suitable to render sugared *)
      values_for_exp ^ (if in_list then "; " else "[ ") ^ recurse head ^ recurse ~in_list:true tail
    else
      (* Render infix *)
      recurse ~parens_context:NextToInfixOp head ^ values_for_exp ^ " :: " ^ recurse ~parens_context:NextToInfixOp tail
  | Pexp_construct ({ txt = lid; _ }, Some arg) ->
    values_for_exp ^ Longident.to_string lid ^ " " ^ recurse ~parens_context:NormalArg arg
  | Pexp_tuple exps ->
    "(" ^ String.concat ", " (exps |>@ recurse) ^ ")"
  | Pexp_ifthenelse (e1, e2, e3_opt) ->
    values_for_exp ^ "if " ^ recurse e1 ^ "<br>then " ^ recurse e2 ^ (e3_opt |>& (fun e3 -> "<br>else " ^ recurse e3) ||& "")
  | _ when String.includes "ident" perhaps_exp_class -> (* not on holes *)
    (* the ident-label class will be toggled off by the JS when the selected call frame has no values. *)
    (* For top level, show the code as a label if there are any values. *)
    (* The CSS handles the styling to draw ident values differently (based on the ident class in `wrap` above) *)
    let code_class = if String.includes "root-value-holder" values_for_exp then "ident-label" else "" in
    span ~attrs:[("class",code_class)] [code'] ^ values_for_exp ^ " "
  | _ ->
    values_for_exp ^ code' ^ " "

let rec gather_vbs exp = (* Dual of ret_tree_html *)
  let tag_rec recflag vb = (recflag, vb) in
  match exp.pexp_desc with
  | Pexp_let (recflag, vbs, e) -> (vbs |>@ tag_rec recflag) @ gather_vbs e
  | Pexp_sequence (e1, e2)     -> [(Asttypes.Nonrecursive, Vb.mk ~loc:e1.pexp_loc ~attrs:e1.pexp_attributes (Pat.unit) e1)] @ gather_vbs e2 (* Need to put the loc/attrs on the vb so the view code that sets up position works. *)
  | Pexp_match (_, cases)      -> cases |>@ Case.rhs |>@@ gather_vbs
  | Pexp_letmodule (_, _, e)   -> gather_vbs e
  | _                          -> []

let rec gather_case_pats exp =
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> gather_case_pats e
  | Pexp_sequence (_, e)     -> gather_case_pats e
  | Pexp_match (_, cases)    -> (cases |>@ Case.lhs |>@@ Pat.flatten |>@? Pat.is_name) @ (cases |>@ Case.rhs |>@@ gather_case_pats)
  | Pexp_letmodule (_, _, e) -> gather_case_pats e
  | _                        -> []

let should_show_vbs { pexp_desc; _ } =
  match pexp_desc with
  | Pexp_let _ | Pexp_sequence _ | Pexp_match _ | Pexp_letmodule _ -> true
  | _ -> false

let rec html_of_vb stuff recflag vb =
  let is_rec_perhaps_checked = if recflag = Asttypes.Recursive then [("checked","true")] else [] in
  let show_pat               = not (Pat.is_unit vb.pvb_pat) in
  let show_pat_on_top        = Exp.is_funlike vb.pvb_expr || should_show_vbs vb.pvb_expr in
  let perhaps_type_attr      = stuff.type_lookups.lookup_exp vb.pvb_expr.pexp_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.exp_type)]) ||& [] in
  let attrs                  = [("data-edit-loc", Serialize.string_of_loc vb.pvb_loc); ("data-edit-code", Vb.to_string vb)] @ perhaps_type_attr in
  box ~loc:vb.pvb_loc ~parsetree_attrs:vb.pvb_attributes ~attrs "vb" @@
    (if show_pat && show_pat_on_top then [html_of_pat stuff vb.pvb_pat] else []) @
    (if show_pat && Exp.is_funlike vb.pvb_expr then [label ~attrs:[("class","is-rec")] [checkbox ~attrs:(is_rec_perhaps_checked @ [loc_attr vb.pvb_loc]) (); "rec"]] else []) @
    [render_tv stuff (if show_pat then Some vb.pvb_pat else None) (Some vb.pvb_expr)](*  @
    (if show_pat && not show_pat_on_top then [html_of_pat stuff vb.pvb_pat] else []) *)

and html_tv_of_case_pat stuff pat =
  let perhaps_type_attr = stuff.type_lookups.lookup_pat pat.ppat_loc |>& (fun texp -> [("data-type", Type.to_string texp.Typedtree.pat_type)]) ||& [] in
  let attrs             = [("data-edit-loc", Serialize.string_of_loc pat.ppat_loc); ("data-edit-code", Pat.to_string pat)] @ perhaps_type_attr in
  box ~loc:pat.ppat_loc ~parsetree_attrs:pat.ppat_attributes ~attrs "vb" @@
    [render_tv stuff (Some pat) None]

(* Shows value bindings *)
and local_canvas_vbs_and_returns_htmls stuff exp =
  let html_of_vb (recflag, vb) = html_of_vb stuff recflag vb in
  let vbs                      = gather_vbs exp in
  let case_pats_to_show_as_tvs = gather_case_pats exp in
  (* let terminal_exps = terminal_exps exp in *)
  (* let ret_tv_path_descs = terminal_match_paths exps |>@ fun (_, pat, _) -> Pat.to_string pat in *)
  (* let ret_tv_htmls  = terminal_exps |>@ render_tv stuff None in *)
  [ div ~attrs:[("class", "vbs"); loc_attr exp.pexp_loc] @@ [hint "Bindings inside function - drag what you want below, or double-click to write code"] @ (case_pats_to_show_as_tvs |>@ html_tv_of_case_pat stuff) @ (vbs |>@ html_of_vb)
  ; div ~attrs:[("class", "returns")] [hint "Return expression(s) and value(s)"; ret_tree_html stuff exp]
  ]

and ret_tree_html stuff exp =
  let recurse = ret_tree_html stuff in
  match exp.pexp_desc with
  | Pexp_let (_, _, e)            -> recurse e
  | Pexp_sequence (_, e2)         -> recurse e2
  | Pexp_letmodule (_, _, e)      -> recurse e
  | Pexp_match (scrutinee, cases) ->
    let perhaps_accept_or_reject =
      if Synth.has_accept_reject_tag exp
      then [accept_or_reject_options_html ~item_name:"case split" stuff.prog exp]
      else []
    in
    let (_, attrs) = exp_gunk stuff exp in
    let html_of_case case =
      span ~attrs:[("class","case")] [html_of_pat stuff case.pc_lhs; recurse case.pc_rhs]
    in
    div ~attrs:[("class","match")] @@
      [ div ~attrs:(attrs @ [("class","scrutinee")]) ["⇠ "; html_of_exp ~show_result:false stuff scrutinee; " ⇢"]
      ; div ~attrs:[("class","cases")] (cases |>@ html_of_case)
      ] @ perhaps_accept_or_reject
  | _ -> div ~attrs:[("class", "return")] [render_tv stuff None (Some exp)]

(* Mirrors ret_tree_html *)
and ret_exps stuff exp =
  let recurse = ret_exps stuff in
  match exp.pexp_desc with
  | Pexp_let (_, _, e)       -> recurse e
  | Pexp_sequence (_, e2)    -> recurse e2
  | Pexp_letmodule (_, _, e) -> recurse e
  | Pexp_match (_, cases)    -> cases |>@ Case.rhs |>@@ recurse
  | _                        -> [exp]

(* Actually renders all values, but only one is displayed at a time (via Javascript). *)
and render_tv stuff pat_opt (exp_opt : expression option) =
  (* if true then "" else *)
  match exp_opt with
  | Some ({ pexp_desc = Pexp_fun (_, _, first_arg_pat, _); _ } as exp) ->
    let rec get_param_rows_and_body exp =
      match exp.pexp_desc with
      | Pexp_fun (label, default_opt, pat, body) ->
        let later_rows, final_body = get_param_rows_and_body body in
        let default_exp_str = default_opt |>& (fun default_exp -> " = " ^ html_of_exp stuff default_exp) ||& "" in
        let row =
          tr ~attrs:[("class", "pat fun-param")] @@
            [ td ~attrs:[("class", "pat-label")] [string_of_arg_label label ^ html_of_pat stuff pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
            ] @ (value_htmls_for_pat stuff pat |>@ List.singleton |>@ td) @ [td ~attrs:[("class", "new-expectation-arg")] [textbox []]]
        in
        (row::later_rows, final_body)
      | _ -> ([], exp)
    in
    (* let get_ret_row some_param_row body =
      let frame_nos =
    in *)
    let param_rows, body = get_param_rows_and_body exp in
    let ret_row =
      let (entries, count_elided) =
        entries_for_loc stuff first_arg_pat.ppat_loc
        |> elide_middle_if_too_many max_frames_per_function
      in
      let rec arg_pat_locs = function
      | { pexp_desc = Pexp_fun (_, _, pat, body); _ } -> pat.ppat_loc :: arg_pat_locs body
      | _                                             -> []
      in
      let arg_pat_locs = arg_pat_locs exp in
      let frame_no_opts = entries |>@ Option.map Trace.Entry.frame_no in
      let ret_locs = ret_exps stuff body |>@ Exp.loc in
      let ret_entries = entries_for_locs stuff ret_locs in
      let type_env = stuff.type_lookups.Typing.lookup_pat first_arg_pat.ppat_loc |>& (fun tpat -> tpat.Typedtree.pat_env) ||& Env.empty in
      let arg_entry_opts = (* List of list of entries... [arg1_entries, arg2_entries, arg3_entries] *)
        (* Need to construct thing to assert on. *)
        arg_pat_locs |>@ begin fun pat_loc ->
          let arg_entries = entries_for_loc stuff pat_loc in
          frame_no_opts |>@& begin function
          | Some frame_no -> arg_entries |> List.find_opt (Trace.Entry.frame_no %> (=) frame_no)
          | None          -> None
          end
        end
      in
      let tds =
        frame_no_opts |>@ begin function
          | Some frame_no ->
            let arg_values_opt =
              arg_entry_opts |>@ begin fun arg_entries ->
                arg_entries
                |> List.find_opt (Trace.Entry.frame_no %> (=) frame_no)
                |>& Trace.Entry.value
              end
              |> Option.project
            in
            let ret_entry_opt =
              ret_entries
              |> List.find_opt (Trace.Entry.frame_no %> (=) frame_no)
            in
            let exp_to_assert_on =
              match pat_opt |>&& Pat.single_name, arg_values_opt with
              | Some fname, Some arg_vals -> Some (Exp.simple_apply fname (arg_vals |>@ Assert_comparison.exp_of_value))
              | _                         -> None
            in
            ret_entry_opt |>& html_of_trace_entry ?exp_to_assert_on ~single_line_only:false stuff [] type_env [] None ||& ""
          | None -> span ~attrs:[("class","ellipses")] ["..." ^ string_of_int count_elided ^ " more..."]
        end
        |>@ List.singleton |>@ td
      in
      tr ~attrs:[("class", "fun-returns")] @@
        [ td ~attrs:[("class", "returns-label")] ["Return"]
        ] @ tds @ [td ~attrs:[("class", "new-expectation-return")] [textbox []]]
    in
    let perhaps_accept_or_reject =
      if Synth.has_accept_reject_tag exp
      then [accept_or_reject_options_html ~item_name:"function introduction" stuff.prog exp]
      else []
    in
    (* Technically, a function is a value and one can argue the above code should be in html_of_values_for_exp *)
    (* Don't remember why I double wrapped this. But when I do, hovering over a top level value causes other top level functions to gray out because there's no child element that has the same frameNo as the top level. So let's try not double wrapping and see what happens... *)
    (* div ~attrs:[("class", "tv")] [ *)
      div ~attrs:[("class", "fun exp tv")] begin
        [ table @@ param_rows @ [ret_row] ] @
        [ div ~attrs:[("class", "add-expectation");("title", "Add example call")] ["+"]] @
        local_canvas_vbs_and_returns_htmls stuff body @
        perhaps_accept_or_reject
      end
    (* ] *)
  | Some ({ pexp_desc = Pexp_assert e; _ }) ->
    let matching_asserts =
      begin match Eval.parse_assert e with
      | Some (lhs, expected) ->
        stuff.assert_results
        |>@? (fun Data.{ lhs_exp; expected_exp; _ } -> (lhs_exp, expected_exp) = (lhs, expected))
      | None -> []
      end
    in
    let lhs_opt = Eval.parse_assert e |>& (fun (lhs, _) -> lhs) in
    (* print_endline @@ string_of_int (List.length assert_results); *)
    let all_passed = List.for_all (fun Data.{ passed; _ } -> passed) matching_asserts in
    let any_failures = List.exists (fun Data.{ passed; _ } -> not passed) matching_asserts in
    let is_passing = all_passed && matching_asserts <> [] in
    let pass_fail_class, pass_fail_icon =
      if any_failures then (" failing", "✘")
      else if is_passing then (" passing", "✔︎")
      else ("", "")
    in
    div ~attrs:[("class", "tv assert" ^ pass_fail_class)] begin
      [ div ~attrs:[("class", "label")] [pass_fail_icon; html_of_exp ~tv_root_exp:true stuff e]
      ] @ if is_passing then [] else (lhs_opt |>& html_of_values_for_exp stuff None |> Option.to_list)
    end
  | Some ({ pexp_desc = Pexp_constraint (e, _); _ }) ->
    render_tv stuff pat_opt (Some e)
  | Some exp ->
    div ~attrs:[("class", "tv")] begin
      if should_show_vbs exp then
        local_canvas_vbs_and_returns_htmls stuff exp
      else
        [ div ~attrs:[("class", "label")] @@
          (pat_opt |>& (fun pat -> html_of_pat ~attrs:[("class", "pat-label pat")] stuff pat ^ "=") |> Option.to_list) @
          [html_of_exp ~tv_root_exp:true stuff exp]
        ; html_of_values_for_exp stuff pat_opt exp
        ]
    end
  | None ->
    pat_opt |>& begin fun pat ->
      div ~attrs:[("class", "tv")]
        [ div ~attrs:[("class", "label")] [html_of_pat ~attrs:[("class", "pat-label pat")] stuff pat]
        ; html_of_values_for_pat stuff pat
        ]
    end ||& "expected either a pat or an exp to be given to render_tv"


let html_of_top_matter_structure_item (item : structure_item) =
  match item.pstr_desc with
  | Pstr_type (_, _) -> div ~attrs:[("class", "type-def");("data-edit-loc", Serialize.string_of_loc item.pstr_loc)] [StructItem.to_string item]
  | _                -> ""

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
  (* ~10ms *)
  (* if true then "" else *)
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

let render_fatal_errors fatal_errors =
  let cleanup str =
    str
    |> String.replace "\027[1m" ""
    |> String.replace "\027[0m" ""
    |> String.replace "\027[1;31m" ""
  in
  div ~attrs:[("class", "fatal_errors")] begin
    fatal_errors
    |>@ begin fun error ->
      div ~attrs:[("class", "fatal_error")] [cleanup @@ Formatter_to_stringifier.f Location.report_exception error]
    end
  end



let html_str (structure_items : structure) lines_of_code_count (trace : Trace.t) (assert_results : Data.assert_result list) type_lookups fatal_errors type_errors final_env final_tenv =
  let names_in_prog = StructItems.deep_names structure_items in
  let stuff =
    { trace                                 = trace
    ; prog                                  = structure_items
    ; assert_results                        = assert_results
    ; type_lookups                          = type_lookups
    ; type_errors                           = type_errors
    ; names_in_prog                         = names_in_prog
    ; final_env                             = final_env
    ; possible_function_names_on_type_cache = ref []
    }
  in
  let prog_no_attrs = Attrs.remove_all_deep structure_items in
  (* print_endline @@ StructItems.to_string prog_no_attrs; *)
  let ast_size      = Synth.program_size prog_no_attrs in (* # of pat nodes plus # of exp nodes *)
  let asserts_count = Exp.count Exp.is_assert prog_no_attrs in
  let asserts_size =
    let asserts_size = ref 0 in
    prog_no_attrs
    |> Vb.iter begin fun vb ->
      if Exp.is_assert vb.pvb_expr then
        asserts_size := !asserts_size + (Synth.pat_size vb.pvb_pat + Synth.exp_size vb.pvb_expr)
    end;
    !asserts_size
  in
  let top_level_vbs_loc = structure_items |> List.last_opt |>& StructItem.loc ||& Location.none in
  html
    [ head
      [ title "Maniposynth"
      ; meta [("charset", "UTF-8")]
      ; link [("rel","icon");("type","image/png");("href","/assets/m.png")]
      ; stylesheet "/assets/maniposynth.css"
      ; script ~src:"/assets/maniposynth.js" ""
      ; script ~src:"/assets/reload_on_file_changes.js" ""
      ]
    ; body @@
      [ nav @@
        [ img ~attrs:[("src", "/assets/maniposynth.svg")]
        ; span ~attrs:[("class","settings tool")]
          [ img ~attrs:[("src", "/assets/settings-gear.svg")]; " ▾"
          ; div ~attrs:["class","settings-pane"]
            [  checkbox ~attrs:[("id", "show-values-in-green-exp-labels");("checked","checked")] ()
            ;  label ~attrs:[("for","show-values-in-green-exp-labels")] ["Show value superscripts in green expression labels."]
            ]
          ]
        ; span ~attrs:[("class","undo tool")] ["Undo (" ^ span ~attrs:[("class","command-key-glyph")] [] ^ "Z)"]
        ; span ~attrs:[("class","redo tool")] ["Redo  (⇧" ^ span ~attrs:[("class","command-key-glyph")] [] ^ "Z)"]
        ] @ [drawing_tools final_tenv structure_items]
      ]
      @ begin if structure_items <> [] then [] else
        [ div ~attrs:([("id", "mission-statement")] @ if structure_items <> [] then [("class","there-is-code-now")] else []) @@
          [ img ~attrs:[("src", "/assets/maniposynth.svg")]
          ; p ["Exploring the frontiers of visual interactive programming—can cutting-edge features meld into a delightful and productive coding environment?"]
          ; p [strong ["Live -"]; "Instant feedback of runtime values."]
          ; p [strong ["Non-linear -"]; "Gather the parts you need, assemble later."]
          ; p [strong ["Synthesis -"]; "Assert and let the computer write code."]
          ; p [strong ["Bimodal -"]; "Work in your normal editor whenever you want."]
          ]
        ]
      end
      @ if fatal_errors <> [] then [render_fatal_errors fatal_errors] else
      [ div ~attrs:[("class", "top-matter")] @@
        List.map html_of_top_matter_structure_item structure_items
      ; div ~attrs:[("class", "top-level vbs"); loc_attr top_level_vbs_loc] @@
        [hint "Top level - drag items from the menus above, or double-click below to write code"] @
        List.map (html_of_vb_structure_item stuff) structure_items
      ; div ~attrs:[("id", "inspector")]
        [ div ~attrs:[("id", "text-edit-pane")]
          [ div ~attrs:[("id", "text-edit-node-stuff")]
            [ label ~attrs:[("for","node-textbox");("id", "type-of-selected")] []
            ; fancyTextbox ~attrs:[("id", "node-textbox")] []
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
      ; button ~attrs:[("id", "synth-button")] ["Synth (" ^ span ~attrs:[("class","command-key-glyph")] [] ^ "Y)"]
      ; div ~attrs:[("id", "tooltip")] []
      ; button ~attrs:[("id", "destruct-button")] ["Destruct"]
      ; div ~attrs:[("id", "interaction-stats")]
        [ button  ~attrs:[("id", "reset-interaction-stats")] ["Reset"]
        ; button  ~attrs:[("id", "copy-interaction-stats")] ["Copy"]
        ; table
          [ tr [td ["LOC"]; td ["AST Size"]; td ["Asserts Count"]; td ["Asserts Size"]]
          ; tr [td [string_of_int lines_of_code_count (* Including annotations, excluding blank lines. *)]; td [string_of_int ast_size]; td [string_of_int asserts_count]; td [string_of_int asserts_size]]
          ]
        ]
      ]
    ]
