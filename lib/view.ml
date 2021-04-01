open Camlboot_interpreter

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


let html_box label content =
  table
    [ tr [td ~attrs:[("class", "label")] [label]]
    ; tr [td ~attrs:[("class", "values")] [content]]
    ]

let rec html_of_value ((value_, _) as value : Data.value) =
  let open Data in
  let wrap_value str = span ~attrs:[("class", "value"); ("data-value", Serialize.string_of_value value)] [str] in
  wrap_value @@
  match value_ with
  | Bomb                                     -> "💣"
  | Int int                                  -> string_of_int int
  | Int32 int32                              -> Int32.to_string int32
  | Int64 int64                              -> Int64.to_string int64
  | Nativeint nativeint                      -> Nativeint.to_string nativeint
  | Fun (_, _, _, _, _)                      -> "func"
  | Function (_, _)                          -> "func"
  | String bytes                             -> Bytes.to_string bytes
  | Float float                              -> string_of_float float
  | Tuple values                             -> "(" ^ String.concat ", " (List.map html_of_value values) ^ ")"
  | Constructor (ctor_name, _, None)         -> ctor_name
  | Constructor (ctor_name, _, Some arg_val) -> ctor_name ^ " " ^ html_of_value arg_val
  | Prim _                                   -> "prim"
  | Fexpr _                                  -> "fexpr"
  | ModVal _                                 -> "modval"
  | InChannel _                              -> "inchannel"
  | OutChannel _                             -> "outchannel"
  | Record entry_map                         -> entry_map |> SMap.bindings |> List.map (fun (field_name, value_ref) -> field_name ^ " = " ^ html_of_value !value_ref) |> String.concat "; " |> (fun entries_str -> "{ " ^ entries_str ^ " }")
  | Lz _                                     -> "lazy"
  | Array values_arr                         -> "[! " ^ (values_arr |> Array.to_list |> List.map html_of_value |> String.concat "; ") ^ " !]"
  | Fun_with_extra_args (_, _, _)            -> "funwithextraargs"
  | Object _                                 -> "object"


let html_of_values_for_loc trace loc =
  trace
  |> Trace.entries_for_loc loc
  |> List.map Trace.Entry.value
  |> List.map html_of_value
  |> String.concat "\n"


let html_box_of_vb (vb : Parsetree.value_binding) =
  html_box
    (string_of_pat vb.pvb_pat ^ " = " ^ string_of_exp vb.pvb_expr)
    ""


let html_box_of_exp trace (exp : Parsetree.expression) =
  html_box
    (string_of_exp exp)
    (html_of_values_for_loc trace exp.pexp_loc)


let rec fun_rows trace (param_label : Asttypes.arg_label) param_exp_opt param_pat body_exp =
  let default_exp_str =
    match param_exp_opt with
    | None             -> ""
    | Some default_exp -> " = " ^ string_of_exp default_exp
  in
  ( tr
    [ td [string_of_arg_label param_label ^ string_of_pat param_pat ^ default_exp_str] (* START HERE: need to trace function value bindings in the evaluator *)
    ; td [html_of_values_for_loc trace param_pat.ppat_loc]
    ]
  ) :: rows_ensure_vbs_canvas_of_exp trace body_exp

and rows_ensure_vbs_canvas_of_exp trace (exp : Parsetree.expression) =
  let single_exp () =
    [ tr [td ~attrs:[("colspan", "2")] [""]]
    ; tr [td ~attrs:[("colspan", "2")] [html_box_of_exp trace exp]]
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
             , body_exp)      -> fun_rows trace param_label param_exp_opt param_pat body_exp
  | Pexp_match (_, _)         -> unhandled "match"
  | Pexp_ifthenelse (_, _, _) -> unhandled "if then else"
  | _                         -> single_exp ()

let html_ensure_vbs_canvas_of_exp trace (exp : Parsetree.expression) =
  table (rows_ensure_vbs_canvas_of_exp trace exp)

let htmls_of_top_level_value_binding trace (vb : Parsetree.value_binding) =
  let drop_target_before_vb (vb : Parsetree.value_binding) =
    div ~attrs:
      [ ("data-before-vb-id", Serialize.string_of_loc vb.pvb_loc)
      ; ("style", "height: 2em")
      ] []
  in
  [ drop_target_before_vb vb
  ; box "value_binding"
      @@ [ string_of_pat vb.pvb_pat ^ " =" ]
      @  [ html_ensure_vbs_canvas_of_exp trace vb.pvb_expr ]
  ]

let html_of_structure_item trace (item : Parsetree.structure_item) =
  let open Parsetree in
  match item.pstr_desc with
  | Pstr_eval (_, _)            -> failwith "can't handle Pstr_eval"
  | Pstr_value (_rec_flag, vbs) -> String.concat "" (List.concat @@ List.map (htmls_of_top_level_value_binding trace) vbs)
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


let html_str (structure_items : Parsetree.structure) (trace : Trace.t) =
  html
    [ head
        [ title "Maniposynth"
        ; meta [("charset", "UTF-8")]
        ; stylesheet "/assets/maniposynth.css"
        ; script ~src:"/assets/maniposynth.js" ""
        ; script ~src:"/assets/reload_on_file_changes.js" ""
        ]
    ; body (List.map (html_of_structure_item trace) structure_items)
    ]
