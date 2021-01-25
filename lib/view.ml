let sprintf = Printf.sprintf

let rec print_attrs attrs  =
  match attrs with
  | (name, Some value)::rest -> sprintf " %s=\"%s\"%s" name value (print_attrs rest)
  | (name, None)::rest       -> sprintf " %s%s"        name       (print_attrs rest)
  | []                       -> ""

let tag name ?(attrs = []) inners =
  sprintf "<%s%s>%s</%s>" name (print_attrs attrs) (String.concat "" inners) name

let lone_tag name ?(attrs = []) () =
  sprintf "<%s%s />" name (print_attrs attrs)

let html ?(attrs = []) inners = tag "html" ~attrs inners
let head ?(attrs = []) inners = tag "head" ~attrs inners
let title ?(attrs = []) str = tag "title" ~attrs [str]
let stylesheet href =
  lone_tag "link" ~attrs:[("rel", Some "stylesheet"); ("href", Some href)] ()

let script ?src ?(attrs = []) str =
  match src with
  | Some src_str -> tag "script" ~attrs:(("src", Some src_str)::attrs) [str]
  | None         -> tag "script" ~attrs                                [str]


let body  ?(attrs = [])       inners = tag "body" ~attrs inners
let div   ?(attrs = [])       inners = tag "div" ~attrs inners
let table ?(attrs = [])       inners = tag "table" ~attrs inners
let tr    ?(attrs = [])       inners = tag "tr" ~attrs inners
let td    ?(attrs = [])       inners = tag "td" ~attrs inners
let box   ?(attrs = []) klass inners =
  let attrs = ("class", Some ("box " ^ klass))::attrs in
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
    [ tr [td ~attrs:[("class", Some "label")] [label]]
    ; tr [td ~attrs:[("class", Some "values")] [content]]
    ]

let html_box_of_vb (vb : Parsetree.value_binding) =
  html_box
    (string_of_pat vb.pvb_pat ^ " = " ^ string_of_exp vb.pvb_expr)
    ""

let html_box_of_exp (exp : Parsetree.expression) =
  html_box
    (string_of_exp exp)
    ""

let rec fun_rows (param_label : Asttypes.arg_label) param_exp_opt param_pat body_exp =
  let default_exp_str =
    match param_exp_opt with
    | None             -> ""
    | Some default_exp -> " = " ^ string_of_exp default_exp
  in
  ( tr
    [ td [string_of_arg_label param_label ^ string_of_pat param_pat ^ default_exp_str]
    ; td []
    ]
  ) :: rows_ensure_vbs_canvas_of_exp body_exp

and rows_ensure_vbs_canvas_of_exp (exp : Parsetree.expression) =
  let single_exp () =
    [ tr [td ~attrs:[("colspan", Some "2")] [""]]
    ; tr [td ~attrs:[("colspan", Some "2")] [html_box_of_exp exp]]
    ]
  in
  let unhandled node_kind_str =
    [ tr [td ~attrs:[("colspan", Some "2")] [""]]
    ; tr [td ~attrs:[("colspan", Some "2")] ["don't know how to handle nodes of kind " ^ node_kind_str]]
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
             , body_exp)      -> fun_rows param_label param_exp_opt param_pat body_exp
  | Pexp_match (_, _)         -> unhandled "match"
  | Pexp_ifthenelse (_, _, _) -> unhandled "if then else"
  | _                         -> single_exp ()

let html_ensure_vbs_canvas_of_exp (exp : Parsetree.expression) =
  table (rows_ensure_vbs_canvas_of_exp exp)

let html_of_top_level_value_binding (vb : Parsetree.value_binding) =
  box "value_binding"
    @@ [ string_of_pat vb.pvb_pat ^ " =" ]
    @  [ html_ensure_vbs_canvas_of_exp vb.pvb_expr ]

let html_of_structure_item (item : Parsetree.structure_item) =
  let open Parsetree in
  match item.pstr_desc with
  | Pstr_eval (_, _)            -> failwith "can't handle Pstr_eval"
  | Pstr_value (_rec_flag, vbs) -> String.concat "" (List.map html_of_top_level_value_binding vbs)
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


let html_of_phrase (phrase : Parsetree.toplevel_phrase) =
  let open Parsetree in
  match phrase with
  | Ptop_def structure_items -> String.concat "" (List.map html_of_structure_item structure_items)
  | Ptop_dir _               -> failwith "can't handle Ptop_dir"


let html_str (toplevel_phrases : Parsetree.toplevel_phrase list) =
  html
    [ head
        [ title "Maniposynth"
        (* ; meta [("charset", Some "UTF-8")] *)
        ; stylesheet "/assets/maniposynth.css"
        ; script ~src:"/assets/maniposynth.js" ""
        ; script ~src:"/assets/reload_on_file_changes.js" ""
        ]
    ; body (List.map html_of_phrase toplevel_phrases)
    ]
