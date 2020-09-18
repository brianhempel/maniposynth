open Ocamlformat_lib.Migrate_ast.Parsetree
open Utils


type skel = Skeleton.t

(* type skel =
  | Constant of constant
  | Unknown
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | App of t * (Asttypes.arg_label * expression option * pattern) * (Asttypes.arg_label * expression * t) * t *)

let txt = Tyxml.Html.txt
let div = Tyxml.Html.div
let a_class = Tyxml.Html.a_class
let a_id = Tyxml.Html.a_id
let a_user_data = Tyxml.Html.a_user_data

let box ?(attrs = []) klass = Tyxml.Html.div ~a:([a_class ["box"; klass]] @ attrs)

let label ?(attrs = []) str = box ~attrs "label" [txt str]

let ast_id_str_of_expr = Ast_id.of_expr %> Ast_id.string_of_t

let a_new_code code_str = a_user_data "new-code" code_str
let a_scope_id scope_expr = a_user_data "scope-id-str" (ast_id_str_of_expr scope_expr)
let a_expr_id expr        = a_user_data "expr-id-str" (ast_id_str_of_expr expr)
(* let a_pat_id pat          = a_user_data "pat-id-str" (ast_id_json_str_of_pat pat) *)

let rec html_of_value = function Tracing.Ctor (name, _type_name, args) ->
  box "value" @@
  match args with
  | []    -> [txt name]
  | [arg] -> [txt name; html_of_value arg]
  | args  -> [txt name; txt "("] @ List.map html_of_value args @ [txt ")"]

let html_of_traced_values_at trace id =
  let open Tracing in
  let tracesnaps =
    let target_str = Ast_id.string_of_t id in
    trace
    |> List.filter (function Tracesnap (_, id_str, _) -> target_str = id_str)
  in
  box "values" @@ begin
    tracesnaps
    |> List.map (function Tracesnap (frame_n, type_str, value) ->
      box "tracesnap"
        ~attrs:[ a_user_data "frame-n" (string_of_int frame_n)
               ; a_user_data "type" type_str ]
        [html_of_value value]
    )
    |> function [] -> [txt "?"] | list -> list
  end

let rec html_of_skeleton trace (skel : skel) =
  let recurse = html_of_skeleton trace in
  match skel with
  | Constant constant -> box "constant" [txt (Show_ast.constant constant)]
  | Unknown -> box "unknown" [txt "?"]
  | Bindings_rets (scope_expr, bindings_skels, ret_skels) ->
      let binding_boxes = List.map (html_of_binding_skel trace) bindings_skels in
      let ret_boxes = List.map recurse ret_skels in
      box "bindings_rets"
        [ box ~attrs:[a_scope_id scope_expr] "bindings" binding_boxes
        ; box ~attrs:[a_scope_id scope_expr] "rets" ret_boxes
        ]
  | Fun (param_label, default_opt, pat, body_skel) ->
      let param_code = Show_ast.fun_param param_label default_opt pat in
      box "fun"
        [ box "param" [label ~attrs:[a_new_code param_code] param_code; html_of_traced_values_at trace (Ast_id.of_pat pat)]
        ; box "ret" [recurse body_skel]
        ]
  | Apply (expr, f_expr, arg_labels_skels) ->
      let arg_box (_arg_label, arg_skel) = box "arg" [recurse arg_skel] in
      box "apply" @@
        [ label ~attrs:[a_expr_id expr] (Show_ast.expr f_expr)
        ; box "args" (List.map arg_box arg_labels_skels)
        ; box "ret" [html_of_traced_values_at trace (Ast_id.of_expr expr)]
        ]
  | Construct (expr, longident, arg_skel_opt) ->
      (* imitate display of Apply *)
      let arg_box_opt =
        arg_skel_opt
        |> Option.map (fun arg_skel -> box "args" [box "arg" [recurse arg_skel]])
      in
      box "apply construct" @@
        [ label ~attrs:[a_expr_id expr] (Show_ast.longident longident) ] @
        Option.to_list arg_box_opt @
        [ box "ret" [html_of_traced_values_at trace (Ast_id.of_expr expr)] ]

and html_of_binding_skel trace (binding, skel) =
  let binding_code =
    Show_ast.pat binding.pvb_pat ^ " = " ^ Show_ast.expr binding.pvb_expr
  in
  box "binding" [label binding_code; html_of_skeleton trace skel]

let html_of_callables callables =
  let html_of_callable (name, arg_count) =
    let arg_strs = List.init arg_count (fun _ -> "(??)") in
    let code_str = String.concat " " (name :: arg_strs) in
    box ~attrs:[a_new_code code_str] "callable" [txt code_str]
  in
  div ~a:[a_id "toolbox"]
    (List.map html_of_callable callables)

let html_str (callables : (string * int) list) (trace : Tracing.tracesnap list) bindings_skels =
  let open Tyxml.Html in
  let doc = 
    html
      (head (title (txt "Manipo"))
         [ link ~rel:[`Stylesheet] ~href:"assets/maniposynth.css" ()
         ; script ~a:[a_src (Xml.uri_of_string "assets/maniposynth.js")] (txt "")
         ; script ~a:[a_src (Xml.uri_of_string "assets/reload_on_file_changes.js")] (txt "")
         ]
      )
      (body @@
        html_of_callables callables ::
        (List.map (html_of_binding_skel trace) bindings_skels)
      )
  in
  (Utils.formatter_to_stringifyer (pp ())) doc;



(* 
let this_title = title (txt "Your Cool Web Page")

let image_box =
  div ~a:[a_id "image_box"]
    []

let links_box =
  ul ~a:[a_class ["links_bar"]; a_id "links_bar"]
    [li ~a:[a_id "home_click"]
       [txt "My Musings"];
     li ~a:[a_id "about_click"]
       [txt "About Me"];
     li ~a:[a_id "blog_posts_click"]
       [txt "Blog"];
     li ~a:[a_id "hackathons_click"]
       [txt "Hackathons"]]

let common_footer =
  footer ~a:[a_id "footer_box"]
    [p [txt "This site was made with ";
        a ~a:[a_href "http://ocaml.org"] [txt "OCaml"];
        txt " and ";
        a ~a:[a_href "https://www.gnu.org/software/emacs/"] [txt "emacs"]]]

let home_content =
  div
    [h2
       [txt "Hello Coder"]]

let main_payload =
  div ~a:[a_id "payload"]
    [home_content]

let common_nav =
  nav [links_box]

let content_box =
  div ~a:[a_id "content_box"]
    [common_nav;
     main_payload;
     common_footer]

let main_script =
  script ~a:[a_src (Xml.uri_of_string "main.js")] (txt "")

let home_page_doc =
  html (head this_title
          [link ~rel:[`Stylesheet] ~href:"home.css" ();])
    (body [image_box; content_box; main_script])

(** The set of pages in your website. *)
let pages = [("index.html", home_page_doc)]

(** Small code to emit all the pages. *)
let emit_page (name, page) =
  Printf.printf "Generating: %s\n" name ;
  let file_handle = open_out name in
  let fmt = Format.formatter_of_out_channel file_handle in
  Format.fprintf fmt "%a@." (pp ~indent:true ()) page;
  close_out file_handle

let () = List.iter emit_page pages *)
