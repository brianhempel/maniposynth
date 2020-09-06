open Tyxml.Html
open Ocamlformat_lib.Migrate_ast.Parsetree


type skel = Skeleton.t

(* type skel =
  | Constant of constant
  | Unknown
  | Let of (value_binding * t) list * t
  | Fun of Asttypes.arg_label * expression option * pattern * t
  | App of t * (Asttypes.arg_label * expression option * pattern) * (Asttypes.arg_label * expression * t) * t *)

let box = div ~a:[a_class ["box"]]


let rec html_of_skeleton (skel : skel) =
  let param_label_box param_label default_opt pat =
    let param_code = Show_ast.fun_param param_label default_opt pat in
    box [txt param_code]
  in
  match skel with
  | Top_binding (vb, skel) -> box_of_binding_skel (vb, skel)
  | Constant constant -> box [txt (Show_ast.constant constant)]
  | Unknown -> box [txt "?"]
  | Labeled exp ->
      box
        [ box [txt (Show_ast.exp exp)]
        ; txt "?"
        ]
  | Let (bindings_skels, body_skel) ->
      let binding_boxes = List.map box_of_binding_skel bindings_skels in
      div (binding_boxes @ [html_of_skeleton body_skel])
  | Fun (param_label, default_opt, pat, body_skel) ->
      box [param_label_box param_label default_opt pat; html_of_skeleton body_skel]
  | Apply (f_exp, arg_labels_skels) ->
      let arg_box (_arg_label, arg_skel) = html_of_skeleton arg_skel in
      box @@
        [ box [txt (Show_ast.exp f_exp)] ] @
        List.map arg_box arg_labels_skels @
        [ txt "?" ]
  | Construct (longident, arg_skel_opt) ->
      (* imitate display of Apply *)
      let arg_box_opt = Option.map html_of_skeleton arg_skel_opt in
      box @@
      [ box [txt (Show_ast.longident longident)] ] @
      Option.to_list arg_box_opt @
      [ txt "?" ]
  | Skels skels ->
    box (List.map html_of_skeleton skels)

and box_of_binding_skel (binding, skel) =
  let binding_code =
    Show_ast.pat binding.pvb_pat ^ " = " ^ Show_ast.exp binding.pvb_expr
  in
  box [box [txt binding_code]; html_of_skeleton skel]

let string_of_doc doc =
  ignore (Format.flush_str_formatter ());
  pp () Format.str_formatter doc;
  Format.flush_str_formatter ()

let html_of_callables callables =
  let html_of_callable (name, arg_count) =
    let arg_strs = List.init arg_count (fun _ -> "?") in
    box [txt (String.concat " " (name :: arg_strs))]
  in
  div ~a:[a_id "toolbox"]
    (List.map html_of_callable callables)

let html_str (callables : (string * int) list) skels =
  let doc = 
    html
      (head (title (txt "Manipos")) [link ~rel:[`Stylesheet] ~href:"assets/maniposynth.css" ();])
      (body @@
        html_of_callables callables ::
        (List.map html_of_skeleton skels)
      )
  in
  string_of_doc doc



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
