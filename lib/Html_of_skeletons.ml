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
  | Constant constant -> box [txt (Show_ast.constant constant)]
  | Unknown -> box [txt "Unknown"]
  | Let (bindings_skels, body_skel) ->
      let binding_boxes = List.map box_of_binding_skel bindings_skels in
      div (binding_boxes @ [html_of_skeleton body_skel])
  | Fun (param_label, default_opt, pat, body_skel) ->
      box [param_label_box param_label default_opt pat; html_of_skeleton body_skel]
  | App (f_skel, (param_label, default_opt, pat), (arg_label, arg_exp, arg_skel), ret_skel) ->
      box
        [ html_of_skeleton f_skel
        ; box
            [ param_label_box param_label default_opt pat
            ; box
                [ box [txt (Show_ast.app_arg arg_label arg_exp)]
                ; html_of_skeleton arg_skel
                ]
            ]
        ; html_of_skeleton ret_skel
        ]
and box_of_binding_skel (binding, skel) =
  let binding_code =
    Show_ast.pat binding.pvb_pat ^ " = " ^ Show_ast.exp binding.pvb_expr
  in
  box [box [txt binding_code]; html_of_skeleton skel]

let string_of_doc doc =
  ignore (Format.flush_str_formatter ());
  pp () Format.str_formatter doc;
  Format.flush_str_formatter ()

let html_str_of_skeletons skels =
  let doc = 
    html
      (head (title (txt "Manipos")) [link ~rel:[`Stylesheet] ~href:"assets/maniposynth.css" ();])
      (body (List.map html_of_skeleton skels))
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
