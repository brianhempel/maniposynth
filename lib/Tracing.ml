open Parsetree

(* 
  Tracepoints:

  1. Just inside fun bodies:
      - setting the scope number
      - emitting the argument values
  2. Var uses (skeletonized as Apply's)
  3. Apply returns
  4. Construct returns (basically Apply returns)
*)

let tracepoint_placeholder ?(id : Ast_id.t option) (expr : expression) =
  let id = Option.value id ~default:(Ast_id.of_expr expr) in
  let id_str_exp = Ast_utils.Exp.string (Ast_id.string_of_t id) in
  let loc = Location.none in (* For metaquote below. *)
  [%expr tracepoint scope_n [%e id_str_exp] [%e expr]]


let rec map_first_non_fun f expr =
  match expr with
  | [%expr fun [%p? param] -> [%e? body]] ->
      let body' = map_first_non_fun f body in
      let loc = expr.pexp_loc in
      [%expr fun [%p param] -> [%e body']]
  | _ ->
      f expr



(* Provide a .ml file path. It will be mutated in place. *)
let add_tracepoint_placeholders toplevel_phrases =
  let open Ast_mapper in
  let add_tracepoints mapper expr =
    match expr with
    | [%expr fun [%p? param] -> [%e? body]] ->
      (match Ast_utils.Pat.get_var_name_opt param with
      | Some name ->
          let body' = mapper.expr mapper body in
          let body'' =
            body'
            |> map_first_non_fun (fun real_body ->
              let tp_expr = tracepoint_placeholder ~id:(Ast_id.of_pat param) (Ast_utils.Exp.var name) in
              let loc = Location.none in
              [%expr ignore [%e tp_expr] ; [%e real_body]]
            )
          in
          let loc = expr.pexp_loc in
          [%expr fun [%p param] -> [%e body'']]          
      | None ->
          default_mapper.expr mapper expr
      )

    | { pexp_desc = (Pexp_ident _ | Pexp_apply _ | Pexp_construct _); _ } ->
        let deeper = default_mapper.expr mapper expr in
        tracepoint_placeholder deeper
  
    | _ ->
      default_mapper.expr mapper expr
  in
  let add_scope_counters mapper expr =
    match expr with
    | [%expr fun [%p? param] -> [%e? body]] ->
        if not (Ast_utils.Exp.is_fun body) then
          let loc = expr.pexp_loc in
          [%expr fun [%p param] -> let scope_n = next_scope_n () in [%e body]]
        else
          default_mapper.expr mapper expr
    | _ ->
      default_mapper.expr mapper expr
  in
  let tp_mapper    = { default_mapper with expr = add_tracepoints } in
  let scope_mapper = { default_mapper with expr = add_scope_counters } in
  (*
    Put the top matter before the first let-binding so that we are (hopefully)
    after all the types. Monomorphization will get stuck in a loop if we are not
    after all the types (it will use a type not in scope and keep trying to monomorphize to infinity)
  *)
  let top_matter : structure_item list =
    let loc = Location.none in
    [ [%stri let scope_n_ref = ref 0]
    ; [%stri let next_scope_n () = incr scope_n_ref; !scope_n_ref]
    ; [%stri let scope_n = 0]
    ; [%stri let tracepoint _scope_n _id_str value = value]
    ]
  in
  let rec add_top_matter structure_items =
    match structure_items with
    | structure_item::rest ->
        (match structure_item.pstr_desc with
        | Pstr_primitive _ | Pstr_type _ | Pstr_typext _
        | Pstr_exception _ | Pstr_open _ | Pstr_include _ ->
            structure_item :: add_top_matter rest
        | _ ->
            top_matter @ structure_items   
        )
    | [] ->
      top_matter
  in
  toplevel_phrases
  |> Ast_utils.apply_mapper_to_toplevel_phrases tp_mapper
  |> Ast_utils.apply_mapper_to_toplevel_phrases scope_mapper
  |> Ast_utils.structure_of_toplevel_phrases
  |> add_top_matter 
  |> Ast_utils.toplevel_phrases_of_structure