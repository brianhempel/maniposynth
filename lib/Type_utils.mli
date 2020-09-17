open Types

val final_env_and_typed_structure_of_file : string -> (Env.t * Typedtree.structure)

(* Btype.fold_type_expr only applys f to the immediate children. *)
val deep_fold_type_expr : ('a -> type_expr -> 'a) -> 'a -> type_expr -> 'a

val arrow_types_flat : type_expr -> type_expr list

val flatten_type_expr : type_expr -> type_expr list
