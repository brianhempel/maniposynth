open Data

let cc x d = new_vtrace @@ Constructor (x, d, None)

let builtin_exn_handler wrap_exn f =
  try f ()
  with exn ->
    (* let bt = Printexc.get_raw_backtrace () in *)
    let exn =
      match wrap_exn exn with
      | None -> exn
      | Some exn_code -> InternalException exn_code
    in
    raise exn
    (* Printexc.raise_with_backtrace exn bt *)


let prim1 f wrap_exn unwrap1 wrap =
  new_vtrace @@ Prim
  (fun x -> try wrap (builtin_exn_handler wrap_exn (fun () -> f (unwrap1 x))) with BombExn -> new_vtrace Bomb)

let prim2 f wrap_exn unwrap1 unwrap2 wrap =
  new_vtrace @@ Prim
  (fun x -> try prim1 (f (unwrap1 x)) wrap_exn unwrap2 wrap with BombExn -> new_vtrace Bomb)

let prim3 f wrap_exn unwrap1 unwrap2 unwrap3 wrap =
  new_vtrace @@ Prim
  (fun x -> try prim2 (f (unwrap1 x)) wrap_exn unwrap2 unwrap3 wrap with BombExn -> new_vtrace Bomb)

let prim4 f wrap_exn unwrap1 unwrap2 unwrap3 unwrap4 wrap =
  new_vtrace @@ Prim
  (fun x -> try prim3 (f (unwrap1 x)) wrap_exn unwrap2 unwrap3 unwrap4 wrap with BombExn -> new_vtrace Bomb)

let prim5 f wrap_exn unwrap1 unwrap2 unwrap3 unwrap4 unwrap5 wrap =
  new_vtrace @@ Prim
  (fun x ->
    try prim4 (f (unwrap1 x)) wrap_exn unwrap2 unwrap3 unwrap4 unwrap5 wrap with BombExn -> new_vtrace Bomb)

let id x = x

let builtin_exn_id env id =
  Envir.env_get_constr env (Location.mknoloc (Longident.Lident id))

let exn0 env name = new_vtrace @@ Constructor (name, builtin_exn_id env name, None)

let exn1 env name wrap1 =
  let exn_id = builtin_exn_id env name in
  fun arg1 ->
    let v1 = wrap1 arg1 in
    new_vtrace @@ Constructor (name, exn_id, Some (new_vtrace @@ Tuple [ v1 ]))

let exn2 env name wrap1 wrap2 =
  let exn_id = builtin_exn_id env name in
  fun arg1 arg2 ->
    let v1 = wrap1 arg1 in
    let v2 = wrap2 arg2 in
    new_vtrace @@ Constructor (name, exn_id, Some (new_vtrace @@ Tuple [ v1; v2 ]))

let exn3 env name wrap1 wrap2 wrap3 =
  let exn_id = builtin_exn_id env name in
  fun arg1 arg2 arg3 ->
    let v1 = wrap1 arg1 in
    let v2 = wrap2 arg2 in
    let v3 = wrap3 arg3 in
    new_vtrace @@ Constructor (name, exn_id, Some (new_vtrace @@ Tuple [ v1; v2; v3 ]))
