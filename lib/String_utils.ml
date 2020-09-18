open String

(* Like String.sub but does not error for ranges outside the string. *)
let safe_sub str i len =
  let safe_i = Utils.clamp 0 (String.length str) i in
  let safe_j = Utils.clamp 0 (String.length str) (i + len) in
  sub str safe_i (safe_j - safe_i)

let prefix str len =
  safe_sub str 0 len

let suffix str len =
  safe_sub str (length str - len) len

let drop str len =
  suffix str (length str - len)

(* Tail recursive string matcher to see if target containts str at the given indices. *)
let rec matches_at_indices_ str str_i target target_i target_len =
  if target_i >= target_len then
    true
  else if unsafe_get str str_i = unsafe_get target target_i then
    matches_at_indices_ str (str_i + 1) target (target_i + 1) target_len
  else
    false

let matches_at_index str str_i target =
  let str_len    = length str in
  let target_len = length target in
  if str_i < 0 || str_i > str_len - target_len then
    false
  else
    matches_at_indices_ str str_i target 0 target_len

let starts_with str target =
  matches_at_index str 0 target

let ends_with str target =
  let str_len    = length str in
  let target_len = length target in
  matches_at_index str  (str_len - target_len) target

let find_index ?(start_index = 0) str target : int option =
  let target_len = length target in
  let last_i     = length str - target_len in
  let rec loop i =
    if i > last_i then
      None
    else if matches_at_indices_ str i target 0 target_len then
      Some i
    else
      loop (i + 1)
  in
  if last_i < 0 then
    None
  else
    loop start_index

let rec split ?(limit = -1) ?(start_index = 0) str sep =
  if limit = 1 then 
    [sub str start_index (length str - start_index)]
  else
    match find_index ~start_index str sep with
    | Some i ->
        sub str start_index (i - start_index)
        :: split ~limit:(limit - 1) ~start_index:(i + length sep) str sep
    | None ->
        [sub str start_index (length str - start_index)]

let replace str ~target ~replacement =
  split str target |> String.concat replacement

(* "a b-c d'" => "a_b_c_d_" *)
let parameterize = map (fun c -> if Char_utils.is_alphanum c then c else '_')