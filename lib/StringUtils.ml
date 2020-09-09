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

let starts_with str target =
  equal target (prefix str (length target)) 

let ends_with str target =
  equal target (suffix str (length target)) 
