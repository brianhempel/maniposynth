
let is_letter c =
  ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let is_number c =
  '0' <= c && c <= '9'

let is_alphanum c =
  is_letter c || is_number c
