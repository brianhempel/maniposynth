
module IMap = Map.Make (struct type t = int let compare : int -> int -> int = compare end) (* https://stackoverflow.com/questions/10131779/ocaml-map-of-int-keys-where-is-the-simple-int-module-to-use-with-the-map-ma/10132568#comment13019626_10132568 *)

module Entry = struct
  type t = (Location.t * int * Data.value) (* (ast id, frame_no, value) *)

  let loc (loc, _, _)           = loc
  let frame_no (_, frame_no, _) = frame_no
  let value (_, _, value)       = value
end

type t = Entry.t IMap.t
let empty = IMap.empty

let add entry trace =
  let counter = if IMap.is_empty trace then 0 else IMap.max_binding trace |> fst in
  IMap.add (counter + 1) entry trace

let entries_for_loc loc trace =
  let finder _ entry results =
    if Entry.loc entry = loc then begin
      entry :: results
    end else
      results
  in
  IMap.fold finder trace []
