(* A tuple of an ephemeral relation as an Erlang term in the external
   term format, for binary_to_term on the BEAM: {Type, #{Name =>
   Value}}, with the type, names and strings as binaries. And back,
   from what term_to_binary writes for such a term. *)

open Rnt

module Error = struct
  open Concepts.Condition
  let malformed () =
  Concepts.Condition.condition "malformed-beam-tuple"
    "A term is not {Type, #{Name => Value}} of binaries, and integers that fit an int"
    Concepts.Condition.empty
end

let binary buffer s =
  Buffer.add_uint8 buffer 109;
  Buffer.add_int32_be buffer (Int32.of_int (String.length s));
  Buffer.add_string buffer s

(* Every integer as a small big: a sign, then the bytes of the magnitude,
   least significant first. binary_to_term gives back an ordinary
   integer when it fits one, and lsr reads abs min_int as 2^62. *)
let integer buffer n =
  let rec digits m = if m = 0 then [] else (m land 0xff) :: digits (m lsr 8) in
  let digits = digits (abs n) in
  Buffer.add_uint8 buffer 110;
  Buffer.add_uint8 buffer (List.length digits);
  Buffer.add_uint8 buffer (if n < 0 then 1 else 0);
  List.iter (Buffer.add_uint8 buffer) digits

let encode {Concepts.Tuple.type_; attributes} =
  let buffer = Buffer.create 64 in
  Buffer.add_uint8 buffer 131;
  Buffer.add_uint8 buffer 104;
  Buffer.add_uint8 buffer 2;
  binary buffer type_;
  Buffer.add_uint8 buffer 116;
  Buffer.add_int32_be buffer (Int32.of_int (BatMap.String.cardinal attributes));
  BatMap.String.iter
    (fun name value ->
      binary buffer name;
      match value with
      | Concepts.Value.String s -> binary buffer s
      | Concepts.Value.Integer n -> integer buffer n )
    attributes;
  Buffer.contents buffer

(* Decoding raises within and answers a result at the end. *)
exception Malformed

let decode bytes =
  let position = ref 0 in
  let take n =
    if !position + n > String.length bytes then raise Malformed;
    let at = !position in
    position := at + n;
    at
  in
  let u8 () = String.get_uint8 bytes (take 1) in
  let i32 () = Int32.to_int (String.get_int32_be bytes (take 4)) in
  let u32 () = i32 () land 0xffff_ffff in
  let expect byte = if u8 () <> byte then raise Malformed in
  let binary () =
    let n = u32 () in
    String.sub bytes (take n) n
  in
  (* a sign, then at most 8 bytes of the magnitude, least significant
     first; an int holds magnitudes up to 2^62 - 1, or 2^62 when
     negative *)
  let big n =
    let negative = u8 () = 1 in
    if n > 8 then raise Malformed;
    let at = take n in
    let rec magnitude i m =
      if i < 0 then m
      else
        magnitude (i - 1)
          (Int64.logor (Int64.shift_left m 8) (Int64.of_int (String.get_uint8 bytes (at + i))))
    in
    let m = magnitude (n - 1) 0L in
    let limit = if negative then Int64.neg (Int64.of_int min_int) else Int64.of_int max_int in
    if Int64.compare m 0L < 0 || Int64.compare m limit > 0 then raise Malformed;
    Int64.to_int (if negative then Int64.neg m else m)
  in
  (* term_to_binary writes an integer in the least of these that holds it *)
  let value () =
    match u8 () with
    | 109 -> Concepts.Value.String (binary ())
    | 97 -> Concepts.Value.Integer (u8 ())
    | 98 -> Concepts.Value.Integer (i32 ())
    | 110 -> Concepts.Value.Integer (big (u8 ()))
    | _ -> raise Malformed
  in
  let rec attributes n map =
    if n = 0 then map
    else begin
      expect 109;
      let name = binary () in
      let value = value () in
      attributes (n - 1) (BatMap.String.add name value map)
    end
  in
  match
    expect 131;
    expect 104;
    expect 2;
    expect 109;
    let type_ = binary () in
    expect 116;
    let attributes = attributes (u32 ()) BatMap.String.empty in
    if !position <> String.length bytes then raise Malformed;
    {Concepts.Tuple.type_; attributes}
  with
  | tuple -> Ok tuple
  | exception Malformed -> Error (Error.malformed ())
