type t = {type_: string; attributes: Value.value BatMap.String.t}

let malformed_value () =
  Condition.condition "malformed-tuple-value" "A tuple field did not conform to what was expected"
    Condition.empty

let bencode_of_value = function
  | Value.String s -> Encoding.Bencode.Tagged ('s', Encoding.Bencode.String s)
  | Value.Integer n -> Encoding.Bencode.Tagged ('i', Encoding.Bencode.Int n)

let value_of_bencode = function
  | Encoding.Bencode.Tagged ('s', Encoding.Bencode.String s) -> Ok (Value.String s)
  | Encoding.Bencode.Tagged ('i', Encoding.Bencode.Int n) -> Ok (Value.Integer n)
  | _ -> Error (malformed_value ())

module rec Representation : (Encoding.Record.S with type t = t) = Encoding.Record.Make (Body)

and Body : Encoding.Record.BODY = struct
  type nonrec t = t

  let tag = 'T'
  let malformed = malformed_value

  let fields {type_; attributes} =
    [ "type", Encoding.Bencode.String type_;
      ( "attributes",
        Encoding.Bencode.Dict
          ( BatMap.String.enum attributes
          |> BatEnum.fold (fun acc (name, value) -> (name, bencode_of_value value) :: acc) [] ) ) ]

  let of_fields data =
    let open Utilities.Result in
    let* type_ = Encoding.Bencode.field "type" data |>> Encoding.Bencode.as_string in
    let* kvs = Encoding.Bencode.field "attributes" data |>> Encoding.Bencode.as_dict in
    kvs
    |> List.map (fun (name, v) -> value_of_bencode v |> Result.map (fun v -> name, v))
    |> Utilities.List.sequence
    |> Result.map (fun kvs -> {type_; attributes= BatMap.String.of_list kvs})
end

let hash tuple = Representation.to_blob tuple |> Hash.hash_of_blob

let to_string {attributes; _} =
  BatMap.String.bindings attributes
  |> List.map (fun (a, v) -> a ^ "=" ^ Value.to_string v)
  |> String.concat " "
