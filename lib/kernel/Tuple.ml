module Make (S : Abstract.Storage.STORAGE) = struct
  module SI = Storage.Make (S)

  module Error = struct
    open Concepts.Condition

    let unknown_attribute name =
      condition "unknown-attribute" "No such attribute on this tuple"
        ("attribute" |=| Concepts.Value.String name)

    let malformed_value () =
      condition "malformed-tuple-value" "A tuple field did not conform to what was expected" empty

    let incomplete_tuple addr =
      condition "incomplete-tuple"
        "A stored tuple is missing part of its expected structure. Is your storage corrupted?"
        ("address" |=| Concepts.Value.String (Concepts.Hash.to_hum_string addr))
  end

  module Attribute = struct
    type t = Concepts.Value.value

    let malformed_value = Error.malformed_value

    let encode value =
      let open Concepts.Encoding in
      Bencode.to_blob
        ( match value with
        | Concepts.Value.String s -> Bencode.Tagged ('s', Bencode.String s)
        | Concepts.Value.Integer n -> Bencode.Tagged ('i', Bencode.Int n) )

    let decode blob =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* data = Bencode.of_blob blob in
      match data with
      | Bencode.Tagged ('s', Bencode.String s) -> Ok (Concepts.Value.String s)
      | Bencode.Tagged ('i', Bencode.Int n) -> Ok (Concepts.Value.Integer n)
      | _ -> Error (malformed_value ())

    let domain = function
      | Concepts.Value.String _ -> "string"
      | Concepts.Value.Integer _ -> "integer"
  end

  module AttributeM = Merkle.Interface (S) (Merkle.StringKey) (Attribute)

  (* TODO: ephemeral tuples are served by instantiating this functor
     over an in-memory storage. Consider later splitting [t] into
     resident (an address) and ephemeral (an in-memory attribute map)
     forms instead. *)
  type t = {type_: string; attributes: AttributeM.address}

  module rec Representation : (Concepts.Encoding.Record.S with type t = t) =
    Concepts.Encoding.Record.Make (Body)

  and Body : Concepts.Encoding.Record.BODY = struct
    type nonrec t = t

    let tag = 'T'
    let malformed = Error.malformed_value

    let fields {type_; attributes} =
      let open Concepts.Encoding in
      ["type", Bencode.String type_; "attributes", Value.bencode_of_hash attributes]

    let of_fields data =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* type_ = Bencode.field "type" data |>> Bencode.as_string in
      let* attributes = Bencode.field "attributes" data |>> Value.hash_of_bencode in
      Ok {type_; attributes}
  end

  let encode = Representation.to_blob
  let decode = Representation.of_blob
  let hash tuple = Representation.to_blob tuple |> Concepts.Hash.hash_of_blob
  let type_of {type_; _} = type_

  let node tx {attributes; _} =
    let open Utilities.Result in
    AttributeM.find tx attributes |>> Option.to_result ~none:(Error.incomplete_tuple attributes)

  let empty tx ~type_ () =
    let open Utilities.Result in
    let* attributes = AttributeM.empty_under tx in
    Ok {type_; attributes}

  let make tx ~type_ attributes =
    let open Utilities.Result in
    let* node = AttributeM.of_list tx (BatMap.String.bindings attributes) in
    Ok {type_; attributes= AttributeM.hash_of node}

  let attribute tx tuple name =
    let open Utilities.Result in
    let* node = node tx tuple in
    let* value = AttributeM.lookup tx name node in
    Option.to_result ~none:(Error.unknown_attribute name) value

  let attributes tx tuple =
    let open Utilities.Result in
    let* node = node tx tuple in
    AttributeM.fold_left tx
      (fun acc name value -> BatMap.String.add name value acc)
      BatMap.String.empty node

  class tuple ~relation conn value node =
    object (self)
      inherit Lifecycle.null
      method to_string = "tuple"
      val tuple = value
      val storage = conn
      val node = node

      method describe () =
        let open Utilities.Result in
        let* attributes =
          SI.with_transaction storage (fun tx ->
              AttributeM.fold_left tx
                (fun acc name value -> BatMap.String.add name (Attribute.domain value) acc)
                BatMap.String.empty node )
        in
        Ok (Protocols.Schematics.Tuple {Protocols.Schematics.relation; attributes})

      method protocols : Protocols.Handle.protocol list = [Protocols.Schematics.make self]
      method hash = hash tuple
    end

  let wrap ~relation conn value =
    let open Utilities.Result in
    let* node = SI.with_transaction conn (fun tx -> node tx value) in
    new tuple ~relation conn value node |> Protocols.Handle.make |> Result.ok
end
