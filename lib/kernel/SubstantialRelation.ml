module Make (S : Abstract.Storage.STORAGE) = struct
  module SI = Storage.Make (S)

  module Error = struct
    open Concepts.Condition

    let malformed_relation () =
      condition "malformed-substantial-relation"
        "The on-disk representation of a substantial relation did not conform to what was \
         expected. Is your database corrupted?"
        empty

    let malformed_tuple_key length =
      condition "malformed-tuple-key" "A tuple key did not have the expected hash size"
        ("length" |=| Concepts.Value.Integer length)

    let invalid_tuple_root root =
      condition "invalid-tuple-root"
        "The tuple-set root for a substantial relation is missing from the backend. Either your \
         storage is corrupted, or this is a bug in RNT!"
        ("hash" |=| Concepts.Value.String (Concepts.Hash.to_hum_string root))
  end

  module TupleKey = struct
    type t = Concepts.Hash.hash

    let encode = Concepts.Hash.blob_of_hash

    let decode blob =
      let raw = Concepts.Blob.bytes_of_blob blob |> Bytes.to_string in
      if String.length raw = Concepts.Hash.size then Ok (Concepts.Hash.of_raw_string raw)
      else Error (Error.malformed_tuple_key (String.length raw))

    let compare = Concepts.Hash.compare
  end

  module TupleValue = struct
    type t = Concepts.Tuple.t

    let encode = Concepts.Tuple.Representation.to_blob
    let decode = Concepts.Tuple.Representation.of_blob
  end

  module TupleSet = Merkle.Interface (S) (TupleKey) (TupleValue)

  type t = {schematics: Concepts.Hash.hash; tuples: TupleSet.address}

  module rec Representation : (Concepts.Encoding.Record.S with type t = t) =
    Concepts.Encoding.Record.Make (Body)

  and Body : Concepts.Encoding.Record.BODY = struct
    type nonrec t = t

    let tag = 'R'
    let malformed = Error.malformed_relation

    let fields {schematics; tuples} =
      let open Concepts.Encoding in
      ["schema", Value.bencode_of_hash schematics; "tuples", Value.bencode_of_hash tuples]

    let of_fields fields =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* schematics = Bencode.field "schema" fields |>> Value.hash_of_bencode in
      let* tuples = Bencode.field "tuples" fields |>> Value.hash_of_bencode in
      Ok {schematics; tuples}
  end

  let encode = Representation.to_blob
  let decode = Representation.of_blob

  let tuple_node tx relation =
    let open Utilities.Result in
    let* tuples = TupleSet.find tx relation.tuples in
    Option.to_result ~none:(Error.invalid_tuple_root relation.tuples) tuples

  let store_schema tx description =
    Concepts.Encoding.Bencode.(
      Dict
        ( BatMap.String.bindings description
        |> List.map (fun (name, {Protocols.Schematics.domain; _}) -> name, String domain) )
      |> to_blob )
    |> SI.store_blob tx

  let schema_of tx schematics =
    let open Utilities.Result in
    let* data = SI.get_req tx (S.Hash schematics) in
    let* fields = Concepts.Encoding.Bencode.of_blob data in
    let* kvs = Concepts.Encoding.Bencode.as_dict fields in
    kvs
    |> List.map (fun (name, domain) ->
        Concepts.Encoding.Bencode.as_string domain
        |> Result.map (fun domain -> name, {Protocols.Schematics.domain; provenance= []}) )
    |> Utilities.List.sequence
    |> Result.map BatMap.String.of_list

  let enumerate connection relation =
    let open Utilities.Result in
    let* tx = S.start_read connection in
    let close () = ignore (S.abort tx) in
    let* node = tuple_node tx relation |> Result.map_error (fun c -> close (); c) in
    Ok
      (Generator.cursor_of ~finally:close (fun ~yield ->
           TupleSet.iter tx (fun _ tuple -> yield tuple) node ) )

  class substantial_relation connection value description =
    object (self)
      inherit Lifecycle.null
      method to_string = "relation"
      val connection : S.connection = connection
      val relation : t = value

      method contains (tuple : Concepts.Tuple.t) =
        SI.with_read connection (fun tx ->
            let open Utilities.Result in
            let* node = tuple_node tx relation in
            TupleSet.mem tx (Concepts.Tuple.hash tuple) node )

      method modes =
        Ok
          Concepts.
            [ Mode.mode [] Cardinality.Finite;
              Mode.mode (List.map fst (BatMap.String.bindings description)) (Cardinality.bounded 1)
            ]

      method describe () = Ok (Protocols.Schematics.Relation description)
      method enumerate = enumerate connection relation

      method protocols : Protocols.Handle.protocol list =
        [ Protocols.Addressable.make self;
          Protocols.Relation.make self;
          Protocols.Enumerable.make self;
          Protocols.Schematics.make self ]

      method hash = encode relation |> Concepts.Hash.hash_of_blob
      method address = self#hash
    end

  let load connection relation =
    SI.with_read connection (fun tx -> schema_of tx relation.schematics)
    |> Result.map (fun description ->
        new substantial_relation connection relation description |> Protocols.Handle.make )

  let store tx description tuples =
    let open Utilities.Result in
    let* schematics = store_schema tx description in
    let* node =
      TupleSet.of_list tx (List.map (fun tuple -> Concepts.Tuple.hash tuple, tuple) tuples)
    in
    let relation = {schematics; tuples= TupleSet.hash_of node} in
    let* _ = SI.store_blob tx (encode relation) in
    Ok relation

  let instantiate connection ~schematics =
    let open Utilities.Result in
    let* relation =
      SI.with_transaction connection (fun tx ->
          let* tuples = TupleSet.empty_under tx in
          let relation = {schematics; tuples} in
          let* _ = SI.store_blob tx (encode relation) in
          Ok relation )
    in
    load connection relation
end
