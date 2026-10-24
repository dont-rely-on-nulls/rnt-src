module Make (S : Abstract.Storage.STORAGE) = struct
  module SI = Storage.Make (S)
  module R = SubstantialRelation.Make (S)
  module E = EphemeralRelation.Make (S)

  (* A relation as a multigroup holds it. *)
  module Entry = struct
    module Stored = EphemeralRelation.Persisted.Representation

    type t = Substantial of R.t | Ephemeral of EphemeralRelation.Persisted.t

    let encode = function
      | Substantial relation -> R.encode relation
      | Ephemeral relation -> Stored.to_blob relation

    let decode blob =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* data = Bencode.of_blob blob in
      match data with
      | Bencode.Tagged (tag, _) when Char.equal tag Stored.tag ->
          Stored.of_bencode data |> Result.map (fun relation -> Ephemeral relation)
      | _ -> R.Representation.of_bencode data |> Result.map (fun relation -> Substantial relation)

    let load ?bind storage = function
      | Substantial relation -> R.load storage relation
      | Ephemeral relation -> E.load ?bind storage relation

    (* A program is stored as itself, to run whenever it is read; any
       other relation is stored as the tuples it holds now. *)
    let admit name h =
      let open Utilities.Result in
      let address entry = Concepts.Hash.hash_of_blob (encode entry) in
      match Program.image h with
      | Some {evaluator; source; _} ->
          let* description = Protocols.Relation.heading h in
          Ok
            (fun tx ->
              let* record = E.store tx ~name ~evaluator ~source description in
              Ok (address (Ephemeral record)) )
      | None ->
          let* description, tuples = Protocols.Relation.read h in
          Ok
            (fun tx ->
              let* relation = R.store tx description tuples in
              Ok (address (Substantial relation)) )
  end

  (* A schema is only a name: \schema\[s] is the tree of its relations,
     with no record of its own. *)
  module T = Merkle.Make (S) (Merkle.StringKey)
  module RelationM = Merkle.Interface (S) (Merkle.StringKey) (Entry)
  module TAddressable = Prototype.Addressable.OfTree (S) (Merkle.StringKey)
  module TAssociative = Prototype.Associative.OfTree (S) (Merkle.StringKey)
  module RMDirectory = Prototype.Directory.OfTree (S) (Merkle.StringKey) (Entry)

  type t = {schemas: T.address; denials: T.address}

  module Error = struct
    open Concepts.Condition

    let malformed_multigroup () =
      condition "malformed-multigroup"
        "The on-disk representation of a multigroup did not conform to what was expected. Is your \
         database corrupted?"
        empty

    let incomplete addr =
      condition "incomplete-multigroup"
        "A stored multigroup is missing part of its expected structure. Is your storage corrupted?"
        ("address" |=| Concepts.Value.String (Concepts.Hash.to_hum_string addr))

    let unjudgeable denial =
      condition "unjudgeable-denial"
        "A denial does not declare that reading it with nothing bound ends, so the state cannot be \
         judged"
        ("denial" |=| Concepts.Value.String denial)
  end

  module Representation = Concepts.Encoding.Record.Make (struct
    type nonrec t = t

    let tag = '*'
    let malformed = Error.malformed_multigroup

    let fields {schemas; denials} =
      let open Concepts.Encoding in
      ["schemas", Value.bencode_of_hash schemas; "denials", Value.bencode_of_hash denials]

    let of_fields fields =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* schemas = Bencode.field "schemas" fields |>> Value.hash_of_bencode in
      let* denials = Bencode.field "denials" fields |>> Value.hash_of_bencode in
      Ok {schemas; denials}
  end)

  let encode = Representation.to_blob
  let decode = Representation.of_blob

  let node_of tx addr =
    let open Utilities.Result in
    T.find tx addr |>> Option.to_result ~none:(Error.incomplete addr)

  (* What [h] holds under [property], each to store once the write has
     begun, and the tree they make when it has. *)
  let admissions property admit h =
    let open Utilities.Result in
    let* listing = Protocols.Handle.require Protocols.Directory.from h in
    let* found = Protocols.Directory.find listing property in
    let* children = Option.fold ~none:(Ok []) ~some:Protocols.Directory.children found in
    List.map
      (fun (name, child) ->
        Prototype.Associative.admission admit name child |> Result.map (fun p -> name, p) )
      children
    |> Utilities.List.sequence

  let tree_of tx admissions =
    let open Utilities.Result in
    List.map (fun (name, store) -> store tx |> Result.map (fun addr -> name, addr)) admissions
    |> Utilities.List.sequence
    |>> T.of_list tx

  let admit_schema _ h =
    let open Utilities.Result in
    let* relations = admissions "relation" Entry.admit h in
    Ok (fun tx -> Result.map T.hash_of (tree_of tx relations))

  let relations ?bind storage node =
    Prototype.mixture_of node (fun make node ->
        [ TAddressable.make ~node;
          RMDirectory.make ~storage ~node:(RelationM.from node)
            ~constructor:(Entry.load ?bind storage);
          TAssociative.make ~admit:Entry.admit ~storage ~node ~constructor:(fun node' ->
              Ok (make node') ) ] )

  let rec schema ?bind storage node =
    let open Utilities.Result in
    Prototype.mixture
      [ TAddressable.make ~node;
        Prototype.Directory.of_properties ["relation", relations ?bind storage node];
        Prototype.Associative.(
          of_properties
            [ ( "relation",
                update_only (fun relations' ->
                    let* a = Protocols.Handle.require Protocols.Addressable.from relations' in
                    let* node' =
                      SI.with_read storage (fun tx -> node_of tx (Protocols.Addressable.address a))
                    in
                    Ok (schema ?bind storage node') ) ) ] ) ]

  let schemas ?bind storage node =
    Prototype.mixture_of node (fun make node ->
        [ TAddressable.make ~node;
          Protocols.Directory.make
            object
              method list = SI.with_read storage (Fun.flip T.keys node)

              method find name =
                let open Utilities.Result in
                SI.with_read storage (fun tx ->
                    let* found = T.lookup tx name node in
                    match found with
                    | None -> Ok None
                    | Some addr ->
                        let* relations = node_of tx addr in
                        Ok (Some (schema ?bind storage relations)) )
            end;
          TAssociative.make ~admit:admit_schema ~storage ~node ~constructor:(fun node' ->
              Ok (make node') ) ] )

  let trees tx {schemas; denials} =
    let open Utilities.Result in
    let* schemas = node_of tx schemas in
    let* denials = node_of tx denials in
    Ok (schemas, denials)

  let through_program ?bind relation f =
    let open Utilities.Result in
    match Program.image relation, bind with
    | Some _, Some {EphemeralRelation.within; _} ->
        let* executable = Protocols.Executable.require relation in
        let* result = Protocols.Executable.invoke executable [] ~within in
        Protocols.Handle.releasing result (fun () -> f result)
    | _ -> f relation

  let held ?bind (name, relation) =
    let open Utilities.Result in
    Protocols.Handle.releasing relation (fun () ->
        through_program ?bind relation (fun relation ->
            let* denial = Protocols.Relation.require relation in
            let* modes = Protocols.Relation.modes denial in
            if not (Concepts.Mode.exhaustible modes BatSet.String.empty) then
              Error (Error.unjudgeable name)
            else
              let* first = Protocols.Enumerable.scan relation Protocols.Cursor.next in
              Ok (Option.to_list (Option.map (fun witness -> name, witness) first)) ) )

  class multigroup ?bind conn value schema_tree denial_tree =
    object (self)
      inherit Lifecycle.null
      method to_string = "multigroup"
      val multigroup = value
      val storage = conn
      val schema_tree = schema_tree (* FIXME: see the comment on Branch.ml *)
      val denial_tree = denial_tree

      (* TODO: Add later to the lifecycle management, accounting for
         derived instances. Callers must release the previous handle
         when done with it so its instance can be cleaned up after the
         last reference is released. *)
      method deriving multigroup' =
        let open Utilities.Result in
        let* schemas', denials' =
          SI.with_transaction storage (fun tx ->
              let* _ = SI.store_blob tx (encode multigroup') in
              trees tx multigroup' )
        in
        new multigroup ?bind storage multigroup' schemas' denials'
        |> Protocols.Handle.make
        |> Result.ok

      method check =
        let open Utilities.Result in
        let* named = Protocols.Directory.children (relations ?bind storage denial_tree) in
        Utilities.List.concat_map (held ?bind) named

      method protocols : Protocols.Handle.protocol list =
        let open Utilities.Result in
        let derive f node' =
          Protocols.Handle.require Protocols.Addressable.from node'
          |> Result.map Protocols.Addressable.address
          |>> fun addr -> self#deriving (f addr)
        in
        Protocols.
          [ Addressable.make self;
            Admission.make self;
            Prototype.Associative.(
              of_properties
                [ "schema", update_only (derive (fun addr -> {multigroup with schemas= addr}));
                  "denial", update_only (derive (fun addr -> {multigroup with denials= addr})) ] );
            Prototype.Directory.of_properties
              [ "schema", schemas ?bind storage schema_tree;
                "denial", relations ?bind storage denial_tree ] ]

      method hash = encode multigroup |> Concepts.Hash.hash_of_blob
      method address = self#hash
    end

  let load ?bind conn value =
    let open Utilities.Result in
    let* schemas, denials = SI.with_read conn (fun tx -> trees tx value) in
    new multigroup ?bind conn value schemas denials |> Protocols.Handle.make |> Result.ok

  let make conn =
    let open Utilities.Result in
    SI.with_transaction conn (fun tx ->
        let* empty = T.empty_under tx in
        let multigroup = {schemas= empty; denials= empty} in
        let* _ = SI.store_blob tx (encode multigroup) in
        new multigroup conn multigroup T.empty T.empty |> Protocols.Handle.make |> Result.ok )

  (* Handed over as the tree shows one, a directory holding its schemas
     under \schema and its denials under \denial, a multigroup not stored
     yet is stored with them. *)
  let admit _ h =
    let open Utilities.Result in
    let* schemas = admissions "schema" admit_schema h in
    let* denials = admissions "denial" Entry.admit h in
    Ok
      (fun tx ->
        let* schemas = tree_of tx schemas in
        let* denials = tree_of tx denials in
        SI.store_blob tx (encode {schemas= T.hash_of schemas; denials= T.hash_of denials}) )
end
