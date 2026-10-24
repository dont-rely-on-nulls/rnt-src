module Make (S : Abstract.Storage.STORAGE) = struct
  (* A branch state holds its multigroups and a backlink to the state it
     succeeded, each multigroup its relations:

     \system\branch\master\multigroup\universe\relation\planet
     \system\branch\master\previous\multigroup\universe\relation\planet
   *)

  module SI = Storage.Make (S)
  module M = Multigroup.Make (S)
  module MultigroupM = Merkle.Interface (S) (Merkle.StringKey) (M)
  module MMDirectory = Prototype.Directory.OfTree (S) (Merkle.StringKey) (M)
  module MMAssociative = Prototype.Associative.OfTree (S) (Merkle.StringKey)
  module MMAddressable = Prototype.Addressable.OfTree (S) (Merkle.StringKey)

  module Error = struct
    open Concepts.Condition

    let incomplete_branch addr =
      condition "incomplete-branch"
        "A stored branch is missing part of its expected structure. Is your storage corrupted?"
        ("address" |=| Concepts.Value.String (Concepts.Hash.to_hum_string addr))
  end

  type t = {multigroups: MultigroupM.address; previous: t SI.Pointer.t option}

  module rec Representation : (Concepts.Encoding.Record.S with type t = t) =
    Concepts.Encoding.Record.Make (Body)

  and Body : Concepts.Encoding.Record.BODY = struct
    type nonrec t = t

    let tag = 'Y'

    let malformed () =
      Concepts.Condition.(
        condition "malformed-branch"
          "The on-disk representation of a branch did not conform to what was expected. Is your \
           database corrupted?"
          empty )

    let fields {multigroups; previous} =
      let open Concepts.Encoding in
      [ "multigroups", Value.bencode_of_hash multigroups;
        ( "previous",
          Value.bencode_of_option
            (fun v -> SI.Pointer.address_of v |> SI.as_hash |> Value.bencode_of_hash)
            previous ) ]

    let of_fields fields =
      let open Utilities.Result in
      let open Concepts.Encoding in
      let* multigroups = Bencode.field "multigroups" fields |>> Value.hash_of_bencode in
      let* previous =
        Bencode.field "previous" fields
        |>> Value.option_of_bencode (fun v ->
            Value.hash_of_bencode v
            |> Result.map (fun hash -> S.Hash hash)
            |> Result.map (SI.Pointer.make Loader.load) )
      in
      Ok {multigroups; previous}
  end

  and Loader : sig
    val load : S.transaction -> S.address -> (t, Concepts.Condition.condition) result
  end = struct
    let load tx addr = Utilities.Result.(SI.get_req tx addr |>> Representation.of_blob)
  end

  let pointer_of hash = SI.Pointer.make Loader.load (S.Hash hash)

  let node_of tx branch =
    let open Utilities.Result in
    MultigroupM.find tx branch.multigroups
    |>> Option.to_result ~none:(Error.incomplete_branch branch.multigroups)

  (* Given [root], the stored programs of this state run through the
     evaluators registered under it, against this very state, so an
     earlier state reads as it was. *)
  class branch ?root storage value node =
    object (self)
      inherit Lifecycle.null
      method to_string = "branch"
      val storage : S.connection = storage
      val branch : t = value
      val node = node (* FIXME: can we not place this inside `t`? *)

      method deriving branch' =
        let open Utilities.Result in
        let branch'' = {branch' with previous= self#address |> pointer_of |> Option.some} in
        let* node' =
          SI.with_transaction storage (fun tx ->
              let* _ = SI.store_blob tx (Representation.to_blob branch'') in
              node_of tx branch' )
        in
        new branch ?root storage branch'' node' |> Protocols.Handle.make |> Result.ok

      method private previous =
        match branch.previous with
        | None -> Ok None
        | Some pointer ->
            SI.with_read storage (fun tx ->
                let open Utilities.Result in
                let* previous = SI.Pointer.deref tx pointer in
                let* node = node_of tx previous in
                Ok (Some (Protocols.Handle.make {<branch = previous; node>})) )

      method protocols : Protocols.Handle.protocol list =
        let bind =
          Option.map (fun root -> {EphemeralRelation.root; within= Protocols.Handle.make {<>}}) root
        in
        let multigroups =
          Prototype.mixture_of node (fun make node ->
              [ MMAddressable.make ~node:(MultigroupM.into node);
                MMDirectory.make ~storage ~node ~constructor:(M.load ?bind storage);
                MMAssociative.make ~admit:M.admit ~storage ~node:(MultigroupM.into node)
                  ~constructor:(fun node' -> MultigroupM.from node' |> make |> Result.ok ) ] )
        in
        let open Utilities.Result in
        let admits (m, multigroup) =
          Protocols.Handle.releasing multigroup (fun () ->
              let* admission = Protocols.Admission.require multigroup in
              let* violations = Protocols.Admission.check admission in
              Ok
                (List.map
                   (fun (d, witness) ->
                     Path.(to_string ("multigroup" @/ m @/ "denial" @/ d @/ this)), witness )
                   violations ) )
        in
        Protocols.
          [ Addressable.make self;
            Admission.make
              object
                method check =
                  let* named = Directory.children multigroups in
                  Utilities.List.concat_map admits named
              end;
            Prototype.Associative.(
              of_properties
                [ ( "multigroup",
                    update_only (fun node' ->
                        Handle.require Addressable.from node'
                        |> Result.map Addressable.address
                        |>> fun addr -> self#deriving {branch with multigroups= addr} ) ) ] );
            Prototype.Directory.of_properties'
              [ ("multigroup", fun () -> Ok (Some multigroups));
                ("previous", fun () -> self#previous) ] ]

      method hash = Representation.to_blob branch |> Concepts.Hash.hash_of_blob
      method address = self#hash
    end

  let load ?root tx conn addr =
    let open Utilities.Result in
    let* data = SI.get_req tx (S.Hash addr) in
    let* branch = Representation.of_blob data in
    let* node = node_of tx branch in
    Ok (new branch ?root conn branch node |> Protocols.Handle.make)

  let make conn =
    let open Utilities.Result in
    SI.with_transaction conn (fun tx ->
        let* empty = MultigroupM.empty_under tx in
        let branch = {multigroups= empty; previous= None} in
        let* _ = SI.store_blob tx (Representation.to_blob branch) in
        Ok (new branch conn branch MultigroupM.empty |> Protocols.Handle.make) )
end
