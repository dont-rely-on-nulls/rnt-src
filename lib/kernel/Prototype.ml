let mixture ps =
  Protocols.Handle.make
  @@ object
       inherit Lifecycle.null
       inherit Identity.of_id (* Should we allow the user to override this? *)
       method protocols = ps
       method to_string = "mixture"
     end

let rec mixture_of value f = mixture (f (fun value' -> mixture_of value' f) value)

module Error = struct
  open Concepts.Condition

  let invalid_property key =
    condition "invalid-property"
      "The specified key does not correspond to any property of the object"
      ("key" |=| Concepts.Value.String key)

  let deletion_not_supported () =
    condition "deletion-not-supported" "Attempting to delete an object property" empty
end

module Addressable = struct
  module OfTree (S : Abstract.Storage.STORAGE) (K : Merkle.KEY) = struct
    module Tree = Merkle.Make (S) (K)

    let make ~node =
      Protocols.Addressable.make
      @@ object
           method address = Tree.hash_of node
         end
  end
end

module Associative = struct
  let of_properties props =
    Protocols.Associative.make
    @@ object
         val props = BatList.to_seq props |> BatMap.of_seq

         method update key value =
           match BatMap.find_opt key props with
           | None -> Error (Error.invalid_property key)
           | Some f -> f value
       end

  let update_only f = function None -> Error (Error.deletion_not_supported ()) | Some x -> f x

  type 'tx admission = 'tx -> (Concepts.Hash.hash, Concepts.Condition.condition) result

  (* A value with no address yet is [admit]ted: it is read here, before
     the write begins, since reading it may itself need storage, and
     stored by the write. *)
  let admission admit key h =
    match Protocols.Addressable.from h with
    | Some a ->
        let addr = Protocols.Addressable.address a in
        Ok (fun _ -> Ok addr)
    | None -> admit key h

  module OfTree (S : Abstract.Storage.STORAGE) (K : Merkle.KEY with type t = string) = struct
    module Tree = Merkle.Make (S) (K)
    module SI = Storage.Make (S)

    let make ~admit ~storage ~constructor ~node =
      Protocols.Associative.make
      @@ object
           method update key value =
             let open Utilities.Result in
             let* store =
               match value with
               | None -> Ok None
               | Some h -> admission admit key h |> Result.map Option.some
             in
             SI.with_transaction storage (fun tx ->
                 let* node' =
                   match store with
                   | None -> Tree.remove tx key node
                   | Some store ->
                       let* addr = store tx in
                       Tree.insert tx key addr node
                 in
                 constructor node' )
         end
  end
end

module Directory = struct
  let of_properties props =
    Protocols.Directory.make
    @@ object
         val props = BatList.to_seq props |> BatMap.of_seq
         method list = Ok (BatMap.keys props |> BatFingerTree.of_enum)
         method find k = Ok (BatMap.find_opt k props)
       end

  let children directory =
    let open Utilities.Result in
    let* listing = Protocols.Handle.require Protocols.Directory.from directory in
    let* names = Protocols.Directory.list listing in
    BatFingerTree.to_list names
    |> List.map (fun name ->
        let* found = Protocols.Directory.find listing name in
        Ok (Option.map (fun child -> name, child) found) )
    |> Utilities.List.sequence
    |> Result.map (List.filter_map Fun.id)

  module OfTree
      (S : Abstract.Storage.STORAGE)
      (K : Merkle.KEY with type t = string)
      (V : Merkle.VALUE) =
  struct
    module Tree = Merkle.Interface (S) (K) (V)
    module SI = Storage.Make (S)

    let make ~storage ~constructor ~node =
      Protocols.Directory.make
      @@ object
           method list = SI.with_read storage (Fun.flip Tree.keys node)

           method find k =
             let open Utilities.Result in
             SI.with_read storage (fun tx -> Tree.lookup tx k node)
             |>> (function
               | None -> Ok None
               | Some x -> constructor x |> Result.map Option.some )
         end
  end
end
