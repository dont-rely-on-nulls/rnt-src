module type VALUE = sig
  type t

  val encode : t -> Concepts.Blob.t
  val decode : Concepts.Blob.t -> (t, Concepts.Condition.condition) result
end

module type KEY = sig
  include VALUE

  val compare : t -> t -> Utilities.Ordering.t
end

module type TREE = functor (S : Abstract.Storage.STORAGE) (K : KEY) -> sig
  type address = Concepts.Hash.hash
  type node

  val with_batch :
    S.transaction ->
    (unit -> (node, Concepts.Condition.condition) result) ->
    (node, Concepts.Condition.condition) result

  val find : S.transaction -> address -> (node option, Concepts.Condition.condition) result
  val persist : S.transaction -> node -> (address, Concepts.Condition.condition) result
  val empty : node
  val empty_under : S.transaction -> (address, Concepts.Condition.condition) result
  val hash_of : node -> address

  val insert :
    S.transaction -> K.t -> address -> node -> (node, Concepts.Condition.condition) result

  val of_list : S.transaction -> (K.t * address) list -> (node, Concepts.Condition.condition) result
  val of_finger_tree : S.transaction -> (K.t * address) BatFingerTree.t -> (node, Concepts.Condition.condition) result
  val remove : S.transaction -> K.t -> node -> (node, Concepts.Condition.condition) result
  val lookup : S.transaction -> K.t -> node -> (address option, Concepts.Condition.condition) result

  val fold_left :
    S.transaction ->
    ('c -> K.t -> address -> 'c) ->
    'c ->
    node ->
    ('c, Concepts.Condition.condition) result

  val keys : S.transaction -> node -> (K.t BatFingerTree.t, Concepts.Condition.condition) result
end

module Make : TREE =
functor
  (S : Abstract.Storage.STORAGE)
  (K : KEY)
  ->
  struct
    type address = Concepts.Hash.hash

    module Error = struct
      open Concepts.Condition

      let malformed_node () =
        condition "malformed-node" "A node representation did not conform to what was expected"
          empty
    end

    type node =
      | Leaf of {keys: K.t BatFingerTree.t; values: address BatFingerTree.t}
      | Trunk of {keys: K.t BatFingerTree.t; children: address BatFingerTree.t}

    let empty = Leaf {keys= BatFingerTree.empty; values= BatFingerTree.empty}

    let rec lookup1' keys key bottom top =
      let open Utilities.Ordering in
      if bottom >= top then bottom, false
      else
        let mid = bottom + ((top - bottom) / 2) in
        let node = BatFingerTree.get keys mid in
        match K.compare node key with
        | Equal -> mid, true
        | Greater -> lookup1' keys key bottom mid
        | Smaller -> lookup1' keys key (mid + 1) top

    let lookup1 keys key = lookup1' keys key 0 (BatFingerTree.size keys)
    let keys_of = function Leaf {keys; _} -> keys | Trunk {keys; _} -> keys

    let of_bencode =
      let open Concepts.Encoding.Bencode in
      let open Utilities.Result in
      (* This is terrible *)
      let decode_key t =
        as_string t
        |> Result.map String.to_bytes
        |> Result.map Concepts.Blob.blob_of_bytes
        |>> K.decode
      in
      let decode_value t = as_string t |> Result.map Concepts.Hash.of_raw_string in
      let decode_list f data =
        data
        |>> as_list
        |> Result.map (List.map f)
        |>> Utilities.List.sequence
        |> Result.map BatFingerTree.of_list
      in
      function
      | Tagged ('!', (Dict _ as data)) ->
          let* keys = field "keys" data |> decode_list decode_key in
          let* values = field "values" data |> decode_list decode_value in
          Ok (Leaf {keys; values})
      | Tagged ('#', (Dict _ as data)) ->
          let* keys = field "keys" data |> decode_list decode_key in
          let* children = field "children" data |> decode_list decode_value in
          Ok (Trunk {keys; children})
      | _ -> Error (Error.malformed_node ())

    let from_blob blob = Utilities.Result.(Concepts.Encoding.Bencode.of_blob blob |>> of_bencode)

    let to_bencode =
      let open Concepts.Encoding.Bencode in
      (* Ditto. *)
      let bencode_key k =
        K.encode k |> Concepts.Blob.bytes_of_blob |> String.of_bytes |> fun s -> String s
      in
      let bencode_hash h = String (Concepts.Hash.to_raw_string h) in
      function
      | Leaf {keys; values} ->
          Tagged
            ( '!',
              Dict
                [ "keys", List (BatFingerTree.to_list keys |> List.map bencode_key);
                  "values", List (BatFingerTree.to_list values |> List.map bencode_hash) ] )
      | Trunk {keys; children} ->
          Tagged
            ( '#',
              Dict
                [ "keys", List (BatFingerTree.to_list keys |> List.map bencode_key);
                  "children", List (BatFingerTree.to_list children |> List.map bencode_hash) ] )

    let to_blob node = to_bencode node |> Concepts.Encoding.Bencode.to_blob

    (* TODO: we should probably cache this inside the node itself rather
     than recalculating it every time. We could also allow the user to
     create "uninterned" nodes that are not storage-backed, that could
     be used for intermediates and the like. *)
    let hash_of node = to_blob node |> Concepts.Hash.hash_of_blob

    type _ Effect.t +=
      | Intern : (address * node * Concepts.Blob.t) -> unit Effect.t
      | Retrieve : address -> (node * Concepts.Blob.t) option Effect.t

    let rec flush tx buffer addr =
      let open Utilities.Result in
      match BatMap.find_opt addr buffer with
      | None -> Ok ()
      | Some (node, data) -> (
          let* _ = S.put tx (S.Hash addr) data in
          match node with
          | Leaf _ -> Ok ()
          | Trunk {children; _} ->
              BatFingerTree.map (fun addr -> flush tx buffer addr) children
              |> Utilities.FingerTree.sequence
              |> Result.map ignore )

    let with_batch tx f =
      let open Utilities.Result in
      let buffer = ref BatMap.empty in
      try
        let* node = f () in
        let* _ = flush tx !buffer (hash_of node) in
        Ok node
      with
      | effect Intern (addr, node, data), k ->
          buffer := BatMap.add addr (node, data) !buffer;
          Effect.Deep.continue k ()
      | effect Retrieve addr, k -> Effect.Deep.continue k (BatMap.find_opt addr !buffer)

    let find tx addr =
      let open Utilities.Result in
      try Effect.perform (Retrieve addr) |> Option.map fst |> Result.ok
      with Effect.Unhandled _ -> (
        let* data = S.get tx (S.Hash addr) in
        match data with
        | None -> Ok None
        | Some data ->
            let* node = from_blob data in
            Ok (Some node) )

    let persist tx node =
      let data = to_blob node in
      let addr = Concepts.Hash.hash_of_blob data in
      begin try Ok (Effect.perform (Intern (addr, node, data)))
      with Effect.Unhandled _ -> S.put tx (S.Hash addr) data
      end
      |> Result.map (fun () -> addr)

    let find' tx addr =
      let open Utilities.Result in
      let* child = find tx addr in
      match child with
      | Some child -> Ok child
      | None ->
          failwith
            "A child node was not found on the underlying storage. Either your database is \
             corrupted, or this is a bug on RNT!"

    let rec lookup tx key node =
      let open Utilities.Result in
      let i, found = lookup1 (keys_of node) key in
      match node with
      | Leaf {values; _} -> if found then Ok (Some (BatFingerTree.get values i)) else Ok None
      | Trunk {children; _} ->
          let* child = BatFingerTree.get children (if found then i + 1 else i) |> find' tx in
          lookup tx key child

    let empty_under tx = persist tx empty

    type op = Update of address * node | Split of address * K.t * address

    let emplace i v ft =
      let size = BatFingerTree.size ft in
      if i < 0 || i > size then invalid_arg "Merkle.emplace: index out of bounds"
      else if size = 0 then BatFingerTree.singleton v
      else if i = size then BatFingerTree.snoc ft v
      else
        let fl, fr = BatFingerTree.split_at ft i in
        BatFingerTree.singleton v |> BatFingerTree.append fl |> (Fun.flip BatFingerTree.append) fr

    let insert1 key value node =
      let i, present = lookup1 (keys_of node) key in
      match node with
      | Leaf ({keys; values} as leaf) ->
          if present then Leaf {leaf with values= BatFingerTree.set values i value}
          else Leaf {keys= emplace i key keys; values= emplace i value values}
      (* When in danger or in doubt: run in circles, scream and shout. *)
      | Trunk _ -> failwith "Cannot insert a value on a trunk node. This is a bug in RNT!"

    let pivot_at ft i =
      let l, r' = BatFingerTree.split_at ft i in
      let r, p = BatFingerTree.front_exn r' in
      l, p, r

    let split_at pivot = function
      | Leaf {keys; values} ->
          let kl, kr = BatFingerTree.split_at keys pivot in
          let vl, vr = BatFingerTree.split_at values pivot in
          let p = BatFingerTree.get kr 0 in
          Leaf {keys= kl; values= vl}, p, Leaf {keys= kr; values= vr}
      | Trunk {keys; children} ->
          let kl, kp, kr = pivot_at keys pivot in
          let cl, cr = BatFingerTree.split_at children (pivot + 1) in
          Trunk {keys= kl; children= cl}, kp, Trunk {keys= kr; children= cr}

    (* FIXME: this works out to a geometric distribution with roughly 64
     keys per node. Some of the consequences of this are that:
     - most of our nodes will end up with one or a few elements, which
       would make our trees taller than they would normally need to be
     - some nodes will end up much larger than usual, which is bad for
       lookup performance

     What we want is a normal distribution centered around our desired
     node size. See
     https://www.dolthub.com/docs/architecture/storage-engine/prolly-tree/#controlling-chunk-size
   *)
    let should_split = Concepts.Hash.pick 6

    let hash_of_keys ks =
      let buffer = Buffer.create 1024 in
      BatFingerTree.iter
        (fun k -> K.encode k |> Concepts.Blob.bytes_of_blob |> Buffer.add_bytes buffer)
        ks;
      Concepts.Hash.hash_of_bytes (Buffer.to_bytes buffer)

    let split_position keys =
      let rec loop left right =
        match BatFingerTree.front right with
        | None -> None
        | Some (tail, head) ->
            (* TODO: rolling hash *)
            let left' = BatFingerTree.snoc left head in
            let hash = hash_of_keys left' in
            if should_split hash then Some (BatFingerTree.size left) else loop left' tail
      in
      loop BatFingerTree.empty keys

    let commit_node tx node =
      let open Utilities.Result in
      match split_position (keys_of node) with
      | Some i ->
          let l, p, r = split_at i node in
          let* l_addr = persist tx l in
          let* r_addr = persist tx r in
          Ok (Split (l_addr, p, r_addr))
      | None ->
          let* addr = persist tx node in
          Ok (Update (addr, node))

    let rec insert' tx key value node =
      let open Utilities.Result in
      match node with
      | Leaf _ -> insert1 key value node |> commit_node tx
      | Trunk {keys; children} -> (
          let i, found = lookup1 keys key in
          let i = if found then i + 1 else i in
          let* child = BatFingerTree.get children i |> find' tx in
          let* r = insert' tx key value child in
          match r with
          | Update (addr, _) ->
              Trunk {keys; children= BatFingerTree.set children i addr} |> commit_node tx
          | Split (l, p, r) ->
              Trunk
                { keys= emplace i p keys;
                  children= BatFingerTree.set children i l |> emplace (i + 1) r }
              |> commit_node tx )

    let insert tx key value node =
      let open Utilities.Result in
      let* op = insert' tx key value node in
      match op with
      | Update (_, node) -> Ok node
      | Split (l, p, r) ->
          let new_root =
            Trunk
              { keys= BatFingerTree.singleton p;
                children=
                  BatFingerTree.empty
                  |> (Fun.flip BatFingerTree.snoc) l
                  |> (Fun.flip BatFingerTree.snoc) r }
          in
          let* _ = persist tx new_root in
          Ok new_root

    let of_list tx bindings =
      let open Utilities.Result in
      with_batch tx (fun () ->
          let* _ = empty_under tx in
          Utilities.List.foldm_left
            (fun node (key, value) -> insert tx key value node)
            empty bindings )

    let of_finger_tree tx bindings =
      let open Utilities.Result in
      with_batch tx (fun () ->
          let* _ = empty_under tx in
          Utilities.FingerTree.foldm_left
            (fun node (key, value) -> insert tx key value node)
            empty bindings )

    let rec fold_left tx f acc =
      let open Utilities.Result in
      function
      | Leaf {keys; values} ->
          Utilities.FingerTree.zip keys values
          |> BatFingerTree.fold_left (fun acc (k, v) -> f acc k v) acc
          |> Result.ok
      | Trunk {children; _} ->
          Utilities.FingerTree.foldm_left
            (fun acc addr ->
              let* node = find' tx addr in
              fold_left tx f acc node )
            acc children

    let keys tx node =
      fold_left tx (fun acc k _ -> BatFingerTree.snoc acc k) BatFingerTree.empty node

    let excise i ft =
      let fl, fr = BatFingerTree.split_at ft i in
      BatFingerTree.append fl (BatFingerTree.tail_exn fr)

    (* Like an insert, produces a new tree where the path to the key
       is copied without it, and a node it leaves empty goes from its
       parent with the key that separated it. *)
    let rec remove' tx key node =
      let open Utilities.Result in
      match node with
      | Leaf {keys; values} ->
          let i, _ = lookup1 keys key in
          if BatFingerTree.size keys = 1 then Ok None
          else
            let leaf = Leaf {keys= excise i keys; values= excise i values} in
            let* _ = persist tx leaf in
            Ok (Some leaf)
      | Trunk {keys; children} ->
          let i, found = lookup1 keys key in
          let i = if found then i + 1 else i in
          let* child = BatFingerTree.get children i |> find' tx in
          let* child = remove' tx key child in
          let trunk =
            match child with
            | Some child -> Trunk {keys; children= BatFingerTree.set children i (hash_of child)}
            | None -> Trunk {keys= excise (max 0 (i - 1)) keys; children= excise i children}
          in
          let* _ = persist tx trunk in
          Ok (Some trunk)

    let rec shrink tx = function
      | Trunk {children; _} when BatFingerTree.size children = 1 ->
          Result.bind (find' tx (BatFingerTree.get children 0)) (shrink tx)
      | node -> Ok node

    let remove tx key node =
      let open Utilities.Result in
      let* present = lookup tx key node in
      if Option.is_none present then Ok node
      else
        let* node = remove' tx key node in
        match node with
        | None ->
            let* _ = persist tx empty in
            Ok empty
        | Some node -> shrink tx node
  end

module type INTERFACE = functor (S : Abstract.Storage.STORAGE) (K : KEY) (V : VALUE) -> sig
  module Tree : module type of Make (S) (K)

  type address = Concepts.Hash.hash
  type node

  val with_batch :
    S.transaction ->
    (unit -> (node, Concepts.Condition.condition) result) ->
    (node, Concepts.Condition.condition) result

  val find : S.transaction -> address -> (node option, Concepts.Condition.condition) result
  val from : Tree.node -> node
  val into : node -> Tree.node
  val empty : node
  val empty_under : S.transaction -> (address, Concepts.Condition.condition) result
  val hash_of : node -> address
  val insert : S.transaction -> K.t -> V.t -> node -> (node, Concepts.Condition.condition) result
  val of_list : S.transaction -> (K.t * V.t) list -> (node, Concepts.Condition.condition) result
  val remove : S.transaction -> K.t -> node -> (node, Concepts.Condition.condition) result
  val lookup : S.transaction -> K.t -> node -> (V.t option, Concepts.Condition.condition) result
  val mem : S.transaction -> K.t -> node -> (bool, Concepts.Condition.condition) result

  val fold_left :
    S.transaction ->
    ('c -> K.t -> V.t -> 'c) ->
    'c ->
    node ->
    ('c, Concepts.Condition.condition) result

  val iter :
    S.transaction -> (K.t -> V.t -> 'a) -> node -> (unit, Concepts.Condition.condition) result

  val keys : S.transaction -> node -> (K.t BatFingerTree.t, Concepts.Condition.condition) result
end

module Interface : INTERFACE =
functor
  (S : Abstract.Storage.STORAGE)
  (K : KEY)
  (V : VALUE)
  ->
  struct
    module Tree = Make (S) (K)
    module SI = Storage.Make (S)

    type address = Tree.address
    type node = Tree.node

    open Utilities.Result

    let intern tx v =
      let data = V.encode v in
      let addr = Concepts.Hash.hash_of_blob data in
      let* () = S.put tx (S.Hash addr) data in
      Ok addr

    let retrieve tx addr = SI.get_req tx (S.Hash addr) |>> V.decode
    let find = Tree.find
    let from x = x
    let into x = x
    let empty = Tree.empty
    let empty_under = Tree.empty_under
    let hash_of = Tree.hash_of
    let with_batch = Tree.with_batch

    let insert tx k v node =
      let* addr = intern tx v in
      Tree.insert tx k addr node

    let of_list tx bindings =
      List.map (fun (k, v) -> intern tx v |> Result.map (fun addr -> k, addr)) bindings
      |> Utilities.List.sequence
      |>> Tree.of_list tx

    let remove = Tree.remove

    let lookup tx k node =
      let* addr = Tree.lookup tx k node in
      match addr with None -> Ok None | Some addr -> retrieve tx addr |> Result.map Option.some

    let mem tx k node = Tree.lookup tx k node |> Result.map Option.is_some

    let fold_left tx f acc node =
      Tree.fold_left tx
        (fun acc k addr ->
          let* acc = acc in
          let* v = retrieve tx addr in
          Ok (f acc k v) )
        (Ok acc) node
      |> Result.join

    let iter tx f node = fold_left tx (fun _ k v -> f k v |> ignore) () node
    let keys = Tree.keys
  end

module StringKey : KEY with type t = string = struct
  type t = string

  let encode s = String.to_bytes s |> Concepts.Blob.blob_of_bytes
  let compare s1 s2 = String.compare s1 s2 |> Utilities.Ordering.of_int
  let decode b = Concepts.Blob.bytes_of_blob b |> String.of_bytes |> Result.ok
end
