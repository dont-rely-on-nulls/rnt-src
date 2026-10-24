class namespace =
  object (self)
    inherit Lifecycle.counted
    inherit Identity.of_id
    method to_string = "namespace"
    val entries : (string, Protocols.Handle.t) BatMap.t Atomic.t = Atomic.make BatMap.empty
    method protocols = Protocols.[Directory.make self; Registry.make self]
    method destroy = Atomic.get entries |> BatMap.values |> BatEnum.iter Protocols.Handle.release

    method update key reference value =
      match
        Utilities.Atomic.mswap entries (fun e ->
            let existing = BatMap.find_opt key e in
            if existing = reference then begin
              Option.iter Protocols.Handle.release existing;
              match value with
              | Some v -> Ok (BatMap.add key (Protocols.Handle.move v) e)
              | None -> Ok (BatMap.remove key e)
            end
            else Error () )
      with
      | Ok _ -> Ok true
      | Error _ -> Ok false

    method list = Atomic.get entries |> BatMap.keys |> BatFingerTree.of_enum |> Result.ok

    method find key =
      let open Utilities.Option in
      Atomic.get entries
      |> BatMap.find_opt key
      |>> Protocols.Handle.copy
      |> Result.ok
  end

let make () = Protocols.Handle.make (new namespace)
