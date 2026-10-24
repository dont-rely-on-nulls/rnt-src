module Make (S : Abstract.Storage.STORAGE) = struct
  module Pointer = struct
    type 'a t =
      { addr: S.address;
        loader: S.transaction -> S.address -> ('a, Concepts.Condition.condition) result }

    let make loader addr = {addr; loader}
    let address_of {addr; _} = addr
    let swap {loader; _} addr = make loader addr
    let deref tx {addr; loader} = loader tx addr
  end

  let as_hash = function
    | S.Hash h -> h
    | _ -> failwith "A label was provided where a hash was expected."

  let to_hum_string = function
    | S.Hash h -> "Hash " ^ Concepts.Hash.to_hum_string h
    | S.Label l -> "Label " ^ l

  module Error = struct
    open Concepts.Condition

    let missing_data addr =
      condition "missing-data"
        "An expected value was not found on the underlying storage. Is your database corrupted?"
        ("address" |=| Concepts.Value.String (to_hum_string addr))
  end

  let finish tx = function
    | Ok value ->
        let open Utilities.Result in
        let* () = S.commit tx in
        Ok value
    | Error condition ->
        let _ = S.abort tx in
        Error condition

  let within start connection body =
    let open Utilities.Result in
    let* tx = start connection in
    body tx |> finish tx

  let with_transaction connection = within S.start connection
  let with_read connection = within S.start_read connection

  let store_blob tx blob =
    let open Utilities.Result in
    let address = Concepts.Hash.hash_of_blob blob in
    let* () = S.put tx (S.Hash address) blob in
    Ok address

  let get_req tx addr =
    Utilities.Result.(S.get tx addr |>> Option.to_result ~none:(Error.missing_data addr))
end
