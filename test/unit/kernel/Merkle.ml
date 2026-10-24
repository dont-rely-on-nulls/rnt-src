open Rnt

module Make (S : Abstract.Storage.STORAGE) (C : Helpers.Storage.CONFIGURATOR) = struct
  open Alcotest
  module H = Helpers.Storage.Make (S) (C)

  module T =
    Rnt.Kernel.Merkle.Interface (S) (Rnt.Kernel.Merkle.StringKey) (Rnt.Kernel.Merkle.StringKey)

  (* TODO: be a bit more comprehensive (ideally, we want to test splits as well) *)
  let insert_and_lookup conn =
    let v1, v2, v3, v3', bogus =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let* node =
          T.empty
          |> T.insert tx "k1" "v1"
          |>> T.insert tx "k2" "v2"
          |>> T.insert tx "k3" "v3"
        in
        let* node' = T.insert tx "k3" "toodles" node in
        let* v1 = T.lookup tx "k1" node in
        let* v2 = T.lookup tx "k2" node in
        let* v3 = T.lookup tx "k3" node in
        let* v3' = T.lookup tx "k3" node' in
        let* bogus = T.lookup tx "fnord" node in
        let* () = S.abort tx in
        Ok (v1, v2, v3, v3', bogus)
      end
      |> Helpers.condition_as_failure
    in
    check (option string) "that in-memory reads from the first write work properly" (Some "v1") v1;
    check (option string) "that in-memory reads from the second write work properly" (Some "v2") v2;
    check (option string) "that in-memory reads from the third write work properly" (Some "v3") v3;
    check (option string) "that in-memory reads from a value replacement work properly"
      (Some "toodles") v3';
    check (option string) "that in-memory reads from a non-existent key returns nothing" None bogus

  let batching conn =
    let intermediate, final =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let intermediate = ref None in
        let* final =
          T.with_batch tx (fun () ->
              let* i = T.empty |> T.insert tx "tree" "maple" in
              intermediate := Some (T.hash_of i);
              T.insert tx "tree" "spruce" i )
        in
        let* () = S.commit tx in
        Ok (Option.get !intermediate, T.hash_of final)
      end
      |> Helpers.condition_as_failure
    in
    let i_node, f_node =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let* intermediate = T.find tx intermediate in
        let* final = T.find tx final in
        Ok (intermediate, final)
      end
      |> Helpers.condition_as_failure
    in
    check bool "that the intermediate node does not get persisted" true (Option.is_none i_node);
    check bool "that the final node does get persisted" true (Option.is_some f_node)

  let persistence conn =
    let addr =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let* node =
          T.empty
          |> T.insert tx "k1" "v1"
          |>> (T.insert tx "k2" "v2")
          |>> (T.insert tx "k3" "v3")
        in
        let* () = S.commit tx in
        Ok (T.hash_of node)
      end
      |> Helpers.condition_as_failure
    in
    let v1, v2, v3 =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let* node = T.find tx addr |> Result.map Option.get in
        let* v1 = T.lookup tx "k1" node in
        let* v2 = T.lookup tx "k2" node in
        let* v3 = T.lookup tx "k3" node in
        Ok (v1, v2, v3)
      end
      |> Helpers.condition_as_failure
    in
    check (option string) "that on-disk reads from the first write work properly" (Some "v1") v1;
    check (option string) "that on-disk reads from the second write work properly" (Some "v2") v2;
    check (option string) "that on-disk reads from the third write work properly" (Some "v3") v3

  let iteration conn =
    let keys, values =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let* node =
          T.empty
          |> T.insert tx "k1" "v1"
          |>> (T.insert tx "k2" "v2")
          |>> (T.insert tx "k3" "v3")
        in
        let* keys = T.fold_left tx (fun acc k _ -> k :: acc) [] node |> Result.map List.rev in
        let* values = T.fold_left tx (fun acc _ v -> v :: acc) [] node |> Result.map List.rev in
        let* () = S.abort tx in
        Ok (keys, values)
      end
      |> Helpers.condition_as_failure
    in
    check (list string) "that keys are properly enumerated from left to right" ["k1"; "k2"; "k3"]
      keys;
    check (list string) "that values are properly enumerated from left to right" ["v1"; "v2"; "v3"]
      values

  (* TODO: this will need `remove` *)
  (* let determinism _conn = *)
  (*   () *)

  (* Enough keys for the tree to grow trunks, so removal reaches through
     them and empties whole leaves. *)
  let removal conn =
    let kept, gone, keys, emptied =
      begin
        let open Utilities.Result in
        let* tx = S.start conn in
        let key i = Printf.sprintf "k%03d" i in
        let all = List.init 300 key in
        let* full = List.fold_left (fun node k -> node |>> T.insert tx k k) (Ok T.empty) all in
        let evens = List.filteri (fun i _ -> i mod 2 = 0) all in
        let* half = List.fold_left (fun node k -> node |>> T.remove tx k) (Ok full) evens in
        let* kept = T.lookup tx (key 1) half in
        let* gone = T.lookup tx (key 2) half in
        let* keys = T.keys tx half in
        let* none = List.fold_left (fun node k -> node |>> T.remove tx k) (Ok half) all in
        let* () = S.abort tx in
        Ok (kept, gone, BatFingerTree.to_list keys, T.hash_of none)
      end
      |> Helpers.condition_as_failure
    in
    check (option string) "a key not removed stays" (Some "k001") kept;
    check (option string) "a removed key is gone" None gone;
    check (list string) "exactly the odd keys remain"
      (List.init 150 (fun i -> Printf.sprintf "k%03d" ((2 * i) + 1)))
      keys;
    check bool "removing every key leaves the empty tree" true
      (Concepts.Hash.hash_equals emptied (T.hash_of T.empty))

  let suite =
    ( "kernel/merkle",
      [ test_case "insert-and-lookup" `Quick (H.with_connection insert_and_lookup "merkle-test");
        test_case "batching" `Quick (H.with_connection batching "merkle-test");
        test_case "persistence" `Quick (H.with_connection persistence "merkle-test");
        test_case "iteration" `Quick (H.with_connection iteration "merkle-test");
        test_case "removal" `Quick (H.with_connection removal "merkle-test") ] )
end

module LMDB = Make (Rnt.Backend.Storage.LMDB) (Helpers.Storage.LMDB_Configurator)

let suites () = [LMDB.suite]
