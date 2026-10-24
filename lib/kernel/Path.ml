type t = string list

let this = []
let ( @/ ) x y = x :: y
let of_list segments = segments
let to_list path = path

let to_string path =
  path
  |> List.map (fun x ->
      BatString.nreplace ~str:(BatString.nreplace ~str:x ~sub:"^" ~by:"^^") ~sub:"\\" ~by:"^\\" )
  |> BatIO.to_string (BatList.print ~first:"\\" ~last:"" ~sep:"\\" BatString.print)

module Error = struct
  open Concepts.Condition

  let path_not_found path =
    condition "path-not-found" "A given path was not found under the specified object"
      ("path" |=| Concepts.Value.String (to_string path))

  let overlapping_change path =
    condition "overlapping-change"
      "A batch of changes both replaced an object and changed inside it"
      ("path" |=| Concepts.Value.String (to_string path))

  let unheld path =
    condition "path-unheld" "The object at the path could not be held"
      ("path" |=| Concepts.Value.String (to_string path))
end

let walking ?missing f g handle path =
  let open Protocols in
  let open Utilities.Result in
  let rec walk handle = function
    | [] -> g (Handle.keep handle)
    | x :: xs -> (
        let* dir =
          Handle.require Directory.from handle
          |> Result.map_error
               Concepts.Condition.(complement ("before-segment" |=| Concepts.Value.String x))
        in
        let* elem = Directory.find dir x |> Result.map (Option.map Handle.autorelease) in
        match elem with
        | None -> (
          match missing with Some m -> m () | None -> Error (Error.path_not_found path) )
        | Some elem -> f x handle (fun () -> walk elem xs) )
  in
  Handle.with_autorelease (fun () ->
      begin match path with
      | [] -> (
        match Handle.copy handle with Some copy -> g copy | None -> Error (Error.unheld path) )
      | _ -> walk handle path
      end
      |> Result.map_error
           Concepts.Condition.(complement ("path" |=| Concepts.Value.String (to_string path))) )

let lookup handle path = walking (fun _ _ f -> f ()) Result.ok handle path

let find handle path =
  walking ~missing:(fun () -> Ok None) (fun _ _ f -> f ()) (fun h -> Ok (Some h)) handle path

let update handle path key reference value =
  let open Utilities.Result in
  let open Protocols in
  let* target = lookup handle path in
  Handle.releasing target (fun () ->
      let* registry = Handle.require Registry.from target in
      Registry.update registry key reference value )

(* The changes at this object, and those beneath each child they reach. *)
let split changes =
  let here, below = List.partition (fun (path, _, _) -> path = []) changes in
  let segments =
    List.sort_uniq String.compare (List.map (fun (path, _, _) -> List.hd path) below)
  in
  let beneath x =
    List.filter_map
      (fun (path, key, value) ->
        match path with y :: rest when y = x -> Some (rest, key, value) | _ -> None )
      below
  in
  here, List.map (fun x -> x, beneath x) segments

(* What is not there yet is handed over as a directory of what the
   changes put in it, for its parent to store. *)
let rec fresh changes =
  let here, children = split changes in
  Prototype.(
    mixture
      [ Directory.of_properties
          ( List.filter_map (fun (_, key, value) -> Option.map (fun v -> key, v) value) here
          @ List.map (fun (x, beneath) -> x, fresh beneath) children ) ] )

let binds changes = List.exists (fun (_, _, value) -> Option.is_some value) changes

(* Changes under the same name are applied to the child together, so
   every object on the way is derived once however many changes reach
   it: a batch of changes to a branch is one successor state. *)
let assoc_all handle changes =
  let open Utilities.Result in
  let open Protocols in
  let assoc_on node (key, value) =
    let* a = Handle.require Associative.from node in
    let* a' = Associative.update a key value in
    Ok (Handle.from a')
  in
  let rec apply prefix node changes =
    let here, below = split changes in
    let segments = List.map fst below in
    match List.find_opt (fun (_, key, _) -> List.mem key segments) here with
    | Some (_, key, _) -> Error (Error.overlapping_change (prefix @ [key]))
    | None ->
        let* children =
          Utilities.List.concat_mapm
            (fun (x, beneath) ->
              let* dir = Handle.require Directory.from node in
              let* found = Directory.find dir x in
              match found with
              | None when binds beneath -> Ok [x, Some (fresh beneath)]
              | None -> Ok []
              | Some child ->
                  Handle.releasing child (fun () -> apply (prefix @ [x]) child beneath)
                  |> Result.map (fun child' -> [x, Some child']) )
            below
        in
        (* each step derives from the last; only the steps in between are
           ours to release *)
        Utilities.List.foldm_left
          (fun current change ->
            let* next = assoc_on current change in
            if current != node then Handle.release current;
            Ok next )
          node
          (children @ List.map (fun (_, key, value) -> key, value) here)
  in
  apply [] handle changes

let assoc handle path key value = assoc_all handle [path, key, value]

let diff a b =
  let open Utilities.Result in
  let open Protocols in
  let address h = Option.map Addressable.address (Addressable.from h) in
  let same x y =
    match address x, address y with
    | Some p, Some q -> Concepts.Hash.hash_equals p q
    | _ -> Handle.equal x y
  in
  let names h =
    let* dir = Handle.require Directory.from h in
    let* names = Directory.list dir in
    Ok (BatFingerTree.to_list names)
  in
  let find h name =
    let* dir = Handle.require Directory.from h in
    Directory.find dir name
  in
  let rec walk prefix a b =
    let* left = names a in
    let* right = names b in
    List.sort_uniq String.compare (left @ right)
    |> Utilities.List.concat_mapm (fun name ->
        let path = prefix @ [name] in
        let* x = find a name in
        let* y = find b name in
        Fun.protect
          ~finally:(fun () -> List.iter Handle.release (Option.to_list x @ Option.to_list y))
          (fun () ->
            match x, y with
            | None, None -> Ok []
            | Some x, Some y when same x y -> Ok []
            | Some x, Some y when Directory.from x <> None && Directory.from y <> None ->
                let* below = walk path x y in
                Ok (if below = [] then [path] else below)
            | _ -> Ok [path] ) )
  in
  walk [] a b
