type home = {multigroup: string; schema: string}

class type implementation = object
  method branch : Protocols.Handle.t
  method home : home
  method previous : (Protocols.Handle.t option, Concepts.Condition.condition) result
  method catalog : (string list, Concepts.Condition.condition) result
end

type Protocols.Handle.protocol += Scope of implementation

let require handle =
  Protocols.Handle.into handle (function Scope i -> Some i | _ -> None)
  |> Option.to_result
       ~none:
         Concepts.Condition.(
           condition "not-a-scope" "A handle was expected to be a branch state read from a home"
             empty )

let relations {multigroup; schema} =
  Path.("multigroup" @/ multigroup @/ "schema" @/ schema @/ "relation" @/ this)

let path home relation = Path.(of_list (to_list (relations home) @ [relation]))
let denial multigroup = Path.("multigroup" @/ multigroup @/ "denial" @/ this)

(* A name leaves out, from the left, what it shares with its home. *)
let resolve home text =
  match String.split_on_char ':' text with
  | names when List.mem "" names -> None
  | [r] -> Some (home, r)
  | [s; r] -> Some ({home with schema= s}, r)
  | [m; s; r] -> Some ({multigroup= m; schema= s}, r)
  | _ -> None

let locate home text = Option.map (fun (h, r) -> path h r) (resolve home text)

let attribute home relation text =
  match List.rev (String.split_on_char ':' text) with
  | [a] -> Some a
  | a :: rest when resolve home (String.concat ":" (List.rev rest)) = resolve home relation ->
      Some a
  | _ -> None

(* every relation of a branch state, as multigroup:schema:relation *)
let catalog_of branch =
  let open Utilities.Result in
  let name prefix last = Utilities.FingerTree.join (BatFingerTree.reverse (BatFingerTree.cons prefix last)) ":" in
  let rec down prefix handle properties =
    let* level = Path.find handle Path.(List.hd properties @/ this) in
    match level, List.tl properties with
    | None, _ -> Ok BatFingerTree.empty
    | Some level, [] ->
        let* listing = Protocols.Handle.require Protocols.Directory.from level in
        let* names = Protocols.Directory.list listing in
        Ok (BatFingerTree.map (name prefix) names)
    | Some level, rest ->
        let* named = Protocols.Directory.children level in
        Utilities.FingerTree.concat_mapm (fun (n, child) -> down (BatFingerTree.cons prefix n) child rest) named
  in
  down BatFingerTree.empty branch ["multigroup"; "schema"; "relation"]

let rec make branch home =
  Prototype.mixture
    [ Protocols.Directory.make
        object
          method list =
            let open Utilities.Result in
            let* found = Path.find branch (relations home) in
            match found with
            | None -> Ok BatFingerTree.empty
            | Some found ->
                let* listing = Protocols.Handle.require Protocols.Directory.from found in
                Protocols.Directory.list listing

          (* what is not a relation's name names no relation here *)
          method find text =
            match resolve home text with
            | None -> Ok None
            | Some (h, r) -> Path.find branch (path h r)
        end;
      Scope
        object
          method branch = branch
          method home = home

          method previous =
            let open Utilities.Result in
            let* previous = Path.find branch Path.("previous" @/ this) in
            Ok (Option.map (fun p -> make p home) previous)

          method catalog = catalog_of branch |> Result.map BatFingerTree.to_list (* FIXME: use finger trees thoroughly *)
        end ]

let heads = Path.("system" @/ "branch" @/ this)

let of_root root ~branch home =
  let open Utilities.Result in
  let* state = Path.lookup root Path.("system" @/ "branch" @/ branch @/ this) in
  Ok (make state home)

let branch i = Protocols.Handle.invoke i (fun o -> o#branch)
let home i = Protocols.Handle.invoke i (fun o -> o#home)
let previous i = Protocols.Handle.invoke i (fun o -> o#previous)
let catalog i = Protocols.Handle.invoke i (fun o -> o#catalog)

module Error = struct
  open Concepts.Condition

  let malformed name =
    condition "malformed-name"
      "A relation is named relation, schema:relation or multigroup:schema:relation"
      ("name" |=| Concepts.Value.String name)

  let malformed_denial name =
    condition "malformed-name" "A denial is named denial or multigroup:denial"
      ("name" |=| Concepts.Value.String name)

  let moved branch =
    condition "serialization-conflict" "The branch moved on while this commit was made; retry it"
      ("branch" |=| Concepts.Value.String branch)
end

let publish ?(denials = []) root ~branch ~home bindings =
  let open Utilities.Result in
  let* changes =
    List.map
      (fun (name, v) ->
        match resolve home name with
        | Some (h, r) -> Ok (relations h, r, v)
        | None -> Error (Error.malformed name) )
      bindings
    |> Utilities.List.sequence
  in
  let* denied =
    List.map
      (fun (name, v) ->
        match String.split_on_char ':' name with
        | [d] when d <> "" -> Ok (denial home.multigroup, d, v)
        | [m; d] when m <> "" && d <> "" -> Ok (denial m, d, v)
        | _ -> Error (Error.malformed_denial name) )
      denials
    |> Utilities.List.sequence
  in
  let changes = changes @ denied in
  if List.is_empty changes then Ok ()
  else
    let* state = Path.lookup root Path.("system" @/ "branch" @/ branch @/ this) in
    let* next = Path.assoc_all state changes in
    let* landed = Path.update root heads branch (Some state) (Some next) in
    if landed then Ok () else Error (Error.moved branch)
