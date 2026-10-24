module Error = struct
  open Concepts.Condition

  let unknown_relation name =
    condition "unknown-relation" "A plan named a relation that does not exist under this snapshot"
      ("name" |=| Concepts.Value.String name)

  let cancelled () =
    condition "evaluation-cancelled" "An evaluation was stopped before it produced its result" empty

  let not_a_plan () =
    condition "not-a-fol-program" "The evaluator was given a program of another kind" empty

  let unknown_attribute name =
    condition "unknown-attribute" "A plan projected an attribute its relation does not have"
      ("attribute" |=| Concepts.Value.String name)

  let malformed_program () =
    condition "malformed-fol-program"
      "A stored FOL program did not conform to what was expected. Is your database corrupted?" empty

  let cyclic_program code =
    condition "cyclic-program" "A stored program reads itself"
      ("program" |=| Concepts.Value.String (Concepts.Hash.to_hum_string code))
end

let name = "fol"

type 'r term = Base of 'r | Project of 'r term * string BatFingerTree.t
type plan = Protocols.Handle.t term
type Kernel.Program.kind += Fol of Kernel.Path.t term

module Bencode = Concepts.Encoding.Bencode

let rec bencode_of_term =
  let strings values = Bencode.List (List.map (fun value -> Bencode.String value) values) in
  function
  | Base path -> Bencode.Tagged ('b', strings (Kernel.Path.to_list path))
  | Project (term, attributes) ->
      Bencode.Tagged
        ( 'p',
          Bencode.Dict
            ["term", bencode_of_term term; "attributes", strings (BatFingerTree.to_list attributes)]
        )

let rec term_of_bencode =
  let open Utilities.Result in
  let strings values =
    let* values = Bencode.as_list values in
    List.map Bencode.as_string values |> Utilities.List.sequence
  in
  function
  | Bencode.Tagged ('b', segments) ->
      strings segments |> Result.map (fun segments -> Base (Kernel.Path.of_list segments))
  | Bencode.Tagged ('p', data) ->
      let* term = Bencode.field "term" data |>> term_of_bencode in
      let* attributes = Bencode.field "attributes" data |>> strings in
      Ok (Project (term, BatFingerTree.of_list attributes))
  | _ -> Error (Error.malformed_program ())

let encode term = bencode_of_term term |> Bencode.to_bytes |> Bytes.to_string
let decode source = Utilities.Result.(Bencode.of_bytes (Bytes.of_string source) |>> term_of_bencode)

(* TODO: To strenghten our checks for self references, we need to
   construct a graph and see raise a condition if there are self
   references. We partially do that here with the program calling
   self, but if the flow is alternated, say between program A and B,
   where B calls A and A calls B, we also must check. *)
let instantiate within =
  let open Utilities.Result in
  let rec bind expanding = function
    | Base reference -> (
        let* relation = Kernel.Path.lookup within reference in
        match Kernel.Program.image relation with
        | None -> Ok (Base relation)
        | Some {kind= Fol term; source; _} ->
            Protocols.Handle.release relation;
            let identity = Concepts.Hash.hash_of_bytes (Bytes.of_string source) in
            if List.exists (Concepts.Hash.hash_equals identity) expanding then
              Error (Error.cyclic_program identity)
            else bind (identity :: expanding) term
        | Some _ ->
            Protocols.Handle.releasing relation (fun () ->
                let* program = Protocols.Executable.require relation in
                let* result = Protocols.Executable.invoke program [] ~within in
                Ok (Base result) ) )
    | Project (term, attributes) ->
        let* plan = bind expanding term in
        Ok (Project (plan, attributes))
  in
  bind []

let restrict attributes description =
  let open Utilities.Result in
  Utilities.FingerTree.foldm_left
    (fun restricted name ->
      let* attribute =
        BatMap.String.find_opt name description
        |> Option.to_result ~none:(Error.unknown_attribute name)
      in
      Ok (BatMap.String.add name attribute restricted) )
    BatMap.String.empty attributes

let rec describe =
  let open Utilities.Result in
  function
  | Base relation -> Protocols.Relation.heading relation
  | Project (plan, attributes) -> describe plan |>> restrict attributes

let rec modes =
  let open Utilities.Result in
  function
  | Base relation ->
      let* relation = Protocols.Relation.require relation in
      Protocols.Relation.modes relation
  | Project (plan, attributes) ->
      modes plan
      |> Result.map
           (Concepts.Mode.project (BatSet.String.of_list (BatFingerTree.to_list attributes)))

let project description relation =
  let open Utilities.Result in
  let* cursor = Protocols.Enumerable.cursor relation in
  let produce ~yield =
    let* scan = Protocols.Cursor.require cursor in
    let rec distinct seen =
      let* next = Protocols.Cursor.next scan in
      match next with
      | None -> Ok ()
      | Some tuple ->
          let tuple =
            { tuple with
              attributes=
                BatMap.String.filter
                  (fun name _ -> BatMap.String.mem name description)
                  tuple.Concepts.Tuple.attributes }
          in
          let key = Concepts.Tuple.hash tuple |> Concepts.Hash.to_raw_string in
          if BatSet.String.mem key seen then distinct seen
          else begin
            yield tuple;
            distinct (BatSet.String.add key seen)
          end
    in
    distinct BatSet.String.empty
  in
  Ok (Kernel.Generator.cursor_of ~finally:(fun () -> Protocols.Handle.release cursor) produce)

let contains relation tuple =
  Result.bind (Protocols.Relation.require relation) (fun r -> Protocols.Relation.contains r tuple)

let derive ?decide relation description modes enumerate =
  Kernel.EphemeralRelation.instantiate ~inputs:[relation] ?decide
    ~modes:(fun () -> Ok modes)
    description
    (Kernel.EphemeralRelation.temporary description)
    (fun () -> enumerate relation)

let rec execute plan =
  let open Utilities.Result in
  let* description = describe plan in
  let* modes = modes plan in
  match plan with
  | Base relation ->
      let relation = Protocols.Handle.move relation in
      Ok (derive ~decide:(contains relation) relation description modes Protocols.Enumerable.cursor)
  | Project (plan, _) ->
      let* relation = execute plan in
      Ok (derive relation description modes (project description))

class evaluator =
  object (self)
    inherit Kernel.Lifecycle.null
    inherit Kernel.Identity.of_id
    method to_string = "fol-evaluator"
    method parse source = decode source |> Result.map (fun term -> Fol term)

    method eval kind _inputs ~within =
      let open Utilities.Result in
      match kind with
      | Fol term ->
          let* plan = instantiate within term in
          execute plan
      | _ -> Error (Error.not_a_plan ())

    method protocols : Protocols.Handle.protocol list = [Protocols.Evaluator.make self]
  end

let make () = new evaluator |> Protocols.Handle.make
let program ?root term = Kernel.Program.make ?root ~evaluator:name ~source:(encode term) (Fol term)
