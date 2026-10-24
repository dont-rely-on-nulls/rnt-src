class type implementation = object
  method list : (string BatFingerTree.t, Concepts.Condition.condition) result
  method find : string -> (Handle.t option, Concepts.Condition.condition) result
end

type Handle.protocol += Directory of implementation
type t = implementation

let make impl = Directory (impl :> implementation)
let from handle = Handle.into handle (function Directory impl -> Some impl | _ -> None)
let list i = Handle.invoke i (fun o -> o#list)
let find i name = Handle.invoke i (fun o -> o#find name)

let children directory =
  let open Utilities.Result in
  let* listing = Handle.require from directory in
  let* names = list listing in
  names
  |> BatFingerTree.map (fun name ->
      let* found = find listing name in
      Ok (Option.map (fun child -> name, child) found) )
  |> Utilities.FingerTree.sequence
  |> Result.map (Utilities.FingerTree.filter_map Fun.id)
