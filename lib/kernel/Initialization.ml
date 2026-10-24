module Error = struct
  open Concepts.Condition

  let taken name =
    condition "name-taken" "A namespace already binds the name"
      ("name" |=| Concepts.Value.String name)
end

let bind namespace (name, handle) =
  let open Utilities.Result in
  let* registry = Protocols.Handle.require Protocols.Registry.from namespace in
  let* bound = Protocols.Registry.update registry name None (Some handle) in
  if bound then Ok () else Error (Error.taken name)

let namespace entries =
  let into = Namespace.make () in
  Utilities.List.foldm_left (fun () -> bind into) () entries |> Result.map (fun () -> into)

(* A subsystem's root holds what is its own and not data: its
   evaluators, and whatever else it registers beside them. *)
let mount root name =
  match Path.lookup root Path.(name @/ this) with
  | Ok mounted -> Ok (Protocols.Handle.release mounted)
  | Error _ ->
      let open Utilities.Result in
      let* mounted = namespace ["evaluator", Namespace.make ()] in
      bind root (name, mounted)

module Make (S : Abstract.Storage.STORAGE) = struct
  module BM = BranchManager.Make (S)
  module B = Branch.Make (S)

  (* The heads of \system's branches, of which there is always a master,
     are kept under the label rnt-head. *)
  let initialize ?(evaluators = []) conn =
    let open Utilities.Result in
    let root = Namespace.make () in
    let* evaluator = namespace evaluators in
    let* branch = BM.make ~root conn "rnt-head" in
    let* () =
      if Path.lookup branch Path.("master" @/ this) |> Result.is_ok then Ok ()
      else Result.bind (B.make conn) (fun empty -> bind branch ("master", empty))
    in
    let* system =
      namespace
        [ "branch", branch;
          "evaluator", evaluator;
          "session", Namespace.make ();
          "application", Namespace.make () ]
    in
    let* () = bind root ("system", system) in
    Ok root
end
