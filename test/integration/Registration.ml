open Rnt

module Make (S : Abstract.Storage.STORAGE) (C : Helpers.Storage.CONFIGURATOR) = struct
  open Alcotest
  module H = Helpers.Storage.Make (S) (C)
  module I = Kernel.Initialization.Make (S)
  module B = Kernel.Branch.Make (S)
  module M = Kernel.Multigroup.Make (S)
  module E = Kernel.EphemeralRelation.Make (S)

  let book =
    Kernel.Path.("multigroup" @/ "library" @/ "schema" @/ "default" @/ "relation" @/ "book" @/ this)

  let shelf =
    Kernel.Path.("multigroup" @/ "library" @/ "schema" @/ "default" @/ "relation" @/ "shelf" @/ this)

  let stacks = Kernel.Path.("system" @/ "branch" @/ "stacks" @/ this)

  let titled title =
    { Concepts.Tuple.type_= "book";
      attributes=
        BatMap.String.of_list
          ["title", Concepts.Value.String title; "author", Concepts.Value.String "Date"] }

  let run conn =
    let open Utilities.Result in
    begin
      let* root = I.initialize ~evaluators:["fol", Evaluators.FOL.make ()] conn in
      let* relation = H.relation conn ["title"; "author"] [titled "SQL and Relational Theory"] in
      let* stored =
        E.persist conn ~name:"shelf"
          Evaluators.FOL.(program (Project (Base book, BatFingerTree.singleton "title")))
          (BatMap.String.singleton "title" {Protocols.Schematics.domain= "string"; provenance= []})
      in
      let* multigroup = M.make conn in
      let relations = Kernel.Path.("schema" @/ "default" @/ "relation" @/ this) in
      let* multigroup =
        Kernel.Path.assoc_all multigroup
          [relations, "book", Some relation; relations, "shelf", Some stored]
      in
      let* branch = B.make conn in
      let* branch' =
        Kernel.Path.(assoc branch ("multigroup" @/ this) "library" (Some multigroup))
      in
      Kernel.Path.(update root ("system" @/ "branch" @/ this) "stacks" None (Some branch'))
    end
    |> Helpers.condition_as_failure
    |> ignore;
    let attributes, shelved =
      begin
        let* root = I.initialize ~evaluators:["fol", Evaluators.FOL.make ()] conn in
        let* branch = Kernel.Path.lookup root stacks in
        let* _ = Kernel.Path.lookup branch book in
        let* plan = Evaluators.FOL.(instantiate branch (Base shelf)) in
        let* description = Evaluators.FOL.describe plan in
        let* stored = Kernel.Path.lookup branch shelf in
        let* shelved = Helpers.titles stored in
        Ok (BatMap.String.keys description |> BatList.of_enum, shelved)
      end
      |> Helpers.condition_as_failure
    in
    check (list string) "the stored program reads the book it was defined over" ["title"] attributes;
    check (list Helpers.value) "read through the branch, the stored program runs"
      [Concepts.Value.String "SQL and Relational Theory"]
      shelved

  let suite =
    ( "registration",
      [test_case "register-and-lookup" `Quick (H.with_connection run "registration-test")] )
end

module LMDB = Make (Rnt.Backend.Storage.LMDB) (Helpers.Storage.LMDB_Configurator)

let suites () = [LMDB.suite]
