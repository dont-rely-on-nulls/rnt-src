open Rnt

module Make (S : Abstract.Storage.STORAGE) (C : Helpers.Storage.CONFIGURATOR) = struct
  open Alcotest
  module H = Helpers.Storage.Make (S) (C)

  let alaric =
    { Concepts.Tuple.type_= "employee";
      attributes= BatMap.String.empty |> BatMap.String.add "name" (Concepts.Value.String "Alaric")
    }

  let employee name age =
    { Concepts.Tuple.type_= "employee";
      attributes=
        BatMap.String.of_list ["name", Concepts.Value.String name; "age", Concepts.Value.Integer age]
    }

  let named name =
    { Concepts.Tuple.type_= "employee";
      attributes= BatMap.String.singleton "name" (Concepts.Value.String name) }

  let employees = Rnt.Evaluators.FOL.Base Kernel.Path.("employee" @/ this)
  let names = Rnt.Evaluators.FOL.Project (employees, BatFingerTree.singleton "name")

  let heading =
    BatMap.String.singleton "name" {Protocols.Schematics.domain= "string"; provenance= []}

  let directory entries = Kernel.Prototype.(mixture [Directory.of_properties entries])

  let eval within term =
    let open Utilities.Result in
    let* evaluator = Protocols.Evaluator.require (Rnt.Evaluators.FOL.make ()) in
    Protocols.Evaluator.eval evaluator (Rnt.Evaluators.FOL.Fol term) [] ~within

  let drain result =
    let open Utilities.Result in
    let* tuples = Protocols.Enumerable.scan result (fun scan -> Protocols.Cursor.drain scan ()) in
    Protocols.Handle.release result;
    Ok (BatFingerTree.to_list tuples)

  let bindings tuples =
    List.map (fun tuple -> BatMap.String.bindings tuple.Concepts.Tuple.attributes) tuples
    |> List.sort compare

  let scan_a_base_relation conn =
    let scanned =
      begin
        let open Utilities.Result in
        let* employee = H.relation conn ["name"] [alaric] in
        let* result = eval (directory ["employee", employee]) employees in
        drain result
      end
      |> Helpers.condition_as_failure
    in
    check int "one tuple scanned" 1 (List.length scanned);
    check bool "the tuple that was asserted" true
      (List.for_all
         (fun tuple ->
           Concepts.Hash.hash_equals (Concepts.Tuple.hash tuple) (Concepts.Tuple.hash alaric) )
         scanned )

  let project_away_an_attribute conn =
    let projected =
      begin
        let open Utilities.Result in
        let* relation =
          H.relation conn ["name"; "age"]
            [employee "Alaric" 42; employee "Alaric" 30; employee "Brunhild" 42]
        in
        let* result = eval (directory ["employee", relation]) names in
        drain result
      end
      |> Helpers.condition_as_failure
    in
    check
      (list (list (pair string Helpers.value)))
      "each name once, and nothing else"
      [["name", Concepts.Value.String "Alaric"]; ["name", Concepts.Value.String "Brunhild"]]
      (bindings projected)

  let instantiate_a_program conn =
    let projected =
      begin
        let open Utilities.Result in
        let* relation = H.relation conn ["name"; "age"] [employee "Alaric" 42] in
        let* plan = Rnt.Evaluators.FOL.instantiate (directory ["employee", relation]) names in
        let* result = Rnt.Evaluators.FOL.execute plan in
        drain result
      end
      |> Helpers.condition_as_failure
    in
    check
      (list (list (pair string Helpers.value)))
      "the program ran over the relation its path resolved to"
      [["name", Concepts.Value.String "Alaric"]]
      (bindings projected)

  module E = Kernel.EphemeralRelation.Make (S)

  let store conn term = E.persist conn ~name:"stored" (Rnt.Evaluators.FOL.program term) heading

  let namespace entries =
    let open Utilities.Result in
    let root = Kernel.Namespace.make () in
    let* registry = Protocols.Handle.require Protocols.Registry.from root in
    let* _ =
      List.fold_left
        (fun registered (name, handle) ->
          let* _ = registered in
          Protocols.Registry.update registry name None (Some handle) )
        (Ok true) entries
    in
    Ok root

  let expand_a_stored_program conn =
    let projected =
      begin
        let open Utilities.Result in
        let* relation = H.relation conn ["name"; "age"] [employee "Alaric" 42] in
        let* stored = store conn names in
        let* root = namespace ["employee", relation; "stored", stored] in
        let* plan = Rnt.Evaluators.FOL.(instantiate root (Base Kernel.Path.("stored" @/ this))) in
        let* result = Rnt.Evaluators.FOL.execute plan in
        drain result
      end
      |> Helpers.condition_as_failure
    in
    check
      (list (list (pair string Helpers.value)))
      "the stored program ran in place of its name"
      [["name", Concepts.Value.String "Alaric"]]
      (bindings projected)

  let run_a_program_within_a_state conn =
    let projected =
      begin
        let open Utilities.Result in
        let* relation = H.relation conn ["name"; "age"] [employee "Alaric" 42] in
        let* evaluators = namespace ["fol", Rnt.Evaluators.FOL.make ()] in
        let* system = namespace ["evaluator", evaluators] in
        let* root = namespace ["system", system] in
        let* within = namespace ["employee", relation] in
        Kernel.EphemeralRelation.of_program ~within heading (Rnt.Evaluators.FOL.program ~root names)
        |> drain
      end
      |> Helpers.condition_as_failure
    in
    check
      (list (list (pair string Helpers.value)))
      "the program found its evaluator under the root and read the state it was given"
      [["name", Concepts.Value.String "Alaric"]]
      (bindings projected)

  let refuse_a_program_that_reads_itself conn =
    let expanded =
      begin
        let open Utilities.Result in
        let stored_path = Kernel.Path.("stored" @/ this) in
        let* stored = store conn (Rnt.Evaluators.FOL.Base stored_path) in
        let* root = namespace ["stored", stored] in
        Rnt.Evaluators.FOL.(instantiate root (Base stored_path))
      end
    in
    check bool "the expansion stopped at the cycle" true
      ( match expanded with
      | Error condition ->
          BatString.starts_with (Concepts.Condition.to_string_hum condition) "cyclic-program"
      | Ok _ -> false )

  let shape modes =
    List.map
      (fun {Concepts.Mode.bound; yields} ->
        BatSet.String.elements bound, Concepts.Cardinality.to_string yields )
      modes

  let a_projection_keeps_the_modes_it_can_bind conn =
    let ask term f =
      begin
        let open Utilities.Result in
        let* relation =
          H.relation conn ["name"; "age"] [employee "Alaric" 42; employee "Brunhild" 30]
        in
        let* result = eval (directory ["employee", relation]) term in
        Protocols.Handle.releasing result (fun () ->
            Result.bind (Protocols.Relation.require result) f )
      end
      |> Helpers.condition_as_failure
    in
    let modes term = shape (ask term Protocols.Relation.modes) in
    let holds term tuple = ask term (fun r -> Protocols.Relation.contains r tuple) in
    check
      (list (pair (list string) string))
      "a base relation keeps the lookup by hash"
      [[], "finite"; ["age"; "name"], "bounded(1)"]
      (modes employees);
    check
      (list (pair (list string) string))
      "its projection keeps only what a projected tuple can bind"
      [[], "finite"]
      (modes names);
    check bool "the base decides by its own test" true (holds employees (employee "Alaric" 42));
    check bool "the projection decides by reading" true (holds names (named "Alaric"));
    check bool "and refuses a stranger" false (holds names (named "Gunther"))

  let counter ?(produced = ref 0) ?(closed = ref false) () =
    let description =
      BatMap.String.singleton "value" {Protocols.Schematics.domain= "integer"; provenance= []}
    in
    let rec count ~yield n =
      incr produced;
      yield
        { Concepts.Tuple.type_= "counter";
          attributes= BatMap.String.singleton "value" (Concepts.Value.Integer n) };
      count ~yield (n + 1)
    in
    Kernel.EphemeralRelation.instantiate description
      ~modes:(fun () -> Ok [Concepts.(Mode.mode [] Cardinality.Countable)])
      (Kernel.EphemeralRelation.temporary description)
      (fun () -> Ok (Kernel.Generator.cursor_of ~finally:(fun () -> closed := true) (count 0)))

  let values source =
    Rnt.Evaluators.FOL.(execute (Project (Base source, BatFingerTree.singleton "value")))

  let pull_one_tuple_at_a_time () =
    let produced = ref 0 and closed = ref false in
    let first =
      begin
        let open Utilities.Result in
        let* result = values (counter ~produced ~closed ()) in
        let* first = Protocols.Enumerable.scan result Protocols.Cursor.next in
        Protocols.Handle.release result; Ok first
      end
      |> Helpers.condition_as_failure
    in
    check bool "a tuple came through" true (Option.is_some first);
    check int "the source produced only that tuple" 1 !produced;
    check bool "and was closed with its consumer" true !closed

  let an_endless_projection_cannot_decide () =
    let asked =
      begin
        let open Utilities.Result in
        let* result = values (counter ()) in
        let* relation = Protocols.Relation.require result in
        Protocols.Relation.contains relation
          { Concepts.Tuple.type_= "counter";
            attributes= BatMap.String.singleton "value" (Concepts.Value.Integer 7) }
      end
    in
    check bool "it fails as undecidable instead of reading without end" true
      ( match asked with
      | Error condition ->
          BatString.starts_with
            (Concepts.Condition.to_string_hum condition)
            "undecidable-membership"
      | Ok _ -> false )

  let a_result_owns_the_relations_of_its_plan () =
    let released = ref false in
    let tracker =
      Protocols.Handle.make
        object
          method reference = true
          method release = released := true
          method is_managed = false
          method hash = Concepts.Hash.hash_of_int 0
          method to_string = "tracker"
          method protocols : Protocols.Handle.protocol list = []
        end
    in
    let relation =
      Kernel.EphemeralRelation.instantiate ~inputs:[tracker] heading
        ~modes:(fun () -> Ok [])
        (Kernel.EphemeralRelation.temporary heading)
        (fun () -> Ok (Kernel.Generator.cursor_of (fun ~yield:_ -> Ok ())))
    in
    let result = Rnt.Evaluators.FOL.(execute (Base relation)) |> Helpers.condition_as_failure in
    check bool "the relation in the plan lives as long as the result" false !released;
    Protocols.Handle.release result;
    check bool "and is released with it" true !released

  let suite =
    ( "evaluators/fol",
      [ test_case "scan-a-base-relation" `Quick (H.with_connection scan_a_base_relation "fol-test");
        test_case "project-away-an-attribute" `Quick
          (H.with_connection project_away_an_attribute "fol-test");
        test_case "instantiate-a-program" `Quick
          (H.with_connection instantiate_a_program "fol-test");
        test_case "expand-a-stored-program" `Quick
          (H.with_connection expand_a_stored_program "fol-test");
        test_case "run-a-program-within-a-state" `Quick
          (H.with_connection run_a_program_within_a_state "fol-test");
        test_case "refuse-a-program-that-reads-itself" `Quick
          (H.with_connection refuse_a_program_that_reads_itself "fol-test");
        test_case "a-projection-keeps-the-modes-it-can-bind" `Quick
          (H.with_connection a_projection_keeps_the_modes_it_can_bind "fol-test");
        test_case "pull-one-tuple-at-a-time" `Quick pull_one_tuple_at_a_time;
        test_case "an-endless-projection-cannot-decide" `Quick an_endless_projection_cannot_decide;
        test_case "a-result-owns-the-relations-of-its-plan" `Quick
          a_result_owns_the_relations_of_its_plan ] )
end

module LMDB = Make (Rnt.Backend.Storage.LMDB) (Helpers.Storage.LMDB_Configurator)

let suites () = [LMDB.suite]
