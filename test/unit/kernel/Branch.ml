open Alcotest
module K = Rnt.Kernel
module P = Rnt.Protocols
module C = Rnt.Concepts

let ok = Helpers.condition_as_failure
let library = {K.Scope.multigroup= "library"; schema= "default"}
let master = K.Path.("system" @/ "branch" @/ "master" @/ this)
let under a b = K.Path.(of_list (to_list a @ to_list b))
let shelf = K.Scope.path library "shelf"
let s v = C.Value.String v
let title = BatMap.String.singleton "title" {P.Schematics.domain= "string"; provenance= []}
let book t = {C.Tuple.type_= "book"; attributes= BatMap.String.singleton "title" (s t)}
let books titles = K.EphemeralRelation.literal title (List.map book titles)
let titles relation = ok (Helpers.titles relation)
let read root path = titles (ok (K.Path.lookup root path))

(* shelf is a stored FOL program reading book where it is stored *)
let shelved =
  K.EphemeralRelation.of_program title
    Rnt.Evaluators.FOL.(program (Base (K.Scope.path library "book")))

let publish ?denials root changes =
  ok (K.Scope.publish ?denials root ~branch:"master" ~home:library changes)

let fresh books' =
  let root = ok (Rnt.Scratch.root ()) in
  publish root ["book", Some (books books'); "shelf", Some shelved];
  root

let address handle = P.Addressable.address (Option.get (P.Addressable.from handle))

let reads_as_of_each_state () =
  let root = fresh ["Codd"] in
  publish root ["book", Some (books ["Codd"; "Date"])];
  check (list Helpers.value) "the head's view reads the books as they are"
    [s "Codd"; s "Date"]
    (read root (under master shelf));
  check (list Helpers.value) "the previous state's view reads them as they were"
    [s "Codd"]
    (read root (under master K.Path.("previous" @/ shelf)))

let a_batch_is_one_successor () =
  let root = fresh ["Codd"] in
  let head = ok (K.Path.lookup root master) in
  publish root ["book", Some (books ["Date"]); "loan", Some (books ["Codd"])];
  let next = ok (K.Path.lookup root master) in
  let previous = ok (K.Path.lookup next K.Path.("previous" @/ this)) in
  check bool "two changes, one state after the head" true
    (C.Hash.hash_equals (address previous) (address head));
  let changed =
    ok
      (K.Path.diff
         (ok (K.Path.lookup head K.Path.("multigroup" @/ this)))
         (ok (K.Path.lookup next K.Path.("multigroup" @/ this))) )
  in
  check
    (list (list string))
    "the diff names what changed and nothing else"
    [ ["library"; "schema"; "default"; "relation"; "book"];
      ["library"; "schema"; "default"; "relation"; "loan"] ]
    (List.map K.Path.to_list changed)

let unbinding_removes_a_relation () =
  let root = fresh ["Codd"] in
  publish root ["shelf", None];
  check bool "shelf is gone" true (Result.is_error (K.Path.lookup root (under master shelf)));
  check (list Helpers.value) "book stays"
    [s "Codd"]
    (read root (under master (K.Scope.path library "book")))

let a_scope_reads_names_from_its_home () =
  let root = fresh ["Codd"] in
  K.Scope.publish root ~branch:"master"
    ~home:{K.Scope.multigroup= "store"; schema= "default"}
    ["stock", Some (books ["Date"]); "archive:old", Some (books ["Codd"])]
  |> ok;
  let scope = ok (K.Scope.of_root root ~branch:"master" library) in
  let directory = Option.get (P.Directory.from scope) in
  let found name = ok (P.Directory.find directory name) |> Option.map titles in
  check
    (option (list Helpers.value))
    "a bare name is the home schema's"
    (Some [s "Codd"])
    (found "book");
  check
    (option (list Helpers.value))
    "schema:name stays in the home multigroup"
    (Some [s "Codd"])
    (found "default:book");
  check
    (option (list Helpers.value))
    "multigroup:schema:name leaves it"
    (Some [s "Date"])
    (found "store:default:stock");
  check (option (list Helpers.value)) "what is not there is not found" None (found "stock");
  check
    (option (list Helpers.value))
    "four parts name an attribute, not a relation" None
    (found "library:default:book:title");
  let catalog = ok (K.Scope.catalog (ok (K.Scope.require scope))) in
  check (list string) "the catalog is every relation of the state"
    ["library:default:book"; "library:default:shelf"; "store:archive:old"; "store:default:stock"]
    (List.sort compare catalog);
  check (option string) "a qualified attribute names the relation's own" (Some "title")
    (K.Scope.attribute library "book" "library:default:book:title");
  check (option string) "but not another relation's" None
    (K.Scope.attribute library "book" "shelf:title")

type K.Program.kind += Title of string | Endless | Shout of K.Path.t

let endless () =
  K.EphemeralRelation.instantiate title
    ~modes:(fun () -> Ok [C.(Mode.mode [] Cardinality.Countable)])
    (K.EphemeralRelation.temporary title)
    (fun () ->
      Ok
        (K.Generator.cursor_of (fun ~yield ->
             let rec from n =
               yield (book (string_of_int n));
               from (n + 1)
             in
             from 0 ) ) )

(* A toy language: "endless" answers titles without end, "shout r" the
   titles of relation r in capitals, and anything else itself as a title. *)
let parse source =
  match String.split_on_char ' ' source with
  | ["endless"] -> Endless
  | ["shout"; name] -> Shout (K.Scope.path library name)
  | _ -> Title source

let shout within path =
  let open Rnt.Utilities.Result in
  let* relation = K.Path.lookup within path in
  let* heard = P.Handle.releasing relation (fun () -> Helpers.titles relation) in
  Ok
    (books
       (List.filter_map
          (function C.Value.String t -> Some (String.uppercase_ascii t) | _ -> None)
          heard ) )

let toy ?(evaluations = ref 0) () =
  P.Handle.make
    object (self)
      inherit K.Lifecycle.null
      inherit K.Identity.of_id
      method to_string = "toy-evaluator"
      method parse source = Ok (parse source)

      method eval kind _ ~within =
        incr evaluations;
        match kind with
        | Title text -> Ok (books [text])
        | Endless -> Ok (endless ())
        | Shout path -> shout within path
        | _ -> Error (C.Condition.condition "foreign-program" "Not a toy program" C.Condition.empty)

      method protocols : P.Handle.protocol list = [P.Evaluator.make self]
    end

let with_toys ?evaluations root =
  ignore (ok (K.Initialization.mount root "toys"));
  ignore
    (ok
       (K.Path.update root
          K.Path.("toys" @/ "evaluator" @/ this)
          "toy" None
          (Some (toy ?evaluations ())) ) )

let toy_program ?root evaluator source = K.Program.make ?root ~evaluator ~source (parse source)

let run root program =
  Result.bind (P.Executable.require program) (fun executable ->
      P.Executable.invoke executable [] ~within:root )

let a_program_runs_through_the_evaluator_it_names () =
  let root = fresh ["Codd"] in
  with_toys root;
  publish root ["named", Some (K.EphemeralRelation.of_program title (toy_program "toys:toy" "this"))];
  check (list Helpers.value) "stored in a branch and read back, it runs"
    [s "this"]
    (read root (under master (K.Scope.path library "named")));
  check (list Helpers.value) "run directly, it runs"
    [s "that"]
    (titles (ok (run root (toy_program ~root "toys:toy" "that"))));
  check bool "an unqualified name is the system's" true
    (Result.is_error (run root (toy_program ~root "toy" "that")))

(* shelf, from fresh, is a FOL program reading book *)
let evaluators_read_each_other () =
  let root = fresh ["Codd"] in
  with_toys root;
  let stored name program = name, Some (K.EphemeralRelation.of_program title program) in
  publish root
    [ stored "toy-shelf" (toy_program "toys:toy" "Date");
      stored "fol-over-toy" Rnt.Evaluators.FOL.(program (Base (K.Scope.path library "toy-shelf")));
      stored "toy-over-fol" (toy_program "toys:toy" "shout shelf") ];
  check (list Helpers.value) "FOL reads the relation a toy program generates"
    [s "Date"]
    (read root (under master (K.Scope.path library "fol-over-toy")));
  check (list Helpers.value) "a toy program shouts the relation a FOL program generates"
    [s "CODD"]
    (read root (under master (K.Scope.path library "toy-over-fol")))

(* shelf, stored as a denial, says no book may be shelved *)
let denied state = List.map fst (ok (P.Admission.check (ok (P.Admission.require state))))
let no_books = "\\multigroup\\library\\denial\\no-books"

let a_head_moves_only_to_an_admitted_state () =
  let root = fresh [] in
  publish root ~denials:["no-books", Some shelved] [];
  let head = ok (K.Path.lookup root master) in
  check (list string) "the head is admitted" [] (denied head);
  let proposed =
    ok (K.Path.assoc_all head [K.Scope.relations library, "book", Some (books ["Codd"])])
  in
  check (list string) "a state with a book is not, and says by which denial" [no_books]
    (denied proposed);
  check bool "publishing it is refused" true
    (Result.is_error
       (K.Scope.publish root ~branch:"master" ~home:library ["book", Some (books ["Codd"])]) );
  check bool "and the head stays" true
    (C.Hash.hash_equals (address head) (address (ok (K.Path.lookup root master))))

(* a denial of multigroup audit reads library's books *)
let a_rule_spans_multigroups () =
  let root = fresh [] in
  publish root ~denials:["audit:no-books", Some shelved] ["loan", Some (books ["Codd"])];
  check bool "a commit to library is judged by audit" true
    (Result.is_error
       (K.Scope.publish root ~branch:"master" ~home:library ["book", Some (books ["Codd"])]) );
  check (list Helpers.value) "one audit's denial does not mind lands"
    [s "Codd"]
    (read root (under master (K.Scope.path library "loan")))

let a_denial_without_end_cannot_be_installed () =
  let root = fresh [] in
  with_toys root;
  let endless = K.EphemeralRelation.of_program title (toy_program "toys:toy" "endless") in
  match
    K.Scope.publish root ~branch:"master" ~home:library ~denials:["endless", Some endless] []
  with
  | Ok () -> fail "a denial without end was installed"
  | Error condition ->
      check bool "the state holding it cannot be judged" true
        (BatString.starts_with (C.Condition.to_string_hum condition) "unjudgeable-denial")

let a_denial_program_runs_once_per_judgement () =
  let root = fresh [] in
  let evaluations = ref 0 in
  with_toys ~evaluations root;
  let dated = K.EphemeralRelation.of_program title (toy_program "toys:toy" "Date") in
  check bool "a denial holding a book refuses the commit" true
    (Result.is_error
       (K.Scope.publish root ~branch:"master" ~home:library ~denials:["dated", Some dated] []) );
  check int "and its program ran once to judge it" 1 !evaluations

let suites () =
  [ ( "kernel/branch",
      [ test_case "reads-as-of-each-state" `Quick reads_as_of_each_state;
        test_case "a-batch-is-one-successor" `Quick a_batch_is_one_successor;
        test_case "unbinding-removes-a-relation" `Quick unbinding_removes_a_relation;
        test_case "a-scope-reads-names-from-its-home" `Quick a_scope_reads_names_from_its_home;
        test_case "a-program-runs-through-the-evaluator-it-names" `Quick
          a_program_runs_through_the_evaluator_it_names;
        test_case "evaluators-read-each-other" `Quick evaluators_read_each_other;
        test_case "a-head-moves-only-to-an-admitted-state" `Quick
          a_head_moves_only_to_an_admitted_state;
        test_case "a-rule-spans-multigroups" `Quick a_rule_spans_multigroups;
        test_case "a-denial-without-end-cannot-be-installed" `Quick
          a_denial_without_end_cannot_be_installed;
        test_case "a-denial-program-runs-once-per-judgement" `Quick
          a_denial_program_runs_once_per_judgement ] ) ]
