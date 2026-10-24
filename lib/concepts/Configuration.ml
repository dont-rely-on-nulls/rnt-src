(* @uses Condition -- builds syntax/type errors *)

open Sexplib.Sexp

type term = Sexplib.Sexp.t

module Error = struct
  open Condition

  let missing_key key =
    condition "missing-key" "An expected key was not found" ("key" |=| Value.String key)

  let mismatched_tag expected actual =
    condition "mismatched-tag" "A tag did not match what was expected"
      ("expected" |=| Value.String expected & "actual" |=| Value.String actual)

  let syntax_error form =
    condition "syntax-error" "Syntax error"
      ("form" |=| Value.String (Sexplib.Sexp.to_string_hum form))

  let tagless_form form =
    condition "tagless-form" "Cannot take tag of an atom or an empty list"
      ~parent:(syntax_error form) empty

  let bodyless_form form =
    condition "bodyless-form" "Cannot take body of an atom or an empty list"
      ~parent:(syntax_error form) empty

  let malformed_pair form =
    condition "malformed-pair" "Expected a pair of key and value" ~parent:(syntax_error form) empty

  let expected_atom form =
    condition "expected-atom" "Expected atom but got list structure" ~parent:(syntax_error form)
      empty

  let not_a_number form =
    condition "not-a-number" "Could not parse value as number" ~parent:(syntax_error form) empty
end

let term_of_sexp t = t
let tag_of = function List (Atom tag :: _) -> Ok tag | form -> Error (Error.tagless_form form)
let body_of = function List (_ :: body) -> Ok body | form -> Error (Error.bodyless_form form)

type dictionary = (string, term) BatMap.t

let value_for k ?default d =
  let default = Option.to_result ~none:(Error.missing_key k) default in
  BatMap.find_opt k d |> Option.map (fun x -> Ok x) |> Option.value ~default

let as_dictionary t tag : (dictionary, Condition.condition) result =
  let open Utilities.Result in
  let strip_tag (tag : string) (t : term) =
    let* tag' = tag_of t in
    if tag' = tag then body_of t else Error (Error.mismatched_tag tag tag')
  in
  let as_dictionary' pairs =
    List.fold_right
      (fun term dict ->
        let* dict = dict in
        match term with
        | List [Atom k; v] -> Ok (BatMap.add k v dict)
        | p -> Error (Error.malformed_pair p) )
      pairs (Ok BatMap.empty)
  in
  strip_tag tag t |>> as_dictionary'

let as_string = function Atom s -> Ok s | form -> Error (Error.expected_atom form)

let as_int f =
  let open Utilities.Result in
  let* s = as_string f in
  int_of_string_opt s |> Option.to_result ~none:(Error.not_a_number f)
