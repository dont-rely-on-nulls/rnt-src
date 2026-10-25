open Rnt
module Translator = Subsystem.Karuta.Translator
module Gen = QCheck2.Gen

let value =
  Gen.oneof
    [ Gen.map (fun s -> Concepts.Value.String s) Gen.string_small;
      Gen.map
        (fun n -> Concepts.Value.Integer n)
        (Gen.oneof [Gen.int; Gen.oneof_list [min_int; max_int]]) ]

let tuple =
  Gen.map2
    (fun type_ attributes -> {Concepts.Tuple.type_; attributes= BatMap.String.of_list attributes})
    Gen.string_small
    (Gen.list_small (Gen.pair Gen.string_small value))

let print tuple = tuple.Concepts.Tuple.type_ ^ " " ^ Concepts.Tuple.to_string tuple

let same (a : Concepts.Tuple.t) (b : Concepts.Tuple.t) =
  a.type_ = b.type_ && BatMap.String.equal Concepts.Value.equal a.attributes b.attributes

let decodes_to_itself =
  QCheck2.Test.make ~name:"a tuple decodes to itself" ~print tuple (fun tuple ->
      match Translator.decode (Translator.encode tuple) with
      | Ok decoded -> same tuple decoded
      | Error _ -> false )

let a_cut_term_is_refused =
  QCheck2.Test.make ~name:"a cut term is refused" ~print tuple (fun tuple ->
      let bytes = Translator.encode tuple in
      List.init (String.length bytes) (fun n -> Translator.decode (String.sub bytes 0 n))
      |> List.for_all Result.is_error )

let erlang_integers_decode =
  QCheck2.Test.make ~name:"an integer as term_to_binary writes it decodes to itself"
    ~print:string_of_int
    (Gen.oneof [Gen.int_range 0 255; Gen.int_range (-0x8000_0000) 0x7fff_ffff])
    (fun n ->
      let term = Buffer.create 32 in
      Buffer.add_string term
        "\131\104\002\109\000\000\000\001t\116\000\000\000\001\109\000\000\000\001n";
      if n >= 0 && n < 256 then begin
        Buffer.add_uint8 term 97; Buffer.add_uint8 term n
      end
      else begin
        Buffer.add_uint8 term 98;
        Buffer.add_int32_be term (Int32.of_int n)
      end;
      match Translator.decode (Buffer.contents term) with
      | Ok {attributes; _} -> BatMap.String.bindings attributes = ["n", Concepts.Value.Integer n]
      | Error _ -> false )

let suites () =
  [ ( "karuta/translator",
      List.map QCheck_alcotest.to_alcotest
        [decodes_to_itself; a_cut_term_is_refused; erlang_integers_decode] ) ]
