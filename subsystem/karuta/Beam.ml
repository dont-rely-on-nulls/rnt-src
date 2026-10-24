(* The beam evaluator. Its programs are functions on a BEAM node, each
   taking one relation per input and giving back a relation of the
   heading the program declares. rnt-node.lfe serves them. Tuples cross
   as Translator writes them, and a message is a byte for its kind
   followed by big-endian integers and binaries:

     RNT   i Cursor:32 M:16 Module F:16 Function Reader:32...  invoke
     RNT   f Cursor:32 Limit:32                                 fetch
     RNT   c Cursor:32                                          close
     node  n Reader:32 Limit:32                                 next
     node  l (Size:32 Segment)...                               lookup
     both  b Exhausted:8 (Size:32 Tuple)...                     a batch
     RNT   r Reader:32                                          a reader
     both  e Message                                            a failure

   fetch and next are answered with a batch or a failure, lookup with a
   reader or a failure, invoke and close not at all. The node applies
   the function at the first fetch, so a function that cannot be applied
   fails it. Calls nest: until its answer comes, whoever waits serves the
   calls that come instead.

   lookup asks for the relation at a path, within what the program runs
   within, and FOL answers it. The node reads it with next like an
   input, and the cursor being fetched, whose program asked, keeps it
   until it closes. *)

open Rnt

module Error = struct
  open Concepts.Condition

  let not_a_program () =
    condition "not-a-beam-program" "The evaluator was given a program of another kind" empty

  let failed message =
    condition "beam-failed" "The BEAM node failed to answer a call"
      ("message" |=| Concepts.Value.String message)

  let closed () = condition "beam-closed" "The BEAM node is gone" empty

  let unexpected () =
    condition "unexpected-beam-message" "The BEAM node said something out of turn" empty

  let unheld_input () =
    condition "unheld-input" "An input could not be held for as long as the program needs it" empty
end

module type TRANSPORT = sig
  type t

  val send : t -> string -> (unit, Concepts.Condition.condition) result
  val receive : t -> (string, Concepts.Condition.condition) result
end

(* A node RNT starts as its child and speaks to over the child's stdin
   and stdout, each message behind its length in four bytes, as a port
   opened with {packet, 4} frames it. *)
module Port = struct
  type t = {input: in_channel; output: out_channel}

  let send {output; _} message =
    let header = Bytes.create 4 in
    Bytes.set_int32_be header 0 (Int32.of_int (String.length message));
    try
      output_bytes output header;
      output_string output message;
      Ok (flush output)
    with Sys_error _ -> Error (Error.closed ())

  let receive {input; _} =
    try
      let header = really_input_string input 4 in
      Ok (really_input_string input (Int32.to_int (String.get_int32_be header 0)))
    with End_of_file | Sys_error _ -> Error (Error.closed ())

  (* The node compiles every LFE module in [directories], which must
     hold rnt.lfe and rnt-node.lfe, and serves until [stop] closes its
     stdin. If it cannot, it says why on stderr and halts. It is started
     with erl and not lfe, whose shell would read stdin, so LFE has to be
     where erl finds it, as ERL_LIBS says. *)
  let start ?(erl = "erl") directories =
    let boot =
      "try [begin {ok, Ms, _} = lfe_comp:file(F, [binary, return]), [{module, M} = \
       code:load_binary(M, F, B) || {ok, M, B, _} <- Ms] end || D <- init:get_plain_arguments(), F \
       <- filelib:wildcard(D ++ \"/*.lfe\")], 'rnt-node':start() catch C:R:S -> \
       io:format(standard_error, \"~p:~p~n~p~n\", [C, R, S]), halt(1) end."
    in
    let input, output =
      Unix.open_process_args erl
        (Array.of_list ([erl; "-noshell"; "-noinput"; "-eval"; boot; "-extra"] @ directories))
    in
    {input; output}

  let stop {input; output} = ignore (Unix.close_process (input, output))
end

let subsystem = "karuta"
let language = "beam"
let name = subsystem ^ ":" ^ language

type program =
  {module_: string; function_: string; heading: Protocols.Schematics.relation_description}

type Kernel.Program.kind += Beam of program

module Bencode = Concepts.Encoding.Bencode

let encode {module_; function_; heading} =
  Bencode.Dict
    [ "module", Bencode.String module_;
      "function", Bencode.String function_;
      ( "heading",
        Bencode.Dict
          ( BatMap.String.bindings heading
          |> List.map (fun (attribute, {Protocols.Schematics.domain; _}) ->
              attribute, Bencode.String domain ) ) ) ]
  |> Bencode.to_bytes
  |> Bytes.to_string

let decode source =
  let open Utilities.Result in
  let* program = Bencode.of_bytes (Bytes.of_string source) in
  let* module_ = Concepts.Encoding.Field.require_string "module" program in
  let* function_ = Concepts.Encoding.Field.require_string "function" program in
  let* heading = Bencode.field "heading" program |>> Bencode.as_dict in
  let* heading =
    heading
    |> List.map (fun (attribute, domain) ->
        Bencode.as_string domain
        |> Result.map (fun domain -> attribute, {Protocols.Schematics.domain; provenance= []}) )
    |> Utilities.List.sequence
  in
  Ok {module_; function_; heading= BatMap.String.of_list heading}

let int32 buffer n = Buffer.add_int32_be buffer (Int32.of_int n)

let invoke_message cursor {module_; function_; _} readers =
  let buffer = Buffer.create 64 in
  Buffer.add_char buffer 'i';
  int32 buffer cursor;
  List.iter
    (fun name ->
      Buffer.add_uint16_be buffer (String.length name);
      Buffer.add_string buffer name )
    [module_; function_];
  List.iter (int32 buffer) readers;
  Buffer.contents buffer

let fetch_message cursor limit =
  let buffer = Buffer.create 9 in
  Buffer.add_char buffer 'f'; int32 buffer cursor; int32 buffer limit; Buffer.contents buffer

let close_message cursor =
  let buffer = Buffer.create 5 in
  Buffer.add_char buffer 'c'; int32 buffer cursor; Buffer.contents buffer

let batch_message {Protocols.Cursor.tuples; exhausted} =
  let buffer = Buffer.create 256 in
  Buffer.add_char buffer 'b';
  Buffer.add_uint8 buffer (Bool.to_int exhausted);
  BatFingerTree.iter
    (fun tuple ->
      let term = Translator.encode tuple in
      int32 buffer (String.length term);
      Buffer.add_string buffer term )
    tuples;
  Buffer.contents buffer

let reader_message reader =
  let buffer = Buffer.create 5 in
  Buffer.add_char buffer 'r'; int32 buffer reader; Buffer.contents buffer

let failure_message condition = "e" ^ Concepts.Condition.to_string_hum condition

(* The pieces of [message] from [at] on, each behind its size in four bytes. *)
let chunks message at =
  let length = String.length message in
  let rec read at pieces =
    if at = length then Ok (List.rev pieces)
    else if at + 4 > length then Error (Error.unexpected ())
    else
      let size = Int32.to_int (String.get_int32_be message at) land 0xffff_ffff in
      if at + 4 + size > length then Error (Error.unexpected ())
      else read (at + 4 + size) (String.sub message (at + 4) size :: pieces)
  in
  read at []

let batch_of message =
  let open Utilities.Result in
  let* terms = chunks message 2 in
  let* tuples = List.map Translator.decode terms |> Utilities.List.sequence in
  Ok {Protocols.Cursor.tuples= BatFingerTree.of_list tuples; exhausted= message.[1] <> '\000'}

module Make (T : TRANSPORT) = struct
  (* The root programs find their evaluators in, the cursors the node
     reads through us by the reader id it knows each by, and the last id
     given to a reader or a cursor. *)
  type node =
    { root: Protocols.Handle.t;
      transport: T.t;
      readers: (int, Protocols.Handle.t) Hashtbl.t;
      mutable last: int }

  let fresh node =
    node.last <- node.last + 1;
    node.last

  let next node message =
    let open Utilities.Result in
    let reader = Int32.to_int (String.get_int32_be message 1) in
    let limit = Int32.to_int (String.get_int32_be message 5) in
    let* cursor =
      Hashtbl.find_opt node.readers reader |> Option.to_result ~none:(Error.unexpected ())
    in
    let* scan = Protocols.Cursor.require cursor in
    Protocols.Cursor.fetch scan limit

  let lookup node within message =
    let open Utilities.Result in
    let* path = chunks message 1 in
    let program =
      Evaluators.FOL.program ~root:node.root (Evaluators.FOL.Base (Kernel.Path.of_list path))
    in
    let* relation =
      Protocols.Handle.releasing program (fun () ->
          let* executable = Protocols.Executable.require program in
          Protocols.Executable.invoke executable [] ~within )
    in
    let* cursor = Kernel.EphemeralRelation.enumerate_owned relation in
    let reader = fresh node in
    Hashtbl.replace node.readers reader cursor;
    Ok reader

  (* [own] keeps a reader the node looked up for the cursor being fetched. *)
  let rec await node within own =
    let open Utilities.Result in
    let* message = T.receive node.transport in
    let reply answer =
      let* () = T.send node.transport answer in
      await node within own
    in
    match if message = "" then ' ' else message.[0] with
    | 'b' when String.length message >= 2 -> batch_of message
    | 'e' -> Error (Error.failed (String.sub message 1 (String.length message - 1)))
    | 'n' when String.length message = 9 -> (
        reply
        @@
        match next node message with
        | Ok batch -> batch_message batch
        | Error c -> failure_message c )
    | 'l' -> (
        reply
        @@
        match lookup node within message with
        | Ok reader -> own reader; reader_message reader
        | Error c -> failure_message c )
    | _ -> Error (Error.unexpected ())

  let forget node readers =
    List.iter
      (fun reader ->
        Hashtbl.find_opt node.readers reader |> Option.iter Protocols.Handle.release;
        Hashtbl.remove node.readers reader )
      readers

  (* It keeps the readers of its inputs, and of what its program looked up. *)
  class cursor node id inputs within =
    object (self)
      inherit Kernel.Lifecycle.counted
      inherit Kernel.Identity.of_id
      val mutable readers = inputs
      method to_string = "beam-cursor"

      method fetch limit =
        Result.bind
          (T.send node.transport (fetch_message id limit))
          (fun () -> await node within (fun reader -> readers <- reader :: readers))

      method destroy =
        ignore (T.send node.transport (close_message id));
        forget node readers

      method protocols : Protocols.Handle.protocol list = Protocols.[Cursor.make self]
    end

  let open_readers node inputs =
    Utilities.List.foldm_left
      (fun readers input ->
        match Protocols.Enumerable.cursor input with
        | Ok cursor ->
            let reader = fresh node in
            Hashtbl.replace node.readers reader cursor;
            Ok (reader :: readers)
        | Error c -> forget node readers; Error c )
      [] inputs
    |> Result.map List.rev

  let invoke node program inputs ~within =
    let open Utilities.Result in
    let* readers = open_readers node inputs in
    let id = fresh node in
    match T.send node.transport (invoke_message id program readers) with
    | Ok () -> Ok (Protocols.Handle.make (new cursor node id readers within))
    | Error c -> forget node readers; Error c

  (* The relation reads its inputs each time it is enumerated, so it holds them. *)
  let hold inputs =
    let held = List.filter_map Protocols.Handle.copy inputs in
    if List.length held = List.length inputs then Ok held
    else begin
      List.iter Protocols.Handle.release held;
      Error (Error.unheld_input ())
    end

  (* It looks relations up within [within] too, so it holds that as well.
     TODO: A program should declare its modes as it declares its heading.
     Until then every program is taken to end. *)
  let generate node program inputs ~within =
    let open Utilities.Result in
    let* held = hold (within :: inputs) in
    match held with
    | [] -> Error (Error.unheld_input ())
    | within :: inputs ->
        Ok
          (Kernel.EphemeralRelation.instantiate ~inputs:held program.heading
             ~modes:(fun () -> Ok [Concepts.Mode.mode [] Concepts.Cardinality.Finite])
             (Kernel.EphemeralRelation.temporary program.heading)
             (fun () -> invoke node program inputs ~within) )

  class evaluator node =
    object (self)
      inherit Kernel.Lifecycle.null
      inherit Kernel.Identity.of_id
      method to_string = "beam-evaluator"
      method parse source = decode source |> Result.map (fun program -> Beam program)

      method eval kind inputs ~within =
        match kind with
        | Beam program -> generate node program inputs ~within
        | _ -> Error (Error.not_a_program ())

      method protocols : Protocols.Handle.protocol list = [Protocols.Evaluator.make self]
    end

  (* \karuta is the subsystem's root, and its programs name the evaluator karuta:beam. *)
  let register root transport =
    let open Utilities.Result in
    let node = {root; transport; readers= Hashtbl.create 8; last= 0} in
    let* _ = Kernel.Initialization.mount root subsystem in
    let* _ =
      Kernel.Path.update root
        Kernel.Path.(subsystem @/ "evaluator" @/ this)
        language None
        (Some (Protocols.Handle.make (new evaluator node)))
    in
    Ok ()
end

let program ?root ~module_ ~function_ heading =
  let program = {module_; function_; heading} in
  Kernel.Program.make ?root ~evaluator:name ~source:(encode program) (Beam program)
