open Rnt

module Error = struct
  open Concepts.Condition

  let closed () = condition "beam-closed" "The BEAM node is gone" empty
  let taken () = condition "beam-taken" "An evaluator is already registered as karuta:beam" empty

  let malformed () =
    condition "malformed-beam-program"
      "A beam program is not {Module, Function, #{Name => Domain}} of binaries" empty

  let not_a_program () =
    condition "not-a-beam-program" "The evaluator was given a program of another kind" empty

  let inputs () = condition "beam-program-inputs" "A beam program takes no inputs" empty

  let failed message =
    condition "beam-failed" "The BEAM node failed to answer a call"
      ("message" |=| Concepts.Value.String message)

  let unexpected () =
    condition "unexpected-beam-message" "The BEAM node said something out of turn" empty
end

module type TRANSPORT = sig
  type t

  val send : t -> string -> (unit, Concepts.Condition.condition) result
  val receive : t -> (string, Concepts.Condition.condition) result
  val stop : t -> unit
end

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
      Ok (really_input_string input (Int32.to_int (String.get_int32_be header 0) land 0xffff_ffff))
    with End_of_file | Sys_error _ -> Error (Error.closed ())

  let start ?(erl = "erl") directories =
    let boot =
      "try [{module, _} = code:load_abs(filename:rootname(F)) || D <- init:get_plain_arguments(), \
       F <- filelib:wildcard(D ++ \"/*.beam\")], 'rnt-node':start() catch C:R:S -> \
       io:format(standard_error, \"~p:~p~n~p~n\", [C, R, S]), halt(1) end."
    in
    match
      Unix.open_process_args erl
        (Array.of_list ([erl; "-noshell"; "-noinput"; "-eval"; boot; "-extra"] @ directories))
    with
    | input, output -> Ok {input; output}
    | exception Unix.Unix_error _ -> Error (Error.closed ())

  let stop {input; output} = ignore (Unix.close_process (input, output))
end

let name = "karuta"

type program =
  {module_: string; function_: string; heading: Protocols.Schematics.relation_description}

type Kernel.Program.kind += Beam of program

let decode source =
  let domain _ = function
    | Concepts.Value.String domain -> Some {Protocols.Schematics.domain; provenance= []}
    | Concepts.Value.Integer _ -> None
  in
  match Translator.read 3 source with
  | Some ([module_; function_], attributes)
    when String.length module_ <= 0xffff && String.length function_ <= 0xffff ->
      let heading = BatMap.String.filter_map domain attributes in
      if BatMap.String.cardinal heading = BatMap.String.cardinal attributes then
        Ok (Beam {module_; function_; heading})
      else Error (Error.malformed ())
  | _ -> Error (Error.malformed ())

module Make (T : TRANSPORT) = struct
  module Poll = struct
    let invoke_message id {module_; function_; _} =
      let buffer = Buffer.create 64 in
      Buffer.add_char buffer 'i';
      Buffer.add_int64_be buffer (Int64.of_int id);
      List.iter
        (fun name ->
          Buffer.add_uint16_be buffer (String.length name);
          Buffer.add_string buffer name )
        [module_; function_];
      Buffer.contents buffer

    let fetch_message id limit =
      let buffer = Buffer.create 13 in
      Buffer.add_char buffer 'f';
      Buffer.add_int64_be buffer (Int64.of_int id);
      Buffer.add_int32_be buffer (Int32.of_int (max 0 (min limit 0xffff_ffff)));
      Buffer.contents buffer

    let close_message id =
      let buffer = Buffer.create 9 in
      Buffer.add_char buffer 'c';
      Buffer.add_int64_be buffer (Int64.of_int id);
      Buffer.contents buffer

    let batch_of message =
      let open Utilities.Result in
      let length = String.length message in
      let rec tuples at read =
        if at = length then Ok (List.rev read)
        else if at + 4 > length then Error (Error.unexpected ())
        else
          let size = Int32.to_int (String.get_int32_be message at) land 0xffff_ffff in
          if at + 4 + size > length then Error (Error.unexpected ())
          else
            let* tuple = Translator.decode (String.sub message (at + 4) size) in
            tuples (at + 4 + size) (tuple :: read)
      in
      if length < 2 then Error (Error.unexpected ())
      else
        let* read = tuples 2 [] in
        Ok {Protocols.Cursor.tuples= BatFingerTree.of_list read; exhausted= message.[1] <> '\000'}

    let await transport =
      let open Utilities.Result in
      let* message = T.receive transport in
      match if message = "" then ' ' else message.[0] with
      | 'b' -> batch_of message
      | 'e' -> Error (Error.failed (String.sub message 1 (String.length message - 1)))
      | _ -> Error (Error.unexpected ())

    class t transport =
      object (self)
        inherit Kernel.Lifecycle.counted
        inherit Kernel.Identity.of_id
        method to_string = name

        method fetch limit =
          Result.bind
            (T.send transport (fetch_message (Oo.id self) limit))
            (fun () -> await transport)

        method destroy = ignore (T.send transport (close_message (Oo.id self)))
        method protocols : Protocols.Handle.protocol list = Protocols.[Cursor.make self]
      end

    let start transport program =
      let poll = new t transport in
      T.send transport (invoke_message (Oo.id poll) program)
      |> Result.map (fun () -> Protocols.Handle.make poll)
  end

  class evaluator (transport : T.t) =
    object (self)
      inherit Kernel.Lifecycle.counted
      inherit Kernel.Identity.of_id
      method to_string = name
      method destroy = T.stop transport
      method parse source = decode source

      method eval :
          Kernel.Program.kind ->
          Protocols.Handle.t list ->
          within:Protocols.Handle.t ->
          (Protocols.Handle.t, Concepts.Condition.condition) result =
        fun kind inputs ~within:_ ->
          match kind, inputs with
          | Beam program, [] ->
              Ok
                (Kernel.EphemeralRelation.instantiate program.heading
                   ~modes:(fun () -> Ok [Concepts.Mode.mode [] Concepts.Cardinality.Countable])
                   (Kernel.EphemeralRelation.temporary program.heading)
                   (fun () -> Poll.start transport program) )
          | Beam _, _ -> Error (Error.inputs ())
          | _ -> Error (Error.not_a_program ())

      method protocols : Protocols.Handle.protocol list = [Protocols.Evaluator.make self]
    end
end

module Node = Make (Port)

let register root directories =
  let open Utilities.Result in
  let* port = Port.start directories in
  let evaluator = Protocols.Handle.make (new Node.evaluator port) in
  let bound =
    let* () = Kernel.Initialization.mount root name in
    Kernel.Path.update root Kernel.Path.(name @/ "evaluator" @/ this) "beam" None (Some evaluator)
  in
  match bound with
  | Ok true -> Ok ()
  | Ok false ->
      Protocols.Handle.release evaluator;
      Error (Error.taken ())
  | Error c ->
      Protocols.Handle.release evaluator;
      Error c
