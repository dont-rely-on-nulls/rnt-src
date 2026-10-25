open Rnt

module Error = struct
  open Concepts.Condition

  let closed () = condition "beam-closed" "The BEAM node is gone" empty

  let unimplemented () =
    condition "beam-unimplemented" "The beam evaluator cannot do this yet" empty

  let taken () = condition "beam-taken" "An evaluator is already registered as karuta:beam" empty
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

module Make (T : TRANSPORT) = struct
  class evaluator (transport : T.t) =
    object (self)
      inherit Kernel.Lifecycle.counted
      inherit Kernel.Identity.of_id
      method to_string = name
      method destroy = T.stop transport

      method parse : string -> (Kernel.Program.kind, Concepts.Condition.condition) result =
        fun _ -> Error (Error.unimplemented ())

      method eval :
          Kernel.Program.kind ->
          Protocols.Handle.t list ->
          within:Protocols.Handle.t ->
          (Protocols.Handle.t, Concepts.Condition.condition) result =
        fun _ _ ~within:_ -> Error (Error.unimplemented ())

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
