module C = struct
  open Ctypes
  open PosixTypes
  open Foreign

  let mdb_result_of_int = function 0 -> Ok () | x -> Error x
  let int_of_mdb_result = function Ok _ -> 0 | Error x -> x
  let mdb_mode_t = mode_t
  let mdb_result = view ~read:mdb_result_of_int ~write:int_of_mdb_result int

  type mdb_env

  let mdb_env : mdb_env structure typ = structure "mdb_env"

  type mdb_dbi = Unsigned.uint

  let mdb_dbi : mdb_dbi typ = uint

  type mdb_txn

  let mdb_txn : mdb_txn structure typ = structure "mdb_txn"

  type mdb_val

  let mdb_val : mdb_val structure typ = structure "mdb_val"
  let mv_size = field mdb_val "mv_size" size_t
  let mv_data = field mdb_val "mv_data" (ptr void)
  let () = seal mdb_val

  let with_output_pointer output_type default body =
    let open Utilities.Result in
    let output_ptr = allocate output_type default in
    let* () = body output_ptr in
    Ok !@output_ptr

  let mdb_env_create = foreign "mdb_env_create" (ptr (ptr mdb_env) @-> returning mdb_result)

  let mdb_env_create' () =
    with_output_pointer (ptr mdb_env) (from_voidp mdb_env null) mdb_env_create

  let mdb_env_open =
    foreign "mdb_env_open" (ptr mdb_env @-> string @-> uint @-> mdb_mode_t @-> returning mdb_result)

  let mdb_env_close = foreign "mdb_env_close" (ptr mdb_env @-> returning void)

  let mdb_env_set_mapsize =
    foreign "mdb_env_set_mapsize" (ptr mdb_env @-> size_t @-> returning mdb_result)

  let mdb_dbi_open =
    foreign "mdb_dbi_open"
      (ptr mdb_txn @-> ptr char @-> uint @-> ptr mdb_dbi @-> returning mdb_result)

  let mdb_dbi_open' txn flags =
    with_output_pointer mdb_dbi (Unsigned.UInt.of_int 0)
      (mdb_dbi_open txn (from_voidp char null) flags)

  let mdb_txn_begin =
    foreign "mdb_txn_begin"
      (ptr mdb_env @-> ptr mdb_txn @-> uint @-> ptr (ptr mdb_txn) @-> returning mdb_result)

  let mdb_txn_begin' env parent flags =
    with_output_pointer (ptr mdb_txn) (from_voidp mdb_txn null) (mdb_txn_begin env parent flags)

  let mdb_txn_commit = foreign "mdb_txn_commit" (ptr mdb_txn @-> returning mdb_result)
  let mdb_txn_abort = foreign "mdb_txn_abort" (ptr mdb_txn @-> returning void)

  (* TODO: make it so that we do not need to copy bytes to a separate array *)
  let carray_of_bytes (b : bytes) =
    let buffer = CArray.make char (Bytes.length b) in
    Bytes.iteri (CArray.set buffer) b;
    buffer

  let bytes_of_carray arr =
    let buffer = Bytes.make (CArray.length arr) (Char.chr 0) in
    CArray.iteri (Bytes.set buffer) arr;
    buffer

  let with_mdb_val (b : bytes) body =
    let buf = carray_of_bytes b in
    let s = make mdb_val in
    setf s mv_size (Unsigned.Size_t.of_int (Bytes.length b));
    setf s mv_data (to_voidp (CArray.start buf));
    (* MDB_val contains a raw pointer, but that pointer doees not keep
       the OCaml array alive through GC. Returning only the structure
       point could allow collection of the buffer before LMDB is done
       with it. The Sys.opaque_identity hides it from OCaml's
       optimizations. *)
    Fun.protect ~finally:(fun () -> ignore (Sys.opaque_identity buf)) (fun () -> body (addr s))

  let bytes_of_mdb_val (s : mdb_val structure) =
    let buf =
      CArray.from_ptr (from_voidp char (getf s mv_data)) (Unsigned.Size_t.to_int (getf s mv_size))
    in
    bytes_of_carray buf

  let mdb_get =
    foreign "mdb_get"
      (ptr mdb_txn @-> mdb_dbi @-> ptr mdb_val @-> ptr mdb_val @-> returning mdb_result)

  let mdb_get' txn dbi key =
    with_mdb_val key (fun key -> with_output_pointer mdb_val (make mdb_val) (mdb_get txn dbi key))
    |> Result.map bytes_of_mdb_val

  let mdb_put =
    foreign "mdb_put"
      (ptr mdb_txn @-> mdb_dbi @-> ptr mdb_val @-> ptr mdb_val @-> uint @-> returning mdb_result)

  let mdb_put' txn dbi key data flags =
    with_mdb_val key (fun key -> with_mdb_val data (fun data -> mdb_put txn dbi key data flags))

  let mdb_strerror = foreign "mdb_strerror" (int @-> returning string)

  type mdb_env_ptr = mdb_env structure ptr
  type mdb_txn_ptr = mdb_txn structure ptr

  let null_txn = from_voidp mdb_txn null

  module Errors = struct
    let mdb_notfound = -30798
  end

  module Flags = struct
    let mdb_notls = Unsigned.UInt.of_int 0x200000
    let mdb_rdonly = Unsigned.UInt.of_int 0x20000
  end
end

module Error = struct
  open Concepts.Condition

  let closed_transaction = condition "closed-transaction" "The transaction has already ended" empty

  let lmdb_error code =
    condition "lmdb-error" (C.mdb_strerror code) ("code" |=| Concepts.Value.Integer code)

  let uncreatable_directory path message =
    condition "uncreatable-directory" "The storage directory could not be created"
      ("path" |=| Concepts.Value.String path & "message" |=| Concepts.Value.String message)
end

type connection = {env: C.mdb_env_ptr; dbi: C.mdb_dbi}
type transaction = {tx: C.mdb_txn_ptr; dbi: C.mdb_dbi; mutable active: bool}
type address = Label of string | Hash of Concepts.Hash.hash

let parse (c : Concepts.Configuration.term) =
  let open Concepts.Configuration in
  let open Utilities.Result in
  let* config = as_dictionary c "lmdb" in
  let* path = value_for "path" config |>> as_string in
  let* mode = value_for "mode" config |>> as_int in
  Ok (path, mode)

(* directories are traversable wherever they are readable *)
let directory_mode mode = mode lor ((mode land 0o444) lsr 2)

let rec ensure_directory path mode =
  let open Utilities.Result in
  if Sys.file_exists path then Ok ()
  else
    let* () = ensure_directory (Filename.dirname path) mode in
    match Sys.mkdir path mode with
    | () -> Ok ()
    | exception Sys_error _ when Sys.file_exists path -> Ok ()
    | exception Sys_error message -> Error (Error.uncreatable_directory path message)

let connect (c : Concepts.Configuration.term) =
  let open Utilities.Result in
  let* path, mode = parse c in
  let* () = ensure_directory path (directory_mode mode) in
  begin
    let* env = C.mdb_env_create' () in
    let* () = C.mdb_env_set_mapsize env (Unsigned.Size_t.of_int (1 lsl 30)) in
    (* NOTLS ties readers to transactions rather than threads, so one
       thread can hold several read transactions (nested cursors). *)
    match C.mdb_env_open env path C.Flags.mdb_notls (PosixTypes.Mode.of_int mode) with
    | Error x -> C.mdb_env_close env; Error x
    | Ok () ->
        let* tx = C.mdb_txn_begin' env C.null_txn Unsigned.UInt.zero in
        let* dbi = C.mdb_dbi_open' tx Unsigned.UInt.zero in
        let* () = C.mdb_txn_commit tx in
        Ok {env; dbi}
  end
  |> Result.map_error Error.lmdb_error
  |> Result.map_error
       Concepts.Condition.(
         complement ("path" |=| Concepts.Value.String path & "mode" |=| Concepts.Value.Integer mode) )

let disconnect ({env; _} : connection) = C.mdb_env_close env

let begin_with flags ({env; dbi} : connection) =
  C.mdb_txn_begin' env C.null_txn flags
  |> Result.map (fun tx -> {tx; dbi; active= true})
  |> Result.map_error Error.lmdb_error

let start = begin_with Unsigned.UInt.zero
let start_read = begin_with C.Flags.mdb_rdonly

let commit transaction =
  if not transaction.active then Error Error.closed_transaction
  else begin
    transaction.active <- false;
    C.mdb_txn_commit transaction.tx |> Result.map_error Error.lmdb_error
  end

let abort transaction =
  if transaction.active then begin
    transaction.active <- false;
    C.mdb_txn_abort transaction.tx
  end;
  Ok ()

(*
 * FIXME: `blob_of_bytes` and `bytes_of_blob` should not exist.
 * Rather, the FFI should know how to serialize a blob directly. This
 * makes it so that we do not depend on the OCaml `bytes` type and
 * opens the path for avoiding a copy on the FFI boundary later on
 *)

let bytes_of_address = function
  | Label s -> String.to_bytes s
  | Hash h -> Concepts.Hash.bytes_of_hash h

let get ({tx; dbi; active} : transaction) (addr : address) =
  if not active then Error Error.closed_transaction
  else
    begin match C.mdb_get' tx dbi (bytes_of_address addr) with
    | Ok x -> Ok (Some (Concepts.Blob.blob_of_bytes x))
    | Error e when e = C.Errors.mdb_notfound -> Ok None
    | Error e -> Error e
    end
    |> Result.map_error Error.lmdb_error

let put ({tx; dbi; active} : transaction) (addr : address) (b : Concepts.Blob.t) =
  if not active then Error Error.closed_transaction
  else
    C.mdb_put' tx dbi (bytes_of_address addr) (Concepts.Blob.bytes_of_blob b) Unsigned.UInt.zero
    |> Result.map_error Error.lmdb_error
