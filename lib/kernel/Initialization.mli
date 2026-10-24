(** a subsystem's root, \[name], holding \[name]\evaluator for the
    evaluators it registers. Mounting it again keeps the one there. *)
val mount : Protocols.Handle.t -> string -> (unit, Concepts.Condition.condition) result

module Make (S : Abstract.Storage.STORAGE) : sig
  (** the root of the object tree, holding \system: its branches, of
      which there is always a master, the system's [evaluators] by
      language, the sessions and the applications. *)
  val initialize :
    ?evaluators:(string * Protocols.Handle.t) list ->
    S.connection ->
    (Protocols.Handle.t, Concepts.Condition.condition) result
end
