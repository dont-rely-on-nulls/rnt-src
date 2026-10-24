type t

class type implementation = object
  method list : (string BatFingerTree.t, Concepts.Condition.condition) result
  method find : string -> (Handle.t option, Concepts.Condition.condition) result
end

val make : #implementation -> Handle.protocol
val from : Handle.t -> t Handle.interface option
val list : t Handle.interface -> (string BatFingerTree.t, Concepts.Condition.condition) result
val find : t Handle.interface -> string -> (Handle.t option, Concepts.Condition.condition) result
val children : Handle.t -> ((string * Handle.t) BatFingerTree.t, Concepts.Condition.condition) result
