module Ordering : sig
  type t = Equal | Smaller | Greater

  val of_int : int -> t
end

module Result : sig
  val ( let* ) : ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
  val ( |>> ) : ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
end

module List : sig
  val sequence : ('a, 'b) result list -> ('a list, 'b) result
  val foldm_left : ('a -> 'b -> ('a, 'e) result) -> 'a -> 'b list -> ('a, 'e) result
  val concat_map : ('a -> ('b list, 'e) result) -> 'a list -> ('b list, 'e) result
  val hd_opt : 'a list -> 'a option
end

module Option : sig
  val ( let* ) : 'a option -> ('a -> 'b option) -> 'b option
  val ( |>> ) : 'a option -> ('a -> 'b option) -> 'b option
  val sequence : ('a, 'b) result option -> ('a option, 'b) result
end

module Atomic : sig
  val swap : 'a Atomic.t -> ('a -> 'a) -> 'a Atomic.t

  (* This is silly *)
  val mswap : 'a Atomic.t -> ('a -> ('a, 'b) result) -> ('a Atomic.t, 'b) result
end

module FingerTree : sig
  val map2 : ('a -> 'b -> 'c) -> 'a BatFingerTree.t -> 'b BatFingerTree.t -> 'c BatFingerTree.t
  val zip : 'a BatFingerTree.t -> 'b BatFingerTree.t -> ('a * 'b) BatFingerTree.t
  val sequence : ('a, 'b) result BatFingerTree.t -> ('a BatFingerTree.t, 'b) result
  val foldm_left : ('a -> 'b -> ('a, 'e) result) -> 'a -> 'b BatFingerTree.t -> ('a, 'e) result
  val join : string BatFingerTree.t -> string -> string
  val filter_map : ('a -> 'b option) -> 'a BatFingerTree.t -> 'b BatFingerTree.t
  val concat_map : ('a -> ('b BatFingerTree.t, 'e) result) -> 'a BatFingerTree.t -> ('b BatFingerTree.t, 'e) result
end

module Fun : sig
  val ( |.| ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end
