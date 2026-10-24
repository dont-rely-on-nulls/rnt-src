module Ordering = struct
  type t = Equal | Smaller | Greater

  let of_int x = if x < 0 then Smaller else if x > 0 then Greater else Equal
end

module Option = struct
  let ( let* ) = Option.bind
  let ( |>> ) = Option.bind
  let sequence = function None -> Ok None | Some x -> Result.map Option.some x
end

module Result = struct
  let ( let* ) = Result.bind
  let ( |>> ) = Result.bind
end

module type SEQUENCE = sig
  type 'a t

  val empty : 'a t
  val cons : 'a -> 'a t -> 'a t
  val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
end

module Generic (S : SEQUENCE) = struct
  let sequence ms =
    let open Result in
    S.fold_right
      (fun m acc ->
        let* acc = acc in
        let* m = m in
        Ok (S.cons m acc) )
      ms (Ok S.empty)

  let foldm_left f init ms =
    let open Result in
    S.fold_left
      (fun acc m ->
        let* acc = acc in
        f acc m )
      (Ok init) ms
end

module List = struct
  module ListSequence : SEQUENCE with type 'a t = 'a list = struct
    type 'a t = 'a list

    let empty = []
    let cons x xs = x :: xs
    let fold_right = List.fold_right
    let fold_left = List.fold_left
  end

  include Generic (ListSequence)

  let concat_map f xs = List.map f xs |> sequence |> Stdlib.Result.map List.concat
  let hd_opt = function x :: _ -> Some x | [] -> None
end

module FingerTree = struct
  module FingerTreeSequence : SEQUENCE with type 'a t = 'a BatFingerTree.t = struct
    type 'a t = 'a BatFingerTree.t

    let empty = BatFingerTree.empty
    let cons x xs = BatFingerTree.cons xs x
    let fold_right f xs acc = BatFingerTree.fold_right (Fun.flip f) acc xs
    let fold_left = BatFingerTree.fold_left
  end

  include Generic (FingerTreeSequence)

  let map2 f xs ys =
    let rec frob xs ys acc =
      match BatFingerTree.front xs with
      | None -> acc
      | Some (xs', x) -> (
        match BatFingerTree.front ys with
        | None -> acc
        | Some (ys', y) -> f x y |> BatFingerTree.snoc acc |> frob xs' ys' )
    in
    frob xs ys BatFingerTree.empty

  let zip xs ys = map2 (fun x y -> x, y) xs ys

  let join ss sep =
    BatFingerTree.print ~first:"" ~last:"" ~sep BatIO.nwrite |> Fun.flip BatIO.to_string ss
end

module Atomic = struct
  let rec swap atom f =
    let v = Atomic.get atom in
    let v' = f v in
    if Atomic.compare_and_set atom v v' then atom else swap atom f

  let rec mswap atom f =
    let open Result in
    let v = Atomic.get atom in
    let* v' = f v in
    if Atomic.compare_and_set atom v v' then Ok atom else mswap atom f
end

module Fun = struct
  let ( |.| ) = Fun.compose
end
