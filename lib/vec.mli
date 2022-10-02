open! Core

type +'a t [@@deriving equal, compare, sexp]

module Lexicographic : sig
  type nonrec 'a t = 'a t [@@deriving compare]
end

include Invariant.S1 with type 'a t := 'a t
include Indexed_container.S1 with type 'a t := 'a t
include Quickcheckable.S1 with type 'a t := 'a t
include Monad.S with type 'a t := 'a t
module To_array : Blit.S1_distinct with type 'a src := 'a t and type 'a dst := 'a array

module View : sig
  type ('a, 'b) t =
    | []
    | ( :: ) of 'a * 'b
end

val empty : _ t
val singleton : 'a -> 'a t
val filter : 'a t -> f:('a -> bool) -> 'a t
val filter_map : 'a t -> f:('a -> 'b option) -> 'b t
val init : int -> f:(int -> 'a) -> 'a t
val get : 'a t -> int -> 'a
val set : 'a t -> int -> 'a -> 'a t
val cons : 'a -> 'a t -> 'a t
val snoc : 'a t -> 'a -> 'a t
val view : 'a t -> ('a, 'a t) View.t
val weiv : 'a t -> ('a t, 'a) View.t
val hd : 'a t -> 'a option
val hd_exn : 'a t -> 'a
val last : 'a t -> 'a option
val last_exn : 'a t -> 'a
val append : 'a t -> 'a t -> 'a t
val concat : 'a t t -> 'a t
val concat_map : 'a t -> f:('a -> 'b t) -> 'b t
val rev : 'a t -> 'a t
val fold_left : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
val fold_right : 'a t -> f:('a -> 'acc -> 'acc) -> init:'acc -> 'acc
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val of_array : 'a array -> 'a t
val to_array : 'a t -> 'a array
val to_sequence : 'a t -> 'a Sequence.t
val of_sequence : 'a Sequence.t -> 'a t
val sort : 'a t -> compare:('a -> 'a -> int) -> 'a t
val stable_sort : 'a t -> compare:('a -> 'a -> int) -> 'a t
val dedup_and_sort : 'a t -> compare:('a -> 'a -> int) -> 'a t
val sub : ('a t, 'a t) Blit.sub
val subo : ('a t, 'a t) Blit.subo
val split_n : 'a t -> int -> 'a t * 'a t
val take : 'a t -> int -> 'a t
val drop : 'a t -> int -> 'a t
