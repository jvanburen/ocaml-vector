open Base

(* TODO:
- append
- concat
- list view
- bin_prot
- sort
- dedup and sort
- shortlex compare
- lexicographic compare
- equal
- to_sequence
- [Indexed_container.S1]
*)

type +'a t [@@deriving equal, compare, sexp]

val empty : _ t
val length : _ t -> int
val is_empty : _ t -> bool
val init : int -> f:(int -> 'a) -> 'a t
val get : 'a t -> int -> 'a
val set : 'a t -> int -> 'a -> 'a t
val cons : 'a -> 'a t -> 'a t
val snoc : 'a t -> 'a -> 'a t
val map : 'a t -> f:('a -> 'b) -> 'b t
val rev : 'a t -> 'a t
val fold : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
val iter : 'a t -> f:('a -> unit) -> unit
val fold_right : 'a t -> init:'acc -> f:('a -> 'acc -> 'acc) -> 'acc
val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list
val of_array : 'a array -> 'a t
val to_array : 'a t -> 'a array
val to_sequence : 'a t -> 'a Sequence.t
val of_sequence : 'a Sequence.t -> 'a t

module To_array : Blit.S1_distinct with type 'a src := 'a t and type 'a dst := 'a array
