open! Base

type elt = private
  | Immediate
  | Not_a_float of int

type 'a node =
  { size : int
  ; prefix_sizes : int array
  ; storage : 'a array (* TODO: uniform array *)
  }
[@@deriving sexp_of]

module Dim = struct
  type _ t =
    | One : int -> elt node t
    | S : int * 'a node t -> 'a node node t

  let max_width = 3
  let one = One 1

  let cols (type a) (t : a t) : int =
    match t with
    | One i -> i
    | S (i, _) -> i
  ;;

  let next (type a) (t : a t) : a node t =
    match t with
    | One i -> S (max_width * i, t)
    | S (i, _) -> S (max_width * i, t)
  ;;
end

type 'a dim = 'a Dim.t

let cols = Dim.cols
let next = Dim.next
let empty = { size = 0; prefix_sizes = [||]; storage = [||] }

let rec get : 't. 't node -> int -> dim:'t node dim -> elt =
  fun (type t) (t : t node) (i : int) ~(dim : t node dim) : elt ->
   match dim with
   | One _ -> t.storage.(i)
   | S (cols, dim) ->
     let j = ref (i / cols) in
     while t.prefix_sizes.(!j) < i do
       Int.incr j
     done;
     let next = t.storage.(!j) in
     get next (i - t.prefix_sizes.(!j)) ~dim
;;

let rec set : 't. 't node -> int -> dim:'t node dim -> elt -> 't node =
  fun (type t) (t : t node) (i : int) ~(dim : t node dim) (elt : elt) : t node ->
   match dim with
   | One _ ->
     let storage = Array.copy t.storage in
     storage.(i) <- elt;
     { t with storage }
   | S (cols, dim) ->
     let j = ref (i / cols) in
     while t.prefix_sizes.(!j) < i do
       Int.incr j
     done;
     let next = t.storage.(!j) in
     let storage = Array.copy t.storage in
     storage.(!j) <- set next (i - t.prefix_sizes.(!j)) ~dim elt;
     { t with storage }
;;

let rec fold_left :
          't 'acc.
          't node -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'t node dim -> 'acc
  =
  fun (type t acc) (t : t node) ~(init : acc) ~(f : acc -> elt -> acc) ~(dim : t node dim)
    : acc ->
   match dim with
   | One _ -> Array.fold t.storage ~init ~f
   | S (_, dim) ->
     Array.fold t.storage ~init ~f:(fun init t' -> fold_left t' ~init ~f ~dim)
;;

let rec fold_right :
          't 'acc.
          't node -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'t node dim -> 'acc
  =
  fun (type t acc) (t : t node) ~(init : acc) ~(f : elt -> acc -> acc) ~(dim : t node dim)
    : acc ->
   match dim with
   | One _ -> Array.fold_right t.storage ~init ~f
   | S (_, dim) ->
     Array.fold_right t.storage ~init ~f:(fun t' init -> fold_right t' ~init ~f ~dim)
;;

(* TODO: return the same thing if the elements are phys_equal *)

let rec map : 't. 't node -> f:('a -> 'b) -> dim:'t node dim -> 't node =
  fun (type t) (t : t node) ~(f : elt -> elt) ~(dim : t node dim) : t node ->
   match dim with
   | One _ -> { t with storage = Array.map t.storage ~f }
   | S (_, dim) -> { t with storage = Array.map t.storage ~f:(fun t -> map t ~f ~dim) }
;;

let rec actual_len : 't. 't node -> dim:'t node dim -> int =
  let open Base in
  fun (type t) (t : t node) ~(dim : t node dim) : int ->
    let len =
      match dim with
      | One _ -> Array.length t.storage
      | S (cols, dim) ->
        Array.fold2_exn t.storage t.prefix_sizes ~init:0 ~f:(fun acc t prefix_sum ->
          [%test_result: int] prefix_sum ~expect:acc;
          let len = actual_len t ~dim in
          assert (len < cols);
          acc + len)
    in
    [%test_result: int] len ~expect:t.size;
    len
;;

let cons (type t) (x : t) (t : t node) ~(dim : t node dim) : t node =
  let new_size =
    match dim with
    | One _ -> 1
    | S _ -> x.size
  in
  let prefix_sizes = Array.create 0 ~len:(Array.length t.prefix_sizes + 1) in
  Array.iteri t.prefix_sizes ~f:(fun i x -> prefix_sizes.(i + 1) <- x + new_size);
  let storage = Array.create x ~len:(Array.length t.storage + 1) in
  Array.blit
    ~src:t.storage
    ~src_pos:0
    ~dst:storage
    ~dst_pos:1
    ~len:(Array.length t.storage);
  { size = t.size + new_size; prefix_sizes; storage }
;;

let snoc (type t) (t : t node) (x : t) ~(dim : t node dim) : t node =
  let new_size =
    match dim with
    | One _ -> 1
    | S _ -> x.size
  in
  let prefix_sizes = Array.create t.size ~len:(Array.length t.prefix_sizes + 1) in
  Array.blit
    ~src:t.prefix_sizes
    ~src_pos:0
    ~dst:prefix_sizes
    ~dst_pos:0
    ~len:(Array.length t.prefix_sizes);
  let storage = Array.create x ~len:(Array.length t.storage + 1) in
  Array.blit
    ~src:t.storage
    ~src_pos:0
    ~dst:storage
    ~dst_pos:0
    ~len:(Array.length t.storage);
  { size = t.size + new_size; prefix_sizes; storage }
;;

let singleton x ~dim = cons x empty ~dim

type _ finger =
  | Top : _ finger
  | Finger :
      { pos : int
      ; len : int
      ; arr : 'a node
      ; up : 'a node node finger
      }
      -> 'a node finger

let rec to_finger :
          't. 't node -> dim:'t node dim -> up:'t node node finger -> elt node finger
  =
  fun (type t) (t : t node) ~(dim : t node dim) ~(up : t node node finger)
    : elt node finger ->
   match Array.length t.storage with
   | 0 -> next_finger up ~dim:(next dim)
   | len ->
     (match dim with
      | One _ -> Finger { pos = 0; len; arr = t; up }
      | S (_, down) ->
        to_finger t.storage.(0) ~dim:down ~up:(Finger { pos = 0; len; arr = t; up }))

and next_finger : 't. 't node finger -> dim:'t node dim -> elt node finger =
  fun (type t) (f : t node finger) ~(dim : t node dim) : elt node finger ->
   match f with
   | Top -> Top
   | Finger ({ pos; len; arr; up } as f) ->
     if pos + 1 = len
     then next_finger up ~dim:(next dim)
     else (
       match dim with
       | One _ -> Top
       | S (_, down) ->
         let pos = pos + 1 in
         let next = Finger { f with pos } in
         to_finger arr.storage.(pos) ~dim:down ~up:next)
;;

let to_sequence (type t) (t : t node) ~(dim : t node dim) : elt Sequence.t =
  Sequence.unfold_step
    ~init:(to_finger t ~dim ~up:Top)
    ~f:(fun (finger : elt node finger) ->
    match finger with
    | Top -> Done
    | Finger { pos; arr; _ } as f -> Yield (arr.storage.(pos), next_finger f ~dim:Dim.one))
;;
