open! Core

type elt = private
  | Immediate
  | Not_a_float of int

(* TODO: These could all be specialized for single-dimensional arrays *)

module Dim : sig
  type _ t [@@immediate]

  type _ kind =
    | One : elt array kind
    | Many : 'a array array kind

  val max_width : int
  val one : elt array t
  val row : 'a array t -> int -> int
  val col : 'a array t -> int -> int
  val cols : _ t -> int
  val next : 'a t -> 'a array t
  val kind : 'a t -> 'a kind
  val inner : 'a array t -> 'a t
end = struct
  type 'a t = int

  let[@inline] row t i = i / t
  let[@inline] col t i = Int.rem i t

  type _ kind =
    | One : elt array kind
    | Many : 'a array array kind

  let bits = 5
  let max_width = 1 lsl bits
  let one = 1
  let[@inline] cols t = t
  let[@inline] next t = max_width * t
  let[@inline] kind t = Obj.magic (t > 1)
  let[@inline] inner t = t / max_width
end

type 'a dim = 'a Dim.t
type 'a t = 'a * 'a dim

let col = Dim.col
let row = Dim.row
let cols = Dim.cols
let kind = Dim.kind
let inner = Dim.inner
let next = Dim.next

external ( mod ) : int -> int -> int = "%modint"

let rec get : 't. 't -> int -> dim:'t dim -> elt =
  fun (type t) (t : t) (i : int) ~(dim : t dim) : elt ->
   match kind dim with
   | One -> t.(i)
   | Many -> get t.(row dim i) (col dim i) ~dim:(inner dim)
;;

let rec set : 't. 't array -> int -> elt -> dim:'t array dim -> 't array =
  fun (type t) (t : t array) (i : int) (elt : elt) ~(dim : t array dim) : t array ->
   let row = row dim i in
   let elt : t =
     match kind dim with
     | One -> elt
     | Many -> set t.(row) (col dim i) elt ~dim:(inner dim)
   in
   let c = Array.copy t in
   c.(row) <- elt;
   c
;;

let rec fold_left :
          't 'acc. 't -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'t dim -> 'acc
  =
  fun (type t acc) (t : t) ~(init : acc) ~(f : acc -> elt -> acc) ~(dim : t dim) : acc ->
   match kind dim with
   | One -> Array.fold t ~init ~f
   | Many ->
     let dim = inner dim in
     Array.fold t ~init ~f:(fun init t -> fold_left t ~init ~f ~dim)
;;

let rec fold_right :
          't 'acc. 't -> f:(elt -> 'acc -> 'acc) -> init:'acc -> dim:'t dim -> 'acc
  =
  fun (type t acc) (t : t) ~(f : elt -> acc -> acc) ~(init : acc) ~(dim : t dim) : acc ->
   match kind dim with
   | One -> Array.fold_right t ~f ~init
   | Many ->
     let dim = inner dim in
     Array.fold_right t ~f:(fun t init -> fold_right t ~f ~init ~dim) ~init
;;

let rec map : 't. 't -> f:(elt -> elt) -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(f : elt -> elt) ~(dim : t dim) : t ->
   match kind dim with
   | One -> Array.map t ~f
   | Many -> Array.map t ~f:(fun t -> map t ~f ~dim:(inner dim))
;;

let rec rev : 't. 't -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(dim : t dim) : t ->
   match kind dim with
   | One -> Array.rev t
   | Many ->
     (match Array.length t with
      | 0 -> [||]
      | len ->
        let dim = inner dim in
        let reversed = Array.create (rev t.(0) ~dim) ~len in
        for i = 1 to len - 1 do
          Array.unsafe_set reversed (len - i - 1) (rev (Array.unsafe_get t i) ~dim)
        done;
        reversed)
;;

let rec equal : 't. (elt -> elt -> bool) -> 't -> 't -> dim:'t dim -> bool =
  fun (type t) (equal_elt : elt -> elt -> bool) (x : t) (y : t) ~(dim : t dim) : bool ->
   phys_equal x y
   ||
   match kind dim with
   | One -> Array.equal equal_elt x y
   | Many ->
     let dim = inner dim in
     let len = Array.length x in
     len = Array.length y && equal_arr equal_elt x y ~dim ~pos:0 ~len

and equal_arr :
      't.
      (elt -> elt -> bool)
      -> 't array
      -> 't array
      -> dim:'t dim
      -> pos:int
      -> len:int
      -> bool
  =
  fun (type t)
      (equal_elt : elt -> elt -> bool)
      (x : t array)
      (y : t array)
      ~(dim : t dim)
      ~pos
      ~len
    : bool ->
   pos = len
   || (equal equal_elt (Array.unsafe_get x pos) (Array.unsafe_get y pos) ~dim
      && equal_arr equal_elt x y ~dim ~pos:(pos + 1) ~len)
;;

let rec compare : 't. (elt -> elt -> int) -> 't -> 't -> dim:'t dim -> int =
  fun (type t) (compare_elt : elt -> elt -> int) (x : t) (y : t) ~(dim : t dim) : int ->
   if phys_equal x y
   then 0
   else (
     match kind dim with
     | One -> Array.compare compare_elt x y
     | Many ->
       let len = Array.length x in
       let cmp = Int.compare len (Array.length y) in
       if cmp <> 0 then cmp else compare_arr compare_elt x y ~dim:(inner dim) ~pos:0 ~len)

and compare_arr :
      't.
      (elt -> elt -> int)
      -> 't array
      -> 't array
      -> dim:'t dim
      -> pos:int
      -> len:int
      -> int
  =
 fun compare_elt x y ~dim ~pos ~len ->
  if pos = len
  then 0
  else (
    let cmp = compare compare_elt x.(pos) y.(pos) ~dim in
    if cmp <> 0 then cmp else compare_arr compare_elt x y ~dim ~pos:(pos + 1) ~len)
;;

module Lexicographic = struct
  let rec compare :
            't. (elt -> elt -> int) -> 't array -> 't array -> dim:'t array dim -> int
    =
    fun (type t)
        (compare_elt : elt -> elt -> int)
        (x : t array)
        (y : t array)
        ~(dim : t array dim)
      : int ->
     if phys_equal x y
     then 0
     else (
       let len = min (Array.length x) (Array.length y) in
       compare_arr compare_elt x y ~dim ~pos:0 ~len)

  and compare_arr :
        't.
        (elt -> elt -> int)
        -> 't array
        -> 't array
        -> dim:'t array dim
        -> pos:int
        -> len:int
        -> int
    =
    fun (type t)
        (compare_elt : elt -> elt -> int)
        (x : t array)
        (y : t array)
        ~(dim : t array dim)
        ~pos
        ~len ->
     if pos = len
     then Int.compare (Array.length x) (Array.length y)
     else (
       let cmp =
         match kind dim with
         | One -> compare_elt x.(pos) y.(pos)
         | Many -> compare compare_elt x.(pos) y.(pos) ~dim:(inner dim)
       in
       if cmp <> 0 then cmp else compare_arr compare_elt x y ~dim ~pos:(pos + 1) ~len)
  ;;
end

module To_array = struct
  let rec unchecked_blit :
            't.
            src:'t array
            -> src_pos:int
            -> dst:elt array
            -> dst_pos:int
            -> len:int
            -> dim:'t array dim
            -> unit
    =
    fun (type t)
        ~(src : t array)
        ~src_pos
        ~(dst : elt array)
        ~dst_pos
        ~len
        ~(dim : t array dim)
      : unit ->
     if len = 0
     then ()
     else (
       match kind dim with
       | One -> Array.blit ~src ~src_pos ~dst ~dst_pos ~len
       | Many ->
         let dst_pos = ref dst_pos in
         let len = ref len in
         let i = ref (row dim src_pos) in
         let src_pos = ref (col dim src_pos) in
         let cols = cols dim in
         let dim = inner dim in
         while !len > 0 do
           let sub_len = min (cols - !src_pos) !len in
           unchecked_blit
             ~src:src.(!i)
             ~src_pos:!src_pos
             ~dst
             ~dst_pos:!dst_pos
             ~len:sub_len
             ~dim;
           Int.incr i;
           len := !len - sub_len;
           src_pos := 0;
           dst_pos := !dst_pos + sub_len
         done)
  ;;
end

let length (type t) (t : t) ~(dim : t dim) =
  match kind dim with
  | One -> Array.length t * cols dim
  | Many -> Array.length t * cols dim
;;

let rec actual_len : 't. 't -> dim:'t dim -> int =
  fun (type t) (t : t) ~(dim : t dim) : int ->
   match kind dim with
   | One -> Array.length t
   | Many ->
     Array.sum
       (module Int)
       t
       ~f:(fun a ->
         let len = actual_len a ~dim:(inner dim) in
         [%test_result: int] len ~expect:(cols dim);
         len)
;;

type _ finger =
  | Top : _ finger
  | Finger :
      { pos : int
      ; len : int
      ; arr : 'a array
      ; up : 'a array array finger
      }
      -> 'a array finger

let rec to_finger :
          't. 't array -> dim:'t array dim -> up:'t array array finger -> elt array finger
  =
  fun (type t) (t : t array) ~(dim : t array dim) ~(up : t array array finger)
    : elt array finger ->
   match Array.length t with
   | 0 -> next_finger up ~dim:(next dim)
   | len ->
     (match kind dim with
      | One -> Finger { pos = 0; len; arr = t; up }
      | Many ->
        to_finger t.(0) ~dim:(inner dim) ~up:(Finger { pos = 0; len; arr = t; up }))

and next_finger : 't. 't array finger -> dim:'t array dim -> elt array finger =
  fun (type t) (f : t array finger) ~(dim : t array dim) : elt array finger ->
   match f with
   | Top -> Top
   | Finger ({ pos; len; arr; up } as f) ->
     if pos + 1 = len
     then next_finger up ~dim:(next dim)
     else (
       match kind dim with
       | One -> Top
       | Many ->
         let pos = pos + 1 in
         let next = Finger { f with pos } in
         to_finger arr.(pos) ~dim:(inner dim) ~up:next)
;;

let to_sequence (type t) (t : t array) ~(dim : t array dim) : elt Sequence.t =
  Sequence.unfold_step
    ~init:(to_finger t ~dim ~up:Top)
    ~f:(fun (finger : elt array finger) ->
    match finger with
    | Top -> Done
    | Finger { pos; arr; _ } as f -> Yield (arr.(pos), next_finger f ~dim:Dim.one))
;;
