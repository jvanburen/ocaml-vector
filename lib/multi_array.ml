open! Core

type elt = private
  | Immediate
  | Not_a_float of int

(* TODO: These could all be specialized for single-dimensional arrays *)

module Dim = struct
  type _ t =
    | Z : elt t
    | S : int * 'a t -> 'a array t

  let max_width = 32
  let one = S (1, Z)
  let cols (type a) (S (c, _) : a array t) : int = c
  let next (type a) (S (i, _) as t : a array t) = S (max_width * i, t)
end

module Height = struct
  type _ t =
    | Z : elt t
    | S : 'a t -> 'a array t

  let one = S Z
end

type 'a dim = 'a Dim.t
type 'a t = 'a * 'a dim

let cols = Dim.cols

external ( mod ) : int -> int -> int = "%modint"

let rec get : 't. 't -> int -> dim:'t dim -> elt =
  fun (type t) (t : t) (i : int) ~(dim : t dim) : elt ->
   match dim with
   | Z -> if i = 0 then t else invalid_arg "index out of bounds"
   | S (cols, dim) -> get t.(i / cols) (i mod cols) ~dim
;;

let rec set : 't. 't -> int -> 'elt -> dim:'t dim -> 't =
  fun (type t) (t : t) (i : int) (elt : elt) ~(dim : t dim) : t ->
   match dim with
   | Z -> if i = 0 then elt else invalid_arg "index out of bounds"
   | S (cols, dim) ->
     let c = Array.copy t in
     c.(i / cols) <- set t.(i / cols) (i mod cols) elt ~dim;
     c
;;

let rec fold_left :
          't 'acc. 't -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'t dim -> 'acc
  =
  fun (type t acc) (t : t) ~(init : acc) ~(f : acc -> elt -> acc) ~(dim : t dim) : acc ->
   match dim with
   | Z -> f init t
   | S (_, Z) -> ArrayLabels.fold_left t ~init ~f
   | S (_, dim) ->
     let init = ref init in
     for i = 0 to Array.length t - 1 do
       init := fold_left (Array.unsafe_get t i) ~init:!init ~f ~dim
     done;
     !init
;;

let rec fold_right :
          't 'acc. 't -> f:(elt -> 'acc -> 'acc) -> init:'acc -> dim:'t dim -> 'acc
  =
  fun (type t acc) (t : t) ~(f : elt -> acc -> acc) ~(init : acc) ~(dim : t dim) : acc ->
   match dim with
   | Z -> f t init
   | S (_, Z) -> Array.fold_right t ~f ~init
   | S (_, dim) ->
     let init = ref init in
     for i = Array.length t - 1 downto 0 do
       init := fold_right (Array.unsafe_get t i) ~f ~init:!init ~dim
     done;
     !init
;;

let rec map : 't. 't -> f:(elt -> elt) -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(f : elt -> elt) ~(dim : t dim) : t ->
   match dim with
   | Z -> f t
   | S (_, dim) -> Array.map t ~f:(fun t -> map t ~f ~dim)
;;

let rec rev : 't. 't -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(dim : t dim) : t ->
   match dim with
   | Z -> t
   | S (_, dim) ->
     (match Array.length t with
      | 0 -> [||]
      | len ->
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
   match dim with
   | Z -> equal_elt x y
   | S (_, dim) ->
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
     match dim with
     | Z -> compare_elt x y
     | S (_, dim) ->
       let len = Array.length x in
       let cmp = Int.compare len (Array.length y) in
       if cmp <> 0 then cmp else compare_arr compare_elt x y ~dim ~pos:0 ~len)

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
  let rec compare : 't. (elt -> elt -> int) -> 't -> 't -> dim:'t dim -> int =
    fun (type t) (compare_elt : elt -> elt -> int) (x : t) (y : t) ~(dim : t dim) : int ->
     if phys_equal x y
     then 0
     else (
       match dim with
       | Z -> compare_elt x y
       | S (_, dim) ->
         let len = min (Array.length x) (Array.length y) in
         compare_arr compare_elt x y ~dim ~pos:0 ~len)

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
    then Int.compare (Array.length x) (Array.length y)
    else (
      let cmp = compare compare_elt x.(pos) y.(pos) ~dim in
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
       match dim with
       | S (_, Z) -> Array.blit ~src ~src_pos ~dst ~dst_pos ~len
       | S (cols, (S _ as dim)) ->
         let dst_pos = ref dst_pos in
         let len = ref len in
         let i = ref (src_pos / cols) in
         let src_pos = ref (src_pos mod cols) in
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
  match dim with
  | Z -> 1
  | S (cols, _) -> Array.length t * cols
;;

let rec actual_len : 't. 't -> dim:'t dim -> int =
  fun (type t) (t : t) ~(dim : t dim) : int ->
   match dim with
   | Z -> 1
   | S (cols, dim) ->
     Array.sum
       (module Int)
       t
       ~f:(fun a ->
         let len = actual_len a ~dim in
         [%test_result: int] len ~expect:cols;
         len)
;;

type 'a height = 'a Height.t

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
          't.
          't array -> dim:'t array height -> up:'t array array finger -> elt array finger
  =
  fun (type t) (t : t array) ~(dim : t array height) ~(up : t array array finger)
    : elt array finger ->
   match Array.length t with
   | 0 -> next_finger up ~dim:(S dim)
   | len ->
     (match dim with
      | S Z -> Finger { pos = 0; len; arr = t; up }
      | S (S _ as down) ->
        to_finger t.(0) ~dim:down ~up:(Finger { pos = 0; len; arr = t; up }))

and next_finger : 't. 't array finger -> dim:'t array height -> elt array finger =
  fun (type t) (f : t array finger) ~(dim : t array height) : elt array finger ->
   match f with
   | Top -> Top
   | Finger ({ pos; len; arr; up } as f) ->
     if pos + 1 = len
     then next_finger up ~dim:(S dim)
     else (
       match dim with
       | S Z -> Top
       | S (S _ as down) ->
         let pos = pos + 1 in
         let next = Finger { f with pos } in
         to_finger arr.(pos) ~dim:down ~up:next)
;;

let to_sequence (type t) (t : t array) ~(dim : t array height) : elt Sequence.t =
  Sequence.unfold_step
    ~init:(to_finger t ~dim ~up:Top)
    ~f:(fun (finger : elt array finger) ->
    match finger with
    | Top -> Done
    | Finger { pos; arr; _ } as f -> Yield (arr.(pos), next_finger f ~dim:(S Z)))
;;
