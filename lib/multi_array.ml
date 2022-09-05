type elt

(* TODO: These could all be specialized for single-dimensional arrays *)

module Dim = struct
  type _ t =
    | Z : elt t
    | S : int * 'a t -> 'a array t

  let max_width = 3
  let one = S (1, Z)
  let cols (type a) (S (c, _) : a array t) : int = c
  let next (type a) (S (i, _) as t : a array t) = S (max_width * i, t)
end

type 'a dim = 'a Dim.t
type 'a t = 'a * 'a dim

let cols = Dim.cols

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
   | Z -> init
   | S (_, Z) -> ArrayLabels.fold_left t ~init ~f
   | S (_, dim) ->
     let init = ref init in
     for i = 0 to Array.length t - 1 do
       init := fold_left (Array.unsafe_get t i) ~init:!init ~f ~dim
     done;
     !init
;;

let rec fold_right :
          't 'acc. 't -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'t dim -> 'acc
  =
  fun (type t acc) (t : t) ~(init : acc) ~(f : elt -> acc -> acc) ~(dim : t dim) : acc ->
   match dim with
   | Z -> init
   | S (_, Z) -> ArrayLabels.fold_right t ~init ~f
   | S (_, dim) ->
     let init = ref init in
     for i = Array.length t - 1 downto 0 do
       init := fold_right (Array.unsafe_get t i) ~init:!init ~f ~dim
     done;
     !init
;;

let rec map : 't. 't -> f:(elt -> elt) -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(f : elt -> elt) ~(dim : t dim) : t ->
   match dim with
   | Z -> f t
   | S (_, dim) -> ArrayLabels.map t ~f:(fun t -> map t ~f ~dim)
;;

let rec rev : 't. 't -> dim:'t dim -> 't =
  fun (type t) (t : t) ~(dim : t dim) : t ->
   match dim with
   | Z -> t
   | S (_, dim) ->
     (match Array.length t with
      | 0 -> [||]
      | len ->
        let reversed = Array.make len (rev t.(0) ~dim) in
        for i = 1 to len - 1 do
          Array.unsafe_set reversed (len - i - 1) (rev (Array.unsafe_get t i) ~dim)
        done;
        reversed)
;;

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
       | S (_, Z) -> ArrayLabels.blit ~src ~src_pos ~dst ~dst_pos ~len
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
           incr i;
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
  let open Base in
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
