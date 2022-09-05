type elt

let width = 3

module Dims = struct
  type _ t =
    | [] : elt t
    | ( :: ) : int * 'a t -> 'a array t

  let one = [ 1 ]
  let dim1 (type a) (i :: _ : a array t) : int = i
  let next (type a) (dim1 :: _ as t : a array t) = (width * dim1) :: t
end

type 'a dims = 'a Dims.t
type 'a t = 'a * 'a dims

let dim1 = Dims.dim1

let rec get : 't. 't -> int -> dims:'t dims -> elt =
  fun (type t) (t : t) (i : int) ~(dims : t dims) : elt ->
   match dims with
   | [] -> if i = 0 then t else invalid_arg "index out of bounds"
   | width :: dims -> get t.(i / width) (i mod width) ~dims
;;

let rec set : 't. 't -> int -> 'elt -> dims:'t dims -> 't =
  fun (type t) (t : t) (i : int) (elt : elt) ~(dims : t dims) : t ->
   match dims with
   | [] -> if i = 0 then elt else invalid_arg "index out of bounds"
   | width :: dims ->
     let c = Array.copy t in
     c.(i / width) <- set t.(i / width) (i mod width) elt ~dims;
     c
;;

let rec fold_left :
          't 'acc. 't -> init:'acc -> f:('acc -> elt -> 'acc) -> dims:'t dims -> 'acc
  =
  fun (type t acc) (t : t) ~(init : acc) ~(f : acc -> elt -> acc) ~(dims : t dims) : acc ->
   match dims with
   | [] -> init
   | [ _ ] -> ArrayLabels.fold_left t ~init ~f
   | _ :: dims ->
     let init = ref init in
     for i = 0 to Array.length t - 1 do
       init := fold_left (Array.unsafe_get t i) ~init:!init ~f ~dims
     done;
     !init
;;

let rec fold_right :
          't 'acc. 't -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dims:'t dims -> 'acc
  =
  fun (type t acc) (t : t) ~(init : acc) ~(f : elt -> acc -> acc) ~(dims : t dims) : acc ->
   match dims with
   | [] -> init
   | [ _ ] -> ArrayLabels.fold_right t ~init ~f
   | _ :: dims ->
     let init = ref init in
     for i = Array.length t - 1 downto 0 do
       init := fold_right (Array.unsafe_get t i) ~init:!init ~f ~dims
     done;
     !init
;;

module O = struct
  type 'a dims = 'a Dims.t

  let dim1 = Dims.dim1
  let next = Dims.next
  let[@inline] ( .+() ) a (i, dims) = get a i ~dims
  let[@inline] ( .+()<- ) a (i, dims) x = set a i x ~dims
end

module To_array = struct
  let rec unchecked_blit :
            't.
            src:'t array
            -> src_pos:int
            -> dst:elt array
            -> dst_pos:int
            -> len:int
            -> dims:'t array dims
            -> unit
    =
    fun (type t)
        ~(src : t array)
        ~src_pos
        ~(dst : elt array)
        ~dst_pos
        ~len
        ~(dims : t array dims)
      : unit ->
     if len = 0
     then ()
     else (
       match dims with
       | [ _ ] -> ArrayLabels.blit ~src ~src_pos ~dst ~dst_pos ~len
       | width :: (_ :: _ as dims) ->
         let dst_pos = ref dst_pos in
         let len = ref len in
         let i = ref (src_pos / width) in
         let src_pos = ref (src_pos mod width) in
         while !len > 0 do
           let sub_len = min (width - !src_pos) !len in
           unchecked_blit
             ~src:src.(!i)
             ~src_pos:!src_pos
             ~dst
             ~dst_pos:!dst_pos
             ~len:sub_len
             ~dims;
           incr i;
           len := !len - sub_len;
           src_pos := 0;
           dst_pos := !dst_pos + sub_len
         done)
  ;;
end

let rec actual_len : 't. 't -> dims:'t dims -> int =
  let open Base in
  fun (type t) (t : t) ~(dims : t dims) : int ->
    match dims with
    | [] -> 1
    | width :: dims ->
      Array.sum
        (module Int)
        t
        ~f:(fun a ->
          let len = actual_len a ~dims in
          [%test_result: int] len ~expect:width;
          len)
;;
