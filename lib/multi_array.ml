type elt =
  | Immediate
  | Not_a_float of int * int

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
