type elt = int

let width = 3

module Multi_array = struct
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

  let rec get : 'arr. 'arr dims -> 'arr -> int -> elt =
    fun (type arr) (dims : arr dims) (arr : arr) (i : int) : elt ->
     match dims with
     | [] -> if i = 0 then arr else invalid_arg "index out of bounds"
     | width :: dims -> get dims arr.(i / width) (i mod width)
  ;;

  let rec set : 'arr. 'arr dims -> 'arr -> int -> 'elt -> 'arr =
    fun (type arr) (dims : arr dims) (arr : arr) (i : int) (elt : elt) : arr ->
     match dims with
     | [] -> if i = 0 then elt else invalid_arg "index out of bounds"
     | width :: dims ->
       let c = Array.copy arr in
       c.(i / width) <- set dims arr.(i / width) (i mod width) elt;
       c
  ;;

  let rec fold_left :
            'arr 'acc. 'arr dims -> ('acc -> elt -> 'acc) -> 'acc -> 'arr -> 'acc
    =
    fun (type arr acc) (dims : arr dims) (f : acc -> elt -> acc) (init : acc) (arr : arr)
      : acc ->
     match dims with
     | [] -> init
     | _ :: dims -> Array.fold_left (fold_left dims f) init arr
  ;;

  let rec fold_right :
            'arr 'acc. 'arr dims -> (elt -> 'acc -> 'acc) -> 'arr -> 'acc -> 'acc
    =
    fun (type arr acc) (dims : arr dims) (f : elt -> acc -> acc) (arr : arr) (init : acc)
      : acc ->
     match dims with
     | [] -> init
     | _ :: dims -> Array.fold_right (fold_right dims f) arr init
  ;;

  let[@inline] fold_left dims a ~init ~f = fold_left dims f init a
  let[@inline] fold_right dims a ~init ~f = fold_right dims f a init

  let rec actual_len : 'arr. 'arr dims -> 'arr -> int =
    let open Base in
    fun (type arr) (dims' : arr dims) (arr : arr) : int ->
      match dims' with
      | [] -> 1
      | inner_width :: dims ->
        Array.sum
          (module Int)
          arr
          ~f:(fun a ->
            let len = actual_len dims a in
            [%test_result: int] len ~expect:inner_width;
            len)
  ;;

  module O = struct
    type 'a dims = 'a Dims.t

    let dim1 = Dims.dim1
    let next = Dims.next
    let[@inline] ( .+() ) a (i, dims) = get dims a i
    let[@inline] ( .+()<- ) a (i, dims) x = set dims a i x
  end
end

open Multi_array.O

let ( @> ) src x =
  let len = Array.length src in
  let dst = Array.make (len + 1) x in
  ArrayLabels.blit ~src ~src_pos:0 ~dst ~dst_pos:0 ~len;
  dst
;;

let ( <@ ) x src =
  let len = Array.length src in
  let dst = Array.make (len + 1) x in
  ArrayLabels.blit ~src ~src_pos:0 ~dst ~dst_pos:1 ~len;
  dst
;;

let ( -$ ) x y = if x >= y then Some (x - y) else None

(* TODO: store pre/pre+data/total lengths instead of pre/data/suff *)
type _ t =
  | Base :
      { len : int
      ; data : 'data array
      }
      -> 'data array t
  | Spine :
      { prefix_len : int
      ; prefix : 'data
      ; data_len : int
      ; data : 'data array t
      ; suffix_len : int
      ; suffix : 'data
      }
      -> 'data t

include struct
  open Core

  let rec sexp_of_t : 'arr. ('arr -> Sexp.t) -> 'arr t -> Sexp.t =
    fun (type arr) (sexp_of_arr : arr -> Sexp.t) (t : arr t) : Sexp.t ->
     match t with
     | Base { len; data } -> [%sexp { len : int; data : arr }]
     | Spine { prefix_len; data_len; suffix_len; prefix; suffix; data } ->
       [%sexp
         { prefix : arr
         ; prefix_len : int
         ; width : int
         ; data : arr array t
         ; data_len : int
         ; suffix : arr
         ; suffix_len : int
         }]
  ;;
end

let empty = Base { len = 0; data = [||] }

let length (type a) (t : a t) =
  match t with
  | Base b -> b.len
  | Spine s -> s.prefix_len + s.data_len + s.suffix_len
;;

let rec get : 'arr. 'arr array t -> int -> dims:'arr array dims -> elt =
  fun (type arr) (t : arr array t) (i : int) ~(dims : arr array dims) : elt ->
   match t with
   | Base b -> b.data.+(i, dims)
   | Spine s ->
     (match i -$ s.prefix_len with
      | None -> s.prefix.+(i, dims)
      | Some i ->
        (match i -$ s.data_len with
         | None -> get s.data i ~dims:(next dims)
         | Some i -> s.suffix.+(i, dims)))
;;

let rec set : 'arr. 'arr array t -> int -> elt -> dims:'arr array dims -> 'arr array t =
  fun (type arr) (t : arr array t) (i : int) (elt : elt) ~(dims : arr array dims)
    : arr array t ->
   match t with
   | Base b -> Base { b with data = b.data.+(i, dims) <- elt }
   | Spine s ->
     (match i -$ s.prefix_len with
      | None -> Spine { s with prefix = s.prefix.+(i, dims) <- elt }
      | Some i ->
        (match i -$ s.data_len with
         | None -> Spine { s with data = set s.data i elt ~dims:(next dims) }
         | Some i -> Spine { s with suffix = s.suffix.+(i, dims) <- elt }))
;;

let rec cons : 'arr. 'arr -> 'arr array t -> dims:'arr array dims -> 'arr array t =
  fun (type arr) (elt : arr) (t : arr array t) ~(dims : arr array dims) : arr array t ->
   match t with
   | Base { len; data } ->
     if Array.length data < width
     then Base { len = len + dim1 dims; data = elt <@ data }
     else
       (* TODO: should this really be in suffix? why not data? *)
       Spine
         { prefix = [| elt |]
         ; prefix_len = dim1 dims
         ; data = empty
         ; data_len = 0
         ; suffix = data
         ; suffix_len = len
         }
   | Spine s ->
     if Array.length s.prefix < width
     then Spine { s with prefix_len = s.prefix_len + dim1 dims; prefix = elt <@ s.prefix }
     else
       Spine
         { prefix_len = dim1 dims
         ; prefix = [| elt |]
         ; data_len = s.prefix_len + s.data_len
         ; data = cons s.prefix s.data ~dims:(next dims)
         ; suffix_len = s.suffix_len
         ; suffix = s.suffix
         }
;;

let rec fold_left :
          'arr 'acc.
          'arr array dims -> 'arr array t -> init:'acc -> f:('acc -> elt -> 'acc) -> 'acc
  =
  fun (type arr acc)
      (dims : arr array dims)
      (t : arr array t)
      ~(init : acc)
      ~(f : acc -> elt -> acc)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_left dims b.data ~init ~f
   | Spine s ->
     let init = Multi_array.fold_left dims s.prefix ~init ~f in
     let init = fold_left (next dims) s.data ~init ~f in
     Multi_array.fold_left dims s.suffix ~init ~f
;;

let rec fold_right :
          'arr 'acc.
          'arr array t
          -> init:'acc
          -> f:(elt -> 'acc -> 'acc)
          -> dims:'arr array dims
          -> 'acc
  =
  fun (type arr acc)
      (t : arr array t)
      ~(init : acc)
      ~(f : elt -> acc -> acc)
      ~(dims : arr array dims)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_right dims b.data ~init ~f
   | Spine s ->
     let init = Multi_array.fold_right dims s.suffix ~init ~f in
     let init = fold_right s.data ~init ~f ~dims:(next dims) in
     Multi_array.fold_right dims s.prefix ~init ~f
;;

open! Base

let rec actual_len : 'arr. 'arr array t -> dims:'arr array dims -> int =
  fun (type arr) (t : arr array t) ~(dims : arr array dims) : int ->
   match t with
   | Base { len; data } ->
     [%test_result: int] len ~expect:(Multi_array.actual_len dims data);
     len
   | Spine { prefix_len; data_len; suffix_len; prefix; suffix; data } ->
     [%test_result: int] prefix_len ~expect:(Multi_array.actual_len dims prefix);
     [%test_result: int] data_len ~expect:(actual_len data ~dims:(next dims));
     [%test_result: int] suffix_len ~expect:(Multi_array.actual_len dims suffix);
     let len = prefix_len + data_len + suffix_len in
     assert (len > 0);
     len
;;

let invariant t ~dims =
  let expect = actual_len t ~dims in
  [%test_result: int] (length t) ~expect
;;
