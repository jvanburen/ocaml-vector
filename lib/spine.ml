type elt = Multi_array.elt

let width = Multi_array.width

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

let rec get : 'a. 'a array t -> int -> dims:'a array dims -> elt =
  fun (type a) (t : a array t) (i : int) ~(dims : a array dims) : elt ->
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

let rec set : 'a. 'a array t -> int -> elt -> dims:'a array dims -> 'a array t =
  fun (type a) (t : a array t) (i : int) (elt : elt) ~(dims : a array dims) : a array t ->
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

let rec cons : 'a. 'a -> 'a array t -> dims:'a array dims -> 'a array t =
  fun (type a) (elt : a) (t : a array t) ~(dims : a array dims) : a array t ->
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

let rec snoc : 'a. 'a array t -> 'a -> dims:'a array dims -> 'a array t =
  fun (type a) (t : a array t) (elt : a) ~(dims : a array dims) : a array t ->
   match t with
   | Base { len; data } ->
     if Array.length data < width
     then Base { len = len + dim1 dims; data = data @> elt }
     else
       (* TODO: should this really be in suffix? why not data? *)
       Spine
         { prefix = data
         ; prefix_len = len
         ; data = empty
         ; data_len = 0
         ; suffix = [| elt |]
         ; suffix_len = dim1 dims
         }
   | Spine s ->
     if Array.length s.suffix < width
     then Spine { s with suffix_len = s.suffix_len + dim1 dims; suffix = s.suffix @> elt }
     else
       Spine
         { prefix_len = s.prefix_len
         ; prefix = s.prefix
         ; data_len = s.suffix_len + s.data_len
         ; data = snoc s.data s.suffix ~dims:(next dims)
         ; suffix_len = dim1 dims
         ; suffix = [| elt |]
         }
;;

let rec fold_left :
          'a 'acc.
          'a array t -> init:'acc -> f:('acc -> elt -> 'acc) -> dims:'a array dims -> 'acc
  =
  fun (type a acc)
      (t : a array t)
      ~(init : acc)
      ~(f : acc -> elt -> acc)
      ~(dims : a array dims)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_left b.data ~init ~f ~dims
   | Spine s ->
     let init = Multi_array.fold_left s.prefix ~init ~f ~dims in
     let init = fold_left s.data ~init ~f ~dims:(next dims) in
     Multi_array.fold_left s.suffix ~init ~f ~dims
;;

let rec fold_right :
          'a 'acc.
          'a array t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dims:'a array dims -> 'acc
  =
  fun (type a acc)
      (t : a array t)
      ~(init : acc)
      ~(f : elt -> acc -> acc)
      ~(dims : a array dims)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_right b.data ~init ~f ~dims
   | Spine s ->
     let init = Multi_array.fold_right s.suffix ~init ~f ~dims in
     let init = fold_right s.data ~init ~f ~dims:(next dims) in
     Multi_array.fold_right s.prefix ~init ~f ~dims
;;

module To_array = struct
  let[@inline] blit_helper ~src_len ~src_pos ~(dst : elt array) ~dst_pos ~len ~blit ~next =
    let written_from_src =
      match src_len -$ src_pos with
      | None -> 0
      | Some src_len ->
        let len = min len src_len in
        blit ~src_pos ~dst ~dst_pos ~len;
        len
    in
    let src_pos = max 0 (src_pos - src_len) in
    let dst_pos = dst_pos + written_from_src in
    let len = len - written_from_src in
    if len > 0 then next ~src_pos ~dst ~dst_pos ~len
  ;;

  let rec unchecked_blit :
            'a.
            src:'a array t
            -> src_pos:int
            -> dst:elt array
            -> dst_pos:int
            -> len:int
            -> dims:'a array dims
            -> unit
    =
    fun (type a)
        ~(src : a array t)
        ~src_pos
        ~(dst : elt array)
        ~dst_pos
        ~len
        ~(dims : a array dims)
      : unit ->
     match src with
     | Base b ->
       Multi_array.To_array.unchecked_blit ~src:b.data ~src_pos ~dst ~dst_pos ~len ~dims
     | Spine s ->
       blit_helper
         ~src_len:s.prefix_len
         ~src_pos
         ~dst
         ~dst_pos
         ~len
         ~blit:(Multi_array.To_array.unchecked_blit ~src:s.prefix ~dims)
         ~next:
           (blit_helper
              ~src_len:s.data_len
              ~blit:(unchecked_blit ~src:s.data ~dims:(next dims))
              ~next:
                (blit_helper
                   ~src_len:s.suffix_len
                   ~blit:(Multi_array.To_array.unchecked_blit ~src:s.suffix ~dims)
                   ~next:(fun ~src_pos:_ ~dst:_ ~dst_pos:_ ~len:_ -> ())))
  ;;
end

open! Base

let rec actual_len : 'arr. 'arr array t -> dims:'arr array dims -> int =
  fun (type arr) (t : arr array t) ~(dims : arr array dims) : int ->
   match t with
   | Base { len; data } ->
     [%test_result: int] len ~expect:(Multi_array.actual_len data ~dims);
     len
   | Spine { prefix_len; data_len; suffix_len; prefix; suffix; data } ->
     [%test_result: int] prefix_len ~expect:(Multi_array.actual_len prefix ~dims);
     [%test_result: int] data_len ~expect:(actual_len data ~dims:(next dims));
     [%test_result: int] suffix_len ~expect:(Multi_array.actual_len suffix ~dims);
     let len = prefix_len + data_len + suffix_len in
     assert (len > 0);
     len
;;

let invariant t ~dims =
  let expect = actual_len t ~dims in
  [%test_result: int] (length t) ~expect
;;
