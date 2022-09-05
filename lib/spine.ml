type elt = Multi_array.elt
type 'a dim = 'a Multi_array.Dim.t
type 'a height = 'a Multi_array.Height.t

let max_width = Multi_array.Dim.max_width
let cols = Multi_array.Dim.cols
let next = Multi_array.Dim.next
let[@inline] ( .+() ) a (i, dim) = Multi_array.get a i ~dim
let[@inline] ( .+()<- ) a (i, dim) x = Multi_array.set a i x ~dim

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

let rec get : 'a. 'a array t -> int -> dim:'a array dim -> elt =
  fun (type a) (t : a array t) (i : int) ~(dim : a array dim) : elt ->
   match t with
   | Base b -> b.data.+(i, dim)
   | Spine s ->
     (match i -$ s.prefix_len with
      | None -> s.prefix.+(i, dim)
      | Some i ->
        (match i -$ s.data_len with
         | None -> get s.data i ~dim:(next dim)
         | Some i -> s.suffix.+(i, dim)))
;;

let rec set : 'a. 'a array t -> int -> elt -> dim:'a array dim -> 'a array t =
  fun (type a) (t : a array t) (i : int) (elt : elt) ~(dim : a array dim) : a array t ->
   match t with
   | Base b -> Base { b with data = b.data.+(i, dim) <- elt }
   | Spine s ->
     (match i -$ s.prefix_len with
      | None -> Spine { s with prefix = s.prefix.+(i, dim) <- elt }
      | Some i ->
        (match i -$ s.data_len with
         | None -> Spine { s with data = set s.data i elt ~dim:(next dim) }
         | Some i -> Spine { s with suffix = s.suffix.+(i, dim) <- elt }))
;;

let rec cons : 'a. 'a -> 'a array t -> dim:'a array dim -> 'a array t =
  fun (type a) (elt : a) (t : a array t) ~(dim : a array dim) : a array t ->
   match t with
   | Base { len; data } ->
     if Array.length data < max_width
     then Base { len = len + cols dim; data = elt <@ data }
     else
       (* TODO: should this really be in suffix? why not data? *)
       Spine
         { prefix = [| elt |]
         ; prefix_len = cols dim
         ; data = empty
         ; data_len = 0
         ; suffix = data
         ; suffix_len = len
         }
   | Spine s ->
     if Array.length s.prefix < max_width
     then Spine { s with prefix_len = s.prefix_len + cols dim; prefix = elt <@ s.prefix }
     else
       Spine
         { prefix_len = cols dim
         ; prefix = [| elt |]
         ; data_len = s.prefix_len + s.data_len
         ; data = cons s.prefix s.data ~dim:(next dim)
         ; suffix_len = s.suffix_len
         ; suffix = s.suffix
         }
;;

let rec snoc : 'a. 'a array t -> 'a -> dim:'a array dim -> 'a array t =
  fun (type a) (t : a array t) (elt : a) ~(dim : a array dim) : a array t ->
   match t with
   | Base { len; data } ->
     if Array.length data < max_width
     then Base { len = len + cols dim; data = data @> elt }
     else
       (* TODO: should this really be in suffix? why not data? *)
       Spine
         { prefix = data
         ; prefix_len = len
         ; data = empty
         ; data_len = 0
         ; suffix = [| elt |]
         ; suffix_len = cols dim
         }
   | Spine s ->
     if Array.length s.suffix < max_width
     then Spine { s with suffix_len = s.suffix_len + cols dim; suffix = s.suffix @> elt }
     else
       Spine
         { prefix_len = s.prefix_len
         ; prefix = s.prefix
         ; data_len = s.suffix_len + s.data_len
         ; data = snoc s.data s.suffix ~dim:(next dim)
         ; suffix_len = cols dim
         ; suffix = [| elt |]
         }
;;

let rec map : 'a. 'a array t -> f:(elt -> elt) -> dim:'a array dim -> 'a array t =
  fun (type a) (t : a array t) ~(f : elt -> elt) ~(dim : a array dim) : a array t ->
   match t with
   | Base b ->
     if b.len = 0 then t else Base { b with data = Multi_array.map b.data ~f ~dim }
   | Spine s ->
     let prefix = Multi_array.map s.prefix ~f ~dim in
     let data = map s.data ~f ~dim:(next dim) in
     let suffix = Multi_array.map s.suffix ~f ~dim in
     Spine { s with prefix; data; suffix }
;;

let rec rev : 'a. 'a array t -> dim:'a array dim -> 'a array t =
  fun (type a) (t : a array t) ~(dim : a array dim) : a array t ->
   match t with
   | Base b -> if b.len = 0 then t else Base { b with data = Multi_array.rev b.data ~dim }
   | Spine { prefix_len; prefix; data_len; data; suffix_len; suffix } ->
     Spine
       { prefix_len = suffix_len
       ; prefix = Multi_array.rev suffix ~dim
       ; data_len
       ; data = rev data ~dim:(next dim)
       ; suffix_len = prefix_len
       ; suffix = Multi_array.rev prefix ~dim
       }
;;

let rec fold_left :
          'a 'acc.
          'a array t -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'a array dim -> 'acc
  =
  fun (type a acc)
      (t : a array t)
      ~(init : acc)
      ~(f : acc -> elt -> acc)
      ~(dim : a array dim)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_left b.data ~init ~f ~dim
   | Spine s ->
     let init = Multi_array.fold_left s.prefix ~init ~f ~dim in
     let init = fold_left s.data ~init ~f ~dim:(next dim) in
     Multi_array.fold_left s.suffix ~init ~f ~dim
;;

let rec fold_right :
          'a 'acc.
          'a array t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'a array dim -> 'acc
  =
  fun (type a acc)
      (t : a array t)
      ~(init : acc)
      ~(f : elt -> acc -> acc)
      ~(dim : a array dim)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_right b.data ~init ~f ~dim
   | Spine s ->
     let init = Multi_array.fold_right s.suffix ~init ~f ~dim in
     let init = fold_right s.data ~init ~f ~dim:(next dim) in
     Multi_array.fold_right s.prefix ~init ~f ~dim
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
            -> dim:'a array dim
            -> unit
    =
    fun (type a)
        ~(src : a array t)
        ~src_pos
        ~(dst : elt array)
        ~dst_pos
        ~len
        ~(dim : a array dim)
      : unit ->
     match src with
     | Base b ->
       Multi_array.To_array.unchecked_blit ~src:b.data ~src_pos ~dst ~dst_pos ~len ~dim
     | Spine s ->
       blit_helper
         ~src_len:s.prefix_len
         ~src_pos
         ~dst
         ~dst_pos
         ~len
         ~blit:(Multi_array.To_array.unchecked_blit ~src:s.prefix ~dim)
         ~next:
           (blit_helper
              ~src_len:s.data_len
              ~blit:(unchecked_blit ~src:s.data ~dim:(next dim))
              ~next:
                (blit_helper
                   ~src_len:s.suffix_len
                   ~blit:(Multi_array.To_array.unchecked_blit ~src:s.suffix ~dim)
                   ~next:(fun ~src_pos:_ ~dst:_ ~dst_pos:_ ~len:_ -> ())))
  ;;
end

open! Base

let rec actual_len : 'arr. 'arr array t -> dim:'arr array dim -> int =
  fun (type arr) (t : arr array t) ~(dim : arr array dim) : int ->
   match t with
   | Base { len; data } ->
     [%test_result: int] len ~expect:(Multi_array.actual_len data ~dim);
     len
   | Spine { prefix_len; data_len; suffix_len; prefix; suffix; data } ->
     [%test_result: int] prefix_len ~expect:(Multi_array.actual_len prefix ~dim);
     [%test_result: int] data_len ~expect:(actual_len data ~dim:(next dim));
     [%test_result: int] suffix_len ~expect:(Multi_array.actual_len suffix ~dim);
     let len = prefix_len + data_len + suffix_len in
     assert (len > 0);
     len
;;

let invariant t ~dim =
  let expect = actual_len t ~dim in
  [%test_result: int] (length t) ~expect
;;
