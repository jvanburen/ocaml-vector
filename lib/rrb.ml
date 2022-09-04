type elt = int

let ( @> ) src x =
  let len = Array.length src in
  let dst = Array.make (len + 1) x in
  ArrayLabels.blit ~src ~src_pos:0 ~dst ~dst_pos:0 ~len;
  dst
;;

let ( <@ ) src x =
  let len = Array.length src in
  let dst = Array.make (len + 1) x in
  ArrayLabels.blit ~src ~src_pos:0 ~dst ~dst_pos:1 ~len;
  dst
;;

let ( -$ ) x y = if x >= y then Some (x - y) else None

type _ spine =
  | Base : 'data array -> 'data array spine
  | Spine :
      { prefix_len : int
      ; data_len : int
      ; suffix_len : int
      ; width : int
      ; prefix : 'data
      ; data : 'data array spine
      ; suffix : 'data
      }
      -> 'data spine

type (_, _) depth =
  | Zero : ('elt, 'elt) depth
  | Nested :
      { inner_size : int
      ; depth : ('arr, 'elt) depth
      }
      -> ('arr array, 'elt) depth

let one = Nested { inner_size = 1; depth = Zero }

type t = elt array spine

include struct
  open Core

  let rec sexp_of_arrays : 'arr. 'arr -> depth:('arr, elt) depth -> Sexp.t =
    fun (type arr) (arr : arr) ~(depth : (arr, elt) depth) : Sexp.t ->
     match depth with
     | Zero -> [%sexp (arr : int)]
     | Nested { inner_size = _; depth } ->
       [%sexp (Array.map arr ~f:(sexp_of_arrays ~depth) : Sexp.t array)]
  ;;

  let rec sexp_of_spine : 'arr. 'arr spine -> depth:('arr, elt) depth -> Sexp.t =
    fun (type arr) (spine : arr spine) ~(depth : (arr, elt) depth) : Sexp.t ->
     match spine with
     | Base arr -> sexp_of_arrays arr ~depth
     | Spine { prefix_len = _; data_len = _; suffix_len = _; width; prefix; suffix; data }
       ->
       [%sexp
         { prefix = (sexp_of_arrays prefix ~depth : Sexp.t)
         ; data =
             (sexp_of_spine data ~depth:(Nested { inner_size = width; depth }) : Sexp.t)
         ; suffix = (sexp_of_arrays suffix ~depth : Sexp.t)
         }]
  ;;

  let sexp_of_t t : Sexp.t = sexp_of_spine t ~depth:one
end

let length (t : t) =
  match t with
  | Spine s -> s.prefix_len + s.data_len + s.suffix_len
  | Base a -> Array.length a
;;

let rec multi_get : 'arr 'elt. ('arr, 'elt) depth -> 'arr -> int -> 'elt =
  fun (type arr elt) (depth : (arr, elt) depth) (arr : arr) (i : int) : elt ->
   match depth with
   | Zero -> if i = 0 then arr else invalid_arg "index out of bounds"
   | Nested { inner_size; depth } ->
     if i < 0 || i / inner_size >= Array.length arr
     then Core.(raise_s [%sexp "OOB:", (i : int), (Array.length arr : int)])
     else multi_get depth arr.(i / inner_size) (i mod inner_size)
;;

let rec get : 'arr. 'arr spine -> depth:('arr, elt) depth -> int -> elt =
  fun (type arr) (spine : arr spine) ~(depth : (arr, elt) depth) (i : int) : elt ->
   match spine with
   | Base arr -> multi_get depth arr i
   | Spine { prefix_len; data_len; suffix_len = _; width; prefix; suffix; data } ->
     (match i -$ prefix_len with
      | None -> multi_get depth prefix i
      | Some i ->
        (match i -$ data_len with
         | Some i -> multi_get depth suffix i
         | None -> get data ~depth:(Nested { inner_size = width; depth }) i))
;;

let get (t : t) i = get t ~depth:one i

let rec multi_set : 'arr 'elt. ('arr, 'elt) depth -> 'arr -> int -> 'elt -> 'arr =
  fun (type arr elt) (depth : (arr, elt) depth) (arr : arr) (i : int) (elt : elt) : arr ->
   match depth with
   | Zero -> if i = 0 then elt else invalid_arg "index out of bounds"
   | Nested { inner_size; depth } ->
     let c = Array.copy arr in
     c.(i / inner_size) <- multi_set depth arr.(i / inner_size) (i mod inner_size) elt;
     c
;;

let rec set : 'arr. 'arr spine -> depth:('arr, elt) depth -> int -> elt -> 'arr spine =
  fun (type arr) (spine : arr spine) ~(depth : (arr, elt) depth) (i : int) (elt : elt)
    : arr spine ->
   match spine with
   | Base arr -> Base (multi_set depth arr i elt)
   | Spine ({ prefix_len; data_len; suffix_len = _; width; prefix; suffix; data } as s) ->
     (match i -$ prefix_len with
      | None -> Spine { s with prefix = multi_set depth prefix i elt }
      | Some i ->
        (match i -$ data_len with
         | Some i -> Spine { s with suffix = multi_set depth suffix i elt }
         | None ->
           Spine
             { s with
               data = set data ~depth:(Nested { inner_size = width; depth }) i elt
             }))
;;

let set (t : t) i x = set t ~depth:one i x

let%test_module _ =
  (module struct
    open! Core
    open Expect_test_helpers_core

    let rec actual_len' : 'arr. 'arr -> depth:('arr, elt) depth -> int =
      fun (type arr) (arr : arr) ~(depth : (arr, elt) depth) : int ->
       match depth with
       | Zero -> 1
       | Nested { inner_size = _; depth } ->
         Array.sum (module Int) arr ~f:(actual_len' ~depth)
    ;;

    let rec actual_len : 'arr. 'arr spine -> depth:('arr, elt) depth -> int =
      fun (type arr) (spine : arr spine) ~(depth : (arr, elt) depth) : int ->
       match spine with
       | Base arr -> actual_len' arr ~depth
       | Spine { prefix_len; data_len; suffix_len; width; prefix; suffix; data } ->
         [%test_result: int] prefix_len ~expect:(actual_len' prefix ~depth);
         [%test_result: int]
           data_len
           ~expect:(actual_len data ~depth:(Nested { inner_size = width; depth }));
         [%test_result: int] suffix_len ~expect:(actual_len' suffix ~depth);
         prefix_len + data_len + suffix_len
    ;;

    let actual_len (t : t) = actual_len t ~depth:one
    let w = 2
    let arr1 ~offset = Array.init w ~f:(fun i -> offset + i)
    let arr2 ~offset = Array.init w ~f:(fun i -> arr1 ~offset:(offset + (i * w)))
    let arr3 ~offset = Array.init w ~f:(fun i -> arr2 ~offset:(offset + (i * w * w)))

    let t =
      Spine
        { prefix_len = w
        ; data_len = (w * w) + (w * w * w) + (w * w)
        ; suffix_len = w
        ; width = w
        ; prefix = arr1 ~offset:0
        ; suffix = arr1 ~offset:18
        ; data =
            Spine
              { prefix_len = w * w
              ; data_len = w * w * w
              ; suffix_len = w * w
              ; width = w * w
              ; prefix = arr2 ~offset:102
              ; suffix = arr2 ~offset:114
              ; data = Base (arr3 ~offset:106)
              }
        }
    ;;

    let%expect_test "set" =
      print_s [%sexp (set t 0 1337 : t)];
      [%expect
        {|
        ((prefix (1337 1))
         (data (
           (prefix (
             (102 103)
             (104 105)))
           (data (
             ((106 107) (108 109))
             ((110 111) (112 113))))
           (suffix (
             (114 115)
             (116 117)))))
         (suffix (18 19))) |}]
    ;;

    let%expect_test "t" =
      print_s [%sexp (t : t)];
      [%expect
        {|
        ((prefix (0 1))
         (data (
           (prefix (
             (102 103)
             (104 105)))
           (data (
             ((106 107) (108 109))
             ((110 111) (112 113))))
           (suffix (
             (114 115)
             (116 117)))))
         (suffix (18 19))) |}]
    ;;

    let%expect_test "length" =
      print_s [%sexp (length t : int)];
      [%expect {| 20 |}];
      print_s [%sexp ~~(actual_len t : int)];
      [%expect {| ("actual_len t" 20) |}]
    ;;

    let%expect_test "get" =
      let l =
        List.init (length t) ~f:(fun i -> i, Or_error.try_with (fun () -> get t i))
      in
      print_s [%sexp (l : (int * int Or_error.t) list)];
      [%expect
        {|
        ((0  (Ok 0))
         (1  (Ok 1))
         (2  (Ok 102))
         (3  (Ok 103))
         (4  (Ok 104))
         (5  (Ok 105))
         (6  (Ok 106))
         (7  (Ok 107))
         (8  (Ok 108))
         (9  (Ok 109))
         (10 (Ok 110))
         (11 (Ok 111))
         (12 (Ok 112))
         (13 (Ok 113))
         (14 (Ok 114))
         (15 (Ok 115))
         (16 (Ok 116))
         (17 (Ok 117))
         (18 (Ok 18))
         (19 (Ok 19))) |}]
    ;;
  end)
;;
