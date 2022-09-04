open Base

type elt = int [@@deriving sexp_of]
type t = elt array Spine.t [@@deriving sexp_of]

let one : elt array Spine.Multi_array.Dims.t = [ 1 ]
let empty = Spine.empty
let length (t : t) = Spine.length t
let get (t : t) i = Spine.get t i ~dims:one
let set (t : t) i x = Spine.set t i x ~dims:one
let cons elt (t : t) = Spine.cons elt t ~dims:one
let fold_left t ~init ~f = Spine.fold_left t ~init ~f ~dims:one
let fold_right t ~init ~f = Spine.fold_right t ~init ~f ~dims:one
let fold = fold_left
let to_list t = fold_right t ~init:[] ~f:List.cons
let invariant (t : t) = Spine.invariant t ~dims:one

let of_list l =
  (* TODO: not the greatest implementation *)
  List.fold_right l ~init:empty ~f:cons
;;

let%test_module _ =
  (module struct
    open! Core
    open Expect_test_helpers_core

    let%expect_test "of_list" =
      let (_ : t) =
        List.fold_right [ 0; 1; 2; 3; 4; 5 ] ~init:empty ~f:(fun x t ->
          let t = cons x t in
          print_s [%sexp (Or_error.try_with (fun () -> invariant t) : unit Or_error.t)];
          print_s [%sexp (t : t)];
          t)
      in
      [%expect
        {|
        (Ok ())
        ((len 1) (data (5)))
        (Ok ())
        ((len 2) (data (4 5)))
        (Ok ())
        ((len 3) (data (3 4 5)))
        (Ok ())
        ((prefix (2))
         (prefix_len 1)
         (width      3)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3))
        (Ok ())
        ((prefix (1 2))
         (prefix_len 2)
         (width      3)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3))
        (Ok ())
        ((prefix (0 1 2))
         (prefix_len 3)
         (width      3)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3)) |}]
    ;;

    let t = of_list (List.init 20 ~f:(( + ) 1))

    let%test_unit "invariant" = invariant t

    let%expect_test "length" =
      print_s [%sexp (length t : int)];
      [%expect {| 20 |}]
    ;;

    let%expect_test "t" =
      print_s [%sexp (t : t)];
      [%expect
        {|
        ((prefix (1 2))
         (prefix_len 2)
         (width      3)
         (data (
           (prefix (
             (3 4 5)
             (6 7 8)))
           (prefix_len 6)
           (width      3)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (9  10 11)
             (12 13 14)
             (15 16 17)))
           (suffix_len 9)))
         (data_len 15)
         (suffix (18 19 20))
         (suffix_len 3)) |}]
    ;;

    let%expect_test "to_list" =
      print_s [%sexp (to_list t : int list)];
      [%expect {| () |}]
    ;;

    let%expect_test "set" =
      print_s [%sexp (set t 0 1337 : t)];
      [%expect
        {|
        ((prefix (1337 2))
         (prefix_len 2)
         (width      3)
         (data (
           (prefix (
             (3 4 5)
             (6 7 8)))
           (prefix_len 6)
           (width      3)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (9  10 11)
             (12 13 14)
             (15 16 17)))
           (suffix_len 9)))
         (data_len 15)
         (suffix (18 19 20))
         (suffix_len 3)) |}]
    ;;

    let print_elems t =
      let l =
        List.init (length t) ~f:(fun i -> i, Or_error.try_with (fun () -> get t i))
      in
      print_s [%sexp (l : (int * int Or_error.t) list)]
    ;;

    let%expect_test "get" =
      print_elems t;
      [%expect
        {|
        ((0  (Ok 1))
         (1  (Ok 2))
         (2  (Ok 3))
         (3  (Ok 4))
         (4  (Ok 5))
         (5  (Ok 6))
         (6  (Ok 7))
         (7  (Ok 8))
         (8  (Ok 9))
         (9  (Ok 10))
         (10 (Ok 11))
         (11 (Ok 12))
         (12 (Ok 13))
         (13 (Ok 14))
         (14 (Ok 15))
         (15 (Ok 16))
         (16 (Ok 17))
         (17 (Ok 18))
         (18 (Ok 19))
         (19 (Ok 20))) |}]
    ;;

    let%expect_test "cons" =
      let t = cons 0 t in
      print_s [%sexp (t : t)];
      [%expect
        {|
        ((prefix (0 1 2))
         (prefix_len 3)
         (width      3)
         (data (
           (prefix (
             (3 4 5)
             (6 7 8)))
           (prefix_len 6)
           (width      3)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (9  10 11)
             (12 13 14)
             (15 16 17)))
           (suffix_len 9)))
         (data_len 15)
         (suffix (18 19 20))
         (suffix_len 3)) |}];
      invariant t;
      print_s [%sexp (length t : int)];
      [%expect {| 21 |}];
      print_elems t;
      [%expect
        {|
        ((0  (Ok 0))
         (1  (Ok 1))
         (2  (Ok 2))
         (3  (Ok 3))
         (4  (Ok 4))
         (5  (Ok 5))
         (6  (Ok 6))
         (7  (Ok 7))
         (8  (Ok 8))
         (9  (Ok 9))
         (10 (Ok 10))
         (11 (Ok 11))
         (12 (Ok 12))
         (13 (Ok 13))
         (14 (Ok 14))
         (15 (Ok 15))
         (16 (Ok 16))
         (17 (Ok 17))
         (18 (Ok 18))
         (19 (Ok 19))
         (20 (Ok 20))) |}]
    ;;
  end)
;;
