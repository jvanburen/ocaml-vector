open Base

type any = Multi_array.elt
type +'a t = any array Spine.t

external of_any : any -> 'a = "%opaque"
external to_any : 'a -> any = "%opaque"
external opaque_magic : 'a -> 'b = "%opaque"

let dim : any array Multi_array.Dim.t = Multi_array.Dim.one
let empty = Spine.empty
let length (t : _ t) = Spine.length t
let is_empty (t : _ t) = Spine.length t = 0
let get (t : 'a t) i : 'a = of_any (Spine.get t i ~dim)
let set (t : 'a t) i (x : 'a) = Spine.set t i (to_any x) ~dim
let cons (x : 'a) (t : 'a t) = Spine.cons (to_any x) t ~dim
let snoc (t : 'a t) (x : 'a) = Spine.snoc t (to_any x) ~dim

let map (type a b) (t : a t) ~(f : a -> b) : b t =
  Spine.map t ~f:(opaque_magic f : any -> any) ~dim
;;

let rev (type a) (t : a t) : a t = Spine.rev t ~dim

let fold_left (t : 'a t) ~(init : 'acc) ~(f : 'acc -> 'a -> 'acc) =
  Spine.fold_left t ~init ~f:(opaque_magic f : 'acc -> any -> 'acc) ~dim
;;

let fold_right (t : 'a t) ~(init : 'acc) ~(f : 'a -> 'acc -> 'acc) =
  Spine.fold_right t ~init ~f:(opaque_magic f : any -> 'acc -> 'acc) ~dim
;;

let fold = fold_left
let iter t ~f = fold t ~init:() ~f:(fun () x -> f x)
let to_list t = fold_right t ~init:[] ~f:List.cons
let to_list_rev t = fold_left t ~init:[] ~f:(fun l x -> x :: l)

module To_array = struct
  let unsafe_blit (type a) ~(src : a t) ~src_pos ~(dst : a array) ~dst_pos ~len =
    Spine.To_array.unchecked_blit
      ~src
      ~src_pos
      ~dst:(opaque_magic dst : any array)
      ~dst_pos
      ~len
      ~dim
  ;;

  let blit (type a) ~(src : a t) ~src_pos ~(dst : a array) ~dst_pos ~len =
    Ordered_collection_common.check_pos_len_exn
      ~pos:src_pos
      ~len
      ~total_length:(length src);
    Ordered_collection_common.check_pos_len_exn
      ~pos:dst_pos
      ~len
      ~total_length:(Array.length dst);
    unsafe_blit ~src ~src_pos ~dst ~dst_pos ~len
  ;;

  let sub t ~pos ~len =
    Ordered_collection_common.check_pos_len_exn ~pos ~len ~total_length:(length t);
    match len with
    | 0 -> [||]
    | len ->
      let dst = Array.create (get t 0) ~len in
      unsafe_blit ~src:t ~src_pos:1 ~dst ~dst_pos:1 ~len:(len - 1);
      dst
  ;;

  let blito ~src ?(src_pos = 0) ?(src_len = length src - src_pos) ~dst ?(dst_pos = 0) () =
    blit ~src ~src_pos ~len:src_len ~dst ~dst_pos
  ;;

  let subo ?(pos = 0) ?len src =
    sub
      src
      ~pos
      ~len:
        (match len with
         | Some i -> i
         | None -> length src - pos)
  ;;
end

let to_array t =
  match length t with
  | 0 -> [||]
  | len ->
    let dst = Array.create (get t 0) ~len in
    To_array.blit ~src:t ~src_pos:1 ~dst ~dst_pos:1 ~len:(len - 1);
    dst
;;

let init =
  let rec go n ~f t i = if i = n then t else go n ~f (snoc t (f i)) (i + 1) in
  fun n ~f ->
    if n < 0 then invalid_arg "Vec.init";
    go n ~f empty 0
;;

let invariant (t : _ t) = Spine.invariant t ~dim

let sexp_of_t (sexp_of_a : 'a -> Sexp.t) (t : 'a t) =
  Sexp.List (fold_right t ~init:[] ~f:(fun a acc -> sexp_of_a a :: acc))
;;

let of_list l = List.fold_right l ~init:empty ~f:cons

let%test_module _ =
  (module struct
    open! Core
    open Expect_test_helpers_core

    type int_elt = any

    let sexp_of_int_elt any = [%sexp (of_any any : int)]

    type debug = int_elt array Spine.t [@@deriving sexp_of]

    let test_result t ~expect =
      Invariant.invariant [%here] t [%sexp_of: debug] (fun () ->
        [%test_result: int] (length t) ~expect:(List.length expect);
        List.iteri expect ~f:(fun i expect -> [%test_result: int] (get t i) ~expect))
    ;;

    let check t =
      invariant t;
      test_result t ~expect:(to_list t)
    ;;

    let%expect_test "of_list" =
      let (_ : int t) =
        List.fold_right [ 0; 1; 2; 3; 4; 5 ] ~init:empty ~f:(fun x t ->
          let t = cons x t in
          print_s [%sexp (Or_error.try_with (fun () -> check t) : unit Or_error.t)];
          print_s [%sexp (t : debug)];
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
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3))
        (Ok ())
        ((prefix (1 2))
         (prefix_len 2)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3))
        (Ok ())
        ((prefix (0 1 2))
         (prefix_len 3)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (3 4 5))
         (suffix_len 3)) |}]
    ;;

    let t = init 20 ~f:succ

    let%expect_test "t" =
      check t;
      [%test_result: int] (length t) ~expect:20;
      print_s [%sexp (t : debug)];
      [%expect
        {|
        ((prefix (1 2 3))
         (prefix_len 3)
         (data (
           (prefix (
             (4  5  6)
             (7  8  9)
             (10 11 12)))
           (prefix_len 9)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (13 14 15)
             (16 17 18)))
           (suffix_len 6)))
         (data_len 15)
         (suffix (19 20))
         (suffix_len 2)) |}]
    ;;

    let%expect_test "to_list" =
      print_s [%sexp (to_list t : int list)];
      [%expect {| (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) |}]
    ;;

    let%expect_test "sexp_of" =
      print_s [%sexp (t : int t)];
      [%expect {| (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) |}]
    ;;

    let%expect_test "set" =
      print_s [%sexp (set t 0 1337 : debug)];
      [%expect
        {|
        ((prefix (1337 2 3))
         (prefix_len 3)
         (data (
           (prefix (
             (4  5  6)
             (7  8  9)
             (10 11 12)))
           (prefix_len 9)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (13 14 15)
             (16 17 18)))
           (suffix_len 6)))
         (data_len 15)
         (suffix (19 20))
         (suffix_len 2)) |}]
    ;;

    (* TODO: test [set] *)
    (*     let%expect_test "set" = *)
    (*       print_s [%sexp (t : debug)]; *)
    (*       let l = Array.of_list (to_list t in       *)
    (*       for i = 0 to length t - 1 do *)
    (* let expect =  *)
    (* k *)

    (*   done *)
    (*   List.init       *)
    (*   print_elems t; *)
    (*   [%expect *)
    (*     {| *)
    (*     ((prefix (1 2 3)) *)
    (*      (prefix_len 3) *)
    (*      (width      3) *)
    (*      (data ( *)
    (*        (prefix ( *)
    (*          (4  5  6) *)
    (*          (7  8  9) *)
    (*          (10 11 12))) *)
    (*        (prefix_len 9) *)
    (*        (width      3) *)
    (*        (data ((len 0) (data ()))) *)
    (*        (data_len 0) *)
    (*        (suffix ( *)
    (*          (13 14 15) *)
    (*          (16 17 18))) *)
    (*        (suffix_len 6))) *)
    (*      (data_len 15) *)
    (*      (suffix (19 20)) *)
    (*      (suffix_len 2)) *)
    (*     ((0  (Ok 1)) *)
    (*      (1  (Ok 2)) *)
    (*      (2  (Ok 3)) *)
    (*      (3  (Ok 4)) *)
    (*      (4  (Ok 5)) *)
    (*      (5  (Ok 6)) *)
    (*      (6  (Ok 7)) *)
    (*      (7  (Ok 8)) *)
    (*      (8  (Ok 9)) *)
    (*      (9  (Ok 10)) *)
    (*      (10 (Ok 11)) *)
    (*      (11 (Ok 12)) *)
    (*      (12 (Ok 13)) *)
    (*      (13 (Ok 14)) *)
    (*      (14 (Ok 15)) *)
    (*      (15 (Ok 16)) *)
    (*      (16 (Ok 17)) *)
    (*      (17 (Ok 18)) *)
    (*      (18 (Ok 19)) *)
    (*      (19 (Ok 20))) |}] *)
    (* ;; *)

    let%expect_test "cons" =
      let t = cons 0 t in
      print_s [%sexp (t : debug)];
      [%expect
        {|
        ((prefix (0))
         (prefix_len 1)
         (data (
           (prefix ((1 2 3)))
           (prefix_len 3)
           (data (
             (len 9)
             (data ((
               (4  5  6)
               (7  8  9)
               (10 11 12))))))
           (data_len 9)
           (suffix (
             (13 14 15)
             (16 17 18)))
           (suffix_len 6)))
         (data_len 18)
         (suffix (19 20))
         (suffix_len 2)) |}];
      [%test_result: int] (length t) ~expect:21;
      check t;
      print_s [%sexp (t : int t)];
      [%expect {| (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20) |}]
    ;;

    let%expect_test "snoc" =
      let t = snoc t 21 in
      print_s [%sexp (t : debug)];
      [%expect
        {|
        ((prefix (1 2 3))
         (prefix_len 3)
         (data (
           (prefix (
             (4  5  6)
             (7  8  9)
             (10 11 12)))
           (prefix_len 9)
           (data ((len 0) (data ())))
           (data_len 0)
           (suffix (
             (13 14 15)
             (16 17 18)))
           (suffix_len 6)))
         (data_len 15)
         (suffix (19 20 21))
         (suffix_len 3)) |}];
      [%test_result: int] (length t) ~expect:21;
      check t;
      print_s [%sexp (t : int t)];
      [%expect {| (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21) |}]
    ;;

    let%expect_test "to_array" =
      let t = ref empty in
      [%test_result: int array] (to_array !t) ~expect:[||];
      for i = 0 to 30 do
        t := snoc !t i;
        [%test_result: int array] (to_array !t) ~expect:(Array.of_list (to_list !t))
      done;
      [%expect]
    ;;

    let%expect_test "rev" =
      let t = ref empty in
      [%test_result: int array] (to_array (rev !t)) ~expect:(Array.rev (to_array !t));
      for i = 0 to 30 do
        t := snoc !t i;
        [%test_result: int array] (to_array (rev !t)) ~expect:(Array.rev (to_array !t))
      done;
      [%expect]
    ;;
  end)
;;
