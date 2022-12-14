open! Core

module View = struct
  type ('a, 'b) t =
    | []
    | ( :: ) of 'a * 'b
end

type any = Multi_array.elt
type +'a t = any array Spine.t

let dim : any array Multi_array.Dim.t = Multi_array.Dim.one

external of_any : any -> 'a = "%opaque"
external to_any : 'a -> any = "%opaque"
external opaque_magic : 'a -> 'b = "%opaque"

include Indexed_container.Make (struct
  type nonrec 'a t = 'a t

  let length = `Custom Spine.length

  let fold (t : 'a t) ~(init : 'acc) ~(f : 'acc -> 'a -> 'acc) =
    Spine.fold_left t ~init ~f:(opaque_magic f : 'acc -> any -> 'acc) ~dim
  ;;

  let iter = `Define_using_fold
  let foldi = `Define_using_fold
  let iteri = `Define_using_fold
end)

let empty = Spine.empty
let is_empty (t : _ t) = Spine.length t = 0
let get (t : 'a t) i : 'a = of_any (Spine.get t i ~dim)
let set (t : 'a t) i (x : 'a) = Spine.set t i (to_any x) ~dim
let cons (x : 'a) (t : 'a t) = Spine.cons (to_any x) t ~dim
let snoc (t : 'a t) (x : 'a) : 'a t = Spine.snoc t (to_any x) ~dim
let singleton x = cons x empty

let map (type a b) (t : a t) ~(f : a -> b) : b t =
  Spine.map t ~f:(opaque_magic f : any -> any) ~dim
;;

let rev (type a) (t : a t) : a t = Spine.rev t ~dim

let fold_left (t : 'a t) ~(init : 'acc) ~(f : 'acc -> 'a -> 'acc) =
  Spine.fold_left t ~init ~f:(opaque_magic f : 'acc -> any -> 'acc) ~dim
;;

let fold_right (t : 'a t) ~(f : 'a -> 'acc -> 'acc) ~(init : 'acc) =
  Spine.fold_right t ~f:(opaque_magic f : any -> 'acc -> 'acc) ~init ~dim
;;

let to_list t = fold_right t ~init:[] ~f:List.cons

let to_sequence (type a) (t : a t) : a Sequence.t =
  let len = length t in
  Sequence.unfold_step ~init:0 ~f:(fun i ->
    if i = len then Done else Yield (get t i, i + 1))
;;

module Lexicographic = struct
  type nonrec 'a t = 'a t

  let compare (type a) (compare_a : a -> a -> int) (x : a t) (y : a t) : int =
    [%compare: a Sequence.t] (to_sequence x) (to_sequence y)
  ;;
end

let compare (type a) (compare_a : a -> a -> int) (x : a t) (y : a t) : int =
  let cmp = Int.compare (length x) (length y) in
  if cmp <> 0 then cmp else [%compare: a Lexicographic.t] x y
;;

let equal (type a) (equal_a : a -> a -> bool) (x : a t) (y : a t) : bool =
  phys_equal x y
  || (length x = length y && [%equal: a Sequence.t] (to_sequence x) (to_sequence y))
;;

let append (type a) (x : a t) (y : a t) : a t =
  if is_empty x
  then y
  else if is_empty y
  then x
  else (
    let b = Spine.Builder.of_spine x ~dim in
    Spine.Builder.add_spine b y ~dim |> Spine.Builder.to_spine ~dim)
;;

let init =
  let rec go n ~f b i =
    if i = n
    then Spine.Builder.to_spine b ~dim
    else go n ~f (Spine.Builder.add b (to_any (f i))) (i + 1)
  in
  fun n ~f ->
    if n < 0 then invalid_arg "Vec.init";
    go n ~f Spine.Builder.empty 0
;;

let filter_map (type a b) (t : a t) ~(f : a -> b option) : b t =
  fold t ~init:Spine.Builder.empty ~f:(fun b x ->
    match f (of_any x) with
    | None -> b
    | Some x -> Spine.Builder.add b (to_any x))
  |> Spine.Builder.to_spine ~dim
;;

let filter t ~f = filter_map t ~f:(fun x -> Option.some_if (f x) x)

let sub (type a) (t : a t) ~pos ~len : a t =
  Ordered_collection_common.check_pos_len_exn ~pos ~len ~total_length:(length t);
  (* TODO: better implementation *)
  init len ~f:(fun i -> get t (pos + i))
;;

let subo ?(pos = 0) ?len t =
  match len with
  | Some len -> sub t ~pos ~len
  | None -> sub t ~pos ~len:(length t - pos)
;;

(* TODO: better implementations *)
let take t n = subo t ~len:(Int.clamp_exn n ~min:0 ~max:(length t))
let drop t n = subo t ~pos:(Int.clamp_exn n ~min:0 ~max:(length t))
let split_n t n = take t n, drop t n

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
    match len with
    | Some len -> sub src ~pos ~len
    | None -> sub src ~pos ~len:(length src - pos)
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

let invariant (t : _ t) = Spine.invariant t ~dim

let sexp_of_t (sexp_of_a : 'a -> Sexp.t) (t : 'a t) =
  Sexp.List (fold_right t ~init:[] ~f:(fun a acc -> sexp_of_a a :: acc))
;;

let of_list (type a) (l : a list) : a t =
  List.fold (opaque_magic l : any list) ~init:Spine.Builder.empty ~f:Spine.Builder.add
  |> Spine.Builder.to_spine ~dim
;;

let of_sequence s =
  Sequence.fold
    (opaque_magic s : any Sequence.t)
    ~init:Spine.Builder.empty
    ~f:Spine.Builder.add
  |> Spine.Builder.to_spine ~dim
;;

let of_array (type a) (a : a array) : a t =
  Spine.Builder.(add_arr empty) (opaque_magic a : any array)
  |> Spine.Builder.to_spine ~dim
;;

let t_of_sexp (type a) (a_of_sexp : Sexp.t -> a) (sexp : Sexp.t) : a t =
  of_array ([%of_sexp: a array] sexp)
;;

let sort (type a) (t : a t) ~(compare : a -> a -> int) : a t =
  let a = to_array t in
  Array.sort a ~compare;
  of_array a
;;

let stable_sort (type a) (t : a t) ~(compare : a -> a -> int) : a t =
  let a = to_array t in
  Array.stable_sort a ~compare;
  of_array a
;;

let dedup_and_sort (type a) (t : a t) ~(compare : a -> a -> int) : a t =
  match length t with
  | 0 -> t
  | len ->
    let a = to_array t in
    Array.sort a ~compare;
    let prev = ref a.(0) in
    let builder = ref Spine.Builder.(add empty (to_any !prev)) in
    for i = 1 to len - 1 do
      let next = a.(i) in
      if compare next !prev <> 0
      then (
        prev := next;
        builder := Spine.Builder.add !builder (to_any next))
    done;
    Spine.Builder.to_spine !builder ~dim
;;

let hd_exn t = get t 0
let hd t = if is_empty t then None else hd_exn t
let last_exn t = get t (length t - 1)
let last t = if is_empty t then None else last_exn t

let view (t : 'a t) : ('a, 'a t) View.t =
  if is_empty t then [] else get t 0 :: subo t ~pos:1
;;

let weiv (t : 'a t) : ('a t, 'a) View.t =
  match length t with
  | 0 -> []
  | len -> sub t ~pos:0 ~len:(len - 1) :: get t (len - 1)
;;

let concat_map t ~f =
  fold t ~init:Spine.Builder.empty ~f:(fun b x -> Spine.Builder.add_spine b (f x) ~dim)
  |> Spine.Builder.to_spine ~dim
;;

let concat t = concat_map t ~f:Fn.id

include Monad.Make (struct
  type nonrec 'a t = 'a t

  let return = singleton
  let map = `Custom map
  let bind = concat_map
end)

include
  Quickcheckable.Of_quickcheckable1
    (List)
    (struct
      type nonrec 'a t = 'a t

      let of_quickcheckable = of_list
      let to_quickcheckable = to_list
    end)

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

    let%test_unit "list conversions" =
      Quickcheck.test [%quickcheck.generator: int list] ~f:(fun l ->
        [%test_result: int list] (to_list (of_list l)) ~expect:l)
    ;;

    let%test_unit "array conversions" =
      Quickcheck.test [%quickcheck.generator: int array] ~f:(fun a ->
        [%test_result: int array] (to_array (of_array a)) ~expect:a)
    ;;

    let%test_unit "init" =
      Quickcheck.test [%quickcheck.generator: int array] ~f:(fun a ->
        [%test_result: int array]
          (to_array (init (Array.length a) ~f:(Array.get a)))
          ~expect:a)
    ;;

    let%test_unit "concat_map" =
      Quickcheck.test
        [%quickcheck.generator: int list * (int -> int list)]
        ~f:(fun (l, f) ->
        let f' x = of_list (f x) in
        [%test_result: int list]
          (to_list (concat_map (of_list l) ~f:f'))
          ~expect:(List.concat_map l ~f))
    ;;

    let%test_unit "append" =
      Quickcheck.test [%quickcheck.generator: int t * int t] ~f:(fun (t1, t2) ->
        [%test_result: int list] (to_list (append t1 t2)) ~expect:(to_list t1 @ to_list t2))
    ;;

    let%test_unit "rev" =
      Quickcheck.test [%quickcheck.generator: int t] ~f:(fun t ->
        [%test_result: int list] (to_list (rev t)) ~expect:(List.rev (to_list t)))
    ;;

    let%expect_test "dedup_and_sort" =
      print_s
        [%sexp
          (dedup_and_sort (of_list [ 1; 5; 2; 3; 2; 2; 7; 8; 4; 9; 6; 0; 2 ]) ~compare
            : int t)];
      [%expect {| (0 1 2 3 4 5 6 7 8 9)  |}];
      Quickcheck.test [%quickcheck.generator: int t] ~f:(fun t ->
        [%test_result: int list]
          (to_list (dedup_and_sort t ~compare))
          ~expect:(List.dedup_and_sort (to_list t) ~compare));
      [%expect {||}]
    ;;

    let%expect_test "of_list" =
      let (_ : int t) =
        List.fold [ 0; 1; 2; 3; 4; 5 ] ~init:empty ~f:(fun t x ->
          let t = snoc t x in
          check t;
          print_s [%sexp (t : debug)];
          t)
      in
      [%expect
        {|
        ((len 1) (data (0)))
        ((prefix (0))
         (prefix_len 1)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (1))
         (suffix_len 1))
        ((prefix (0))
         (prefix_len 1)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (1 2))
         (suffix_len 2))
        ((prefix (0))
         (prefix_len 1)
         (data ((len 0) (data ())))
         (data_len 0)
         (suffix (1 2 3))
         (suffix_len 3))
        ((prefix (0))
         (prefix_len 1)
         (data ((len 3) (data ((1 2 3)))))
         (data_len 3)
         (suffix (4))
         (suffix_len 1))
        ((prefix (0))
         (prefix_len 1)
         (data ((len 3) (data ((1 2 3)))))
         (data_len 3)
         (suffix (4 5))
         (suffix_len 2)) |}]
    ;;

    let t = init 20 ~f:succ

    let%expect_test "t" =
      check t;
      [%test_result: int] (length t) ~expect:20;
      print_s [%sexp (t : debug)];
      [%expect
        {|
        ((prefix (1))
         (prefix_len 1)
         (data (
           (prefix ((2 3 4)))
           (prefix_len 3)
           (data (
             (len 9)
             (data ((
               (5  6  7)
               (8  9  10)
               (11 12 13))))))
           (data_len 9)
           (suffix (
             (14 15 16)
             (17 18 19)))
           (suffix_len 6)))
         (data_len 18)
         (suffix (20))
         (suffix_len 1)) |}]
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
        ((prefix (1337))
         (prefix_len 1)
         (data (
           (prefix ((2 3 4)))
           (prefix_len 3)
           (data (
             (len 9)
             (data ((
               (5  6  7)
               (8  9  10)
               (11 12 13))))))
           (data_len 9)
           (suffix (
             (14 15 16)
             (17 18 19)))
           (suffix_len 6)))
         (data_len 18)
         (suffix (20))
         (suffix_len 1)) |}]
    ;;

    let%expect_test "cons" =
      let t = cons 0 t in
      print_s [%sexp (t : debug)];
      [%expect
        {|
        ((prefix (0 1))
         (prefix_len 2)
         (data (
           (prefix ((2 3 4)))
           (prefix_len 3)
           (data (
             (len 9)
             (data ((
               (5  6  7)
               (8  9  10)
               (11 12 13))))))
           (data_len 9)
           (suffix (
             (14 15 16)
             (17 18 19)))
           (suffix_len 6)))
         (data_len 18)
         (suffix (20))
         (suffix_len 1)) |}];
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
        ((prefix (1))
         (prefix_len 1)
         (data (
           (prefix ((2 3 4)))
           (prefix_len 3)
           (data (
             (len 9)
             (data ((
               (5  6  7)
               (8  9  10)
               (11 12 13))))))
           (data_len 9)
           (suffix (
             (14 15 16)
             (17 18 19)))
           (suffix_len 6)))
         (data_len 18)
         (suffix (20 21))
         (suffix_len 2)) |}];
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
      [%expect {||}]
    ;;
  end)
;;
