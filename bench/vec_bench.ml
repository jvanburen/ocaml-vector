open! Core

let prng () =
  let seed = [ "ocaml"; "immutable"; "vector"; "benchmarks" ] in
  Random.State.make (Array.of_list_map seed ~f:[%hash: string])
;;

let len = 1337
let strings_array = Array.init len ~f:Int.to_string
let strings_list = List.init len ~f:Int.to_string

module type Empty = sig end

module Make_tests (M : sig
  type 'a t

  val is_list : bool
  val is_array : bool

  (* val length : _ t -> int *)
  (* val set : 'a t -> int -> 'a -> 'a t *)

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val init : int -> f:(int -> 'a) -> 'a t
  val get : 'a t -> int -> 'a
  val cons : 'a -> 'a t -> 'a t
  val hd_exn : 'a t -> 'a
  val last_exn : 'a t -> 'a
  val append : 'a t -> 'a t -> 'a t
  val concat : 'a t t -> 'a t
  val fold_left : 'a t -> init:'acc -> f:('acc -> 'a -> 'acc) -> 'acc
  val fold_right : 'a t -> f:('a -> 'acc -> 'acc) -> init:'acc -> 'acc
  val of_list : 'a list -> 'a t
  val to_list : 'a t -> 'a list
  val of_array : 'a array -> 'a t
  val to_array : 'a t -> 'a array
end) =
struct
  let strings = M.init len ~f:Int.to_string
  let ints = M.init len ~f:[%hash: int]

  include
    (val if M.is_list
         then (module struct end : Empty)
         else
           (module struct
             let%bench "of_list" = M.of_list strings_list
             let%bench "to_list" = M.to_list strings
           end : Empty))

  include
    (val if M.is_array
         then (module struct end : Empty)
         else
           (module struct
             let%bench "of_array" = M.of_array strings_array
             let%bench "to_array" = M.to_array strings
           end : Empty))

  let%bench "map" = M.map strings ~f:Fn.id

  let%bench_fun "get" =
    let prng = prng () in
    fun () -> M.get ints (Random.State.int prng len)
  ;;

  let%bench "fold_right" = M.fold_right ints ~init:0 ~f:( + )
  let%bench "fold_left" = M.fold_left ints ~init:0 ~f:( + )
  let%bench "cons" = M.cons "front" strings
  let%bench "hd_exn" = M.hd_exn strings
  let%bench "last_exn" = M.last_exn strings
  let%bench "append" = M.append strings strings

  let%bench_fun "concat wide" =
    let inner = M.init 10 ~f:[%hash: int] in
    let nested = M.init len ~f:(fun (_ : int) -> inner) in
    fun () -> M.concat nested
  ;;

  let%bench_fun "concat narrow" =
    let inner = M.init len ~f:[%hash: int] in
    let nested = M.init 10 ~f:(fun (_ : int) -> inner) in
    fun () -> M.concat nested
  ;;
end

let%bench_module "List" =
  (module Make_tests (struct
    include List

    let is_list = true
    let is_array = false
    let of_array = Array.to_list
    let get = nth_exn
  end))
;;

let%bench_module "Array" =
  (module Make_tests (struct
    include Array

    let is_list = false
    let is_array = true
    let of_array t = t
    let hd_exn t = t.(0)
    let last_exn t = t.(Array.length t - 1)
    let fold_left = fold

    let concat (type a) (ts : a t t) =
      let ts : a Uniform_array.t Uniform_array.t = Obj.magic ts in
      let outer_len = Uniform_array.length ts in
      let total_len = ref 0 in
      for i = 0 to outer_len - 1 do
        total_len := !total_len + Uniform_array.length (Uniform_array.unsafe_get ts i)
      done;
      let dst = Uniform_array.unsafe_create_uninitialized ~len:!total_len in
      let dst_pos = ref 0 in
      for i = 0 to outer_len - 1 do
        let src = Uniform_array.unsafe_get ts i in
        let len = Uniform_array.length src in
        Uniform_array.unsafe_blit ~src ~src_pos:0 ~dst ~dst_pos:!dst_pos ~len;
        dst_pos := !dst_pos + len
      done;
      (Obj.magic dst : a array)
    ;;

    let cons x xs =
      let len = Array.length xs in
      let dst = Array.create x ~len:(len + 1) in
      Array.unsafe_blit ~src:xs ~src_pos:0 ~dst ~dst_pos:1 ~len;
      dst
    ;;
  end))
;;

let%bench_module "Vec" =
  (module Make_tests (struct
    include Vec

    let is_list = false
    let is_array = false
  end))
;;
(*
benchmark results 2022-09-10

Vec branching factor: 32

┌─────────────────────────────────────────────────────┬─────────────┬────────────┬────────────┬───────────┬────────────┐
│ Name                                                │    Time/Run │    mWd/Run │   mjWd/Run │  Prom/Run │ Percentage │
├─────────────────────────────────────────────────────┼─────────────┼────────────┼────────────┼───────────┼────────────┤
│ [bench/vec_bench.ml:Make_tests:List] of_array       │  1_599.95ns │  4_016.00w │     30.95w │    30.95w │      2.57% │
│ [bench/vec_bench.ml:Make_tests:List] to_array       │  9_461.68ns │      5.00w │  1_338.00w │           │     15.18% │
│ [bench/vec_bench.ml:Make_tests:List] map            │  3_736.80ns │  4_011.00w │     30.84w │    30.84w │      5.99% │
│ [bench/vec_bench.ml:Make_tests:List] get            │    638.04ns │      2.00w │            │           │      1.02% │
│ [bench/vec_bench.ml:Make_tests:List] fold_right     │  6_147.24ns │  4_016.00w │     30.99w │    30.99w │      9.86% │
│ [bench/vec_bench.ml:Make_tests:List] fold_left      │  3_538.05ns │            │            │           │      5.68% │
│ [bench/vec_bench.ml:Make_tests:List] cons           │      3.07ns │      3.00w │            │           │            │
│ [bench/vec_bench.ml:Make_tests:List] hd_exn         │      2.22ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:List] last_exn       │  1_258.94ns │            │            │           │      2.02% │
│ [bench/vec_bench.ml:Make_tests:List] append         │  3_666.79ns │  4_011.00w │     30.82w │    30.82w │      5.88% │
│ [bench/vec_bench.ml:Make_tests:List] concat wide    │ 47_547.00ns │ 44_096.00w │  3_580.85w │ 3_580.85w │     76.27% │
│ [bench/vec_bench.ml:Make_tests:List] concat narrow  │ 51_284.09ns │ 36_134.00w │  2_599.49w │ 2_599.49w │     82.27% │
│ [bench/vec_bench.ml:Make_tests:Array] of_list       │  9_200.33ns │      5.00w │  1_338.00w │           │     14.76% │
│ [bench/vec_bench.ml:Make_tests:Array] to_list       │  1_583.07ns │  4_016.00w │     31.05w │    31.05w │      2.54% │
│ [bench/vec_bench.ml:Make_tests:Array] map           │  8_877.18ns │            │  1_338.00w │           │     14.24% │
│ [bench/vec_bench.ml:Make_tests:Array] get           │      7.71ns │            │            │           │      0.01% │
│ [bench/vec_bench.ml:Make_tests:Array] fold_right    │  2_860.01ns │            │            │           │      4.59% │
│ [bench/vec_bench.ml:Make_tests:Array] fold_left     │  2_819.46ns │            │            │           │      4.52% │
│ [bench/vec_bench.ml:Make_tests:Array] cons          │  7_249.08ns │            │  1_339.00w │           │     11.63% │
│ [bench/vec_bench.ml:Make_tests:Array] hd_exn        │      2.47ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Array] last_exn      │      2.52ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Array] append        │ 10_537.72ns │            │  2_675.00w │           │     16.90% │
│ [bench/vec_bench.ml:Make_tests:Array] concat wide   │ 62_339.92ns │  4_016.00w │ 14_709.00w │           │    100.00% │
│ [bench/vec_bench.ml:Make_tests:Array] concat narrow │ 48_685.00ns │     46.00w │ 13_371.00w │           │     78.10% │
│ [bench/vec_bench.ml:Make_tests:Vec] of_list         │  9_947.81ns │  4_191.00w │     22.87w │    22.87w │     15.96% │
│ [bench/vec_bench.ml:Make_tests:Vec] to_list         │  3_848.25ns │  4_017.00w │     30.93w │    30.93w │      6.17% │
│ [bench/vec_bench.ml:Make_tests:Vec] of_array        │  2_202.45ns │  1_601.00w │      8.39w │     8.39w │      3.53% │
│ [bench/vec_bench.ml:Make_tests:Vec] to_array        │  8_715.44ns │    477.00w │  1_338.00w │           │     13.98% │
│ [bench/vec_bench.ml:Make_tests:Vec] map             │  6_363.06ns │  1_705.00w │      7.01w │     7.01w │     10.21% │
│ [bench/vec_bench.ml:Make_tests:Vec] get             │     23.54ns │      8.82w │            │           │      0.04% │
│ [bench/vec_bench.ml:Make_tests:Vec] fold_right      │  3_657.83ns │      6.00w │            │           │      5.87% │
│ [bench/vec_bench.ml:Make_tests:Vec] fold_left       │  3_490.27ns │      6.00w │            │           │      5.60% │
│ [bench/vec_bench.ml:Make_tests:Vec] cons            │     30.08ns │     39.00w │            │           │      0.05% │
│ [bench/vec_bench.ml:Make_tests:Vec] hd_exn          │      5.66ns │      3.00w │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Vec] last_exn        │      7.93ns │      7.00w │            │           │      0.01% │
│ [bench/vec_bench.ml:Make_tests:Vec] append          │  2_756.32ns │  1_682.00w │      9.70w │     9.70w │      4.42% │
│ [bench/vec_bench.ml:Make_tests:Vec] concat wide     │ 49_207.18ns │ 15_209.00w │    860.96w │   860.96w │     78.93% │
│ [bench/vec_bench.ml:Make_tests:Vec] concat narrow   │ 28_007.10ns │ 13_937.00w │    711.51w │   711.51w │     44.93% │
└─────────────────────────────────────────────────────┴─────────────┴────────────┴────────────┴───────────┴────────────┘


Hardware Overview:

Model Name:	MacBook Pro
Model Identifier:	MacBookPro18,2
Chip:	Apple M1 Max
Total Number of Cores:	10 (8 performance and 2 efficiency)
Memory:	64 GB
*)
