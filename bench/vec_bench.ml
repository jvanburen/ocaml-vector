open! Core

let prng () =
  let seed = [ "ocaml"; "immutable"; "vector"; "benchmarks" ] in
  Random.State.make (Array.of_list_map seed ~f:[%hash: string])
;;

let len = 1337
let strings_array = Array.init len ~f:Int.to_string
let strings_list = List.init len ~f:Int.to_string
let string_seq = Array.to_sequence_mutable strings_array

module type Empty = sig end

module Make_tests (M : sig
  type 'a t

  val is_list : bool
  val is_array : bool

  (* val length : _ t -> int *)
  (* val set : 'a t -> int -> 'a -> 'a t *)

  val map : 'a t -> f:('a -> 'b) -> 'b t
  val filter : 'a t -> f:('a -> bool) -> 'a t
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
  val of_sequence : 'a Sequence.t -> 'a t
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

             let%bench "get sequential (1k)" =
               assert (len >= 1000);
               for i = 0 to 999 do
                 ignore (Sys.opaque_identity (M.get ints i))
               done
             ;;

             let%bench_fun "get random (1k)" =
               let prng = prng () in
               let indices = Array.init 1_000 ~f:(fun _ -> Random.State.int prng len) in
               fun () ->
                 for i = 0 to 999 do
                   ignore (Sys.opaque_identity (M.get ints (Array.unsafe_get indices i)))
                 done
             ;;
           end : Empty))

  include
    (val if M.is_array
         then (module struct end : Empty)
         else
           (module struct
             let%bench "of_array" = M.of_array strings_array
             let%bench "to_array" = M.to_array strings

             let%bench "cons 10" =
               let m = ref strings in
               for _ = 0 to 9 do
                 m := M.cons "front" !m
               done;
               !m
             ;;
           end : Empty))

  let%bench "of_sequence" = M.of_sequence string_seq
  let%bench "map once" = M.map strings ~f:Fn.id
  let%bench "map x3" = strings |> M.map ~f:Fn.id |> M.map ~f:Fn.id |> M.map ~f:Fn.id
  let%bench "filter" = ints |> M.filter ~f:(fun i -> i % 3 = 0)
  let%bench "fold_right" = M.fold_right ints ~init:0 ~f:( + )
  let%bench "fold_left" = M.fold_left ints ~init:0 ~f:( + )
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
    let of_sequence = Sequence.to_list
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
    let of_sequence = Sequence.to_array

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

┌───────────────────────────────────────────────────────────┬─────────────┬────────────┬────────────┬───────────┬────────────┐
│ Name                                                      │    Time/Run │    mWd/Run │   mjWd/Run │  Prom/Run │ Percentage │
├───────────────────────────────────────────────────────────┼─────────────┼────────────┼────────────┼───────────┼────────────┤
│ [bench/vec_bench.ml:Make_tests:List] of_array             │  1_600.70ns │  4_016.00w │     30.97w │    30.97w │      3.16% │
│ [bench/vec_bench.ml:Make_tests:List] to_array             │  9_483.08ns │      5.00w │  1_338.00w │           │     18.75% │
│ [bench/vec_bench.ml:Make_tests:List] cons 10              │     22.65ns │     30.00w │            │           │      0.04% │
│ [bench/vec_bench.ml:Make_tests:List] of_sequence          │  9_279.23ns │ 10_536.00w │    121.12w │   121.12w │     18.35% │
│ [bench/vec_bench.ml:Make_tests:List] map                  │  3_752.97ns │  4_011.00w │     30.89w │    30.89w │      7.42% │
│ [bench/vec_bench.ml:Make_tests:List] fold_right           │  6_205.43ns │  4_016.00w │     30.99w │    30.99w │     12.27% │
│ [bench/vec_bench.ml:Make_tests:List] fold_left            │  3_576.20ns │            │            │           │      7.07% │
│ [bench/vec_bench.ml:Make_tests:List] hd_exn               │      2.21ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:List] last_exn             │  1_279.16ns │            │            │           │      2.53% │
│ [bench/vec_bench.ml:Make_tests:List] append               │  3_661.35ns │  4_011.00w │     30.81w │    30.81w │      7.24% │
│ [bench/vec_bench.ml:Make_tests:List] concat wide          │ 47_304.65ns │ 44_096.00w │  3_578.89w │ 3_578.89w │     93.52% │
│ [bench/vec_bench.ml:Make_tests:List] concat narrow        │ 50_580.93ns │ 36_134.00w │  2_608.32w │ 2_608.32w │    100.00% │
│ [bench/vec_bench.ml:Make_tests:Array] of_list             │  9_308.50ns │      5.00w │  1_338.00w │           │     18.40% │
│ [bench/vec_bench.ml:Make_tests:Array] to_list             │  1_586.67ns │  4_016.00w │     30.98w │    30.98w │      3.14% │
│ [bench/vec_bench.ml:Make_tests:Array] get sequential (1k) │  2_131.14ns │            │            │           │      4.21% │
│ [bench/vec_bench.ml:Make_tests:Array] get random (1k)     │  2_231.39ns │            │            │           │      4.41% │
│ [bench/vec_bench.ml:Make_tests:Array] of_sequence         │ 17_259.96ns │ 12_038.00w │  1_437.17w │    99.17w │     34.12% │
│ [bench/vec_bench.ml:Make_tests:Array] map                 │  9_669.73ns │            │  1_338.00w │           │     19.12% │
│ [bench/vec_bench.ml:Make_tests:Array] fold_right          │  2_904.04ns │            │            │           │      5.74% │
│ [bench/vec_bench.ml:Make_tests:Array] fold_left           │  2_836.81ns │            │            │           │      5.61% │
│ [bench/vec_bench.ml:Make_tests:Array] hd_exn              │      2.49ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Array] last_exn            │      2.58ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Array] append              │ 10_706.32ns │            │  2_675.00w │           │     21.17% │
│ [bench/vec_bench.ml:Make_tests:Array] concat wide         │ 45_073.06ns │            │ 13_371.00w │           │     89.11% │
│ [bench/vec_bench.ml:Make_tests:Array] concat narrow       │ 42_023.58ns │            │ 13_371.00w │           │     83.08% │
│ [bench/vec_bench.ml:Make_tests:Vec] of_list               │  9_732.37ns │  4_185.00w │     23.38w │    23.38w │     19.24% │
│ [bench/vec_bench.ml:Make_tests:Vec] to_list               │  3_902.56ns │  4_032.00w │     30.06w │    30.06w │      7.72% │
│ [bench/vec_bench.ml:Make_tests:Vec] get sequential (1k)   │  4_801.75ns │            │            │           │      9.49% │
│ [bench/vec_bench.ml:Make_tests:Vec] get random (1k)       │  6_475.17ns │            │            │           │     12.80% │
│ [bench/vec_bench.ml:Make_tests:Vec] of_array              │  2_055.45ns │  1_595.00w │      8.56w │     8.56w │      4.06% │
│ [bench/vec_bench.ml:Make_tests:Vec] to_array              │  8_176.18ns │    460.00w │  1_338.00w │           │     16.16% │
│ [bench/vec_bench.ml:Make_tests:Vec] cons 10               │    230.68ns │    218.00w │            │           │      0.46% │
│ [bench/vec_bench.ml:Make_tests:Vec] of_sequence           │ 11_815.02ns │  8_196.00w │     44.89w │    44.89w │     23.36% │
│ [bench/vec_bench.ml:Make_tests:Vec] map                   │  5_408.31ns │  1_447.00w │      5.97w │     5.97w │     10.69% │
│ [bench/vec_bench.ml:Make_tests:Vec] fold_right            │  3_610.85ns │     21.00w │            │           │      7.14% │
│ [bench/vec_bench.ml:Make_tests:Vec] fold_left             │  3_512.35ns │     21.00w │            │           │      6.94% │
│ [bench/vec_bench.ml:Make_tests:Vec] hd_exn                │      2.91ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Vec] last_exn              │      4.13ns │            │            │           │            │
│ [bench/vec_bench.ml:Make_tests:Vec] append                │  2_575.10ns │  1_664.00w │      9.59w │     9.59w │      5.09% │
│ [bench/vec_bench.ml:Make_tests:Vec] concat wide           │ 46_191.12ns │ 15_218.00w │    860.12w │   860.12w │     91.32% │
│ [bench/vec_bench.ml:Make_tests:Vec] concat narrow         │ 26_710.08ns │ 13_871.00w │    709.81w │   709.81w │     52.81% │
└───────────────────────────────────────────────────────────┴─────────────┴────────────┴────────────┴───────────┴────────────┘

Hardware Overview:

Model Name:	MacBook Pro
Model Identifier:	MacBookPro18,2
Chip:	Apple M1 Max
Total Number of Cores:	10 (8 performance and 2 efficiency)
Memory:	64 GB

Compiler:
target: aarch64-apple-darwin21.6.0
flambda: true
safe_string: true
default_safe_string: true
flat_float_array: false
function_sections: false
afl_instrument: false
windows_unicode: false
supports_shared_libraries: true
naked_pointers: true
*)
