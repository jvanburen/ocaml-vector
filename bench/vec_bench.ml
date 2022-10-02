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
