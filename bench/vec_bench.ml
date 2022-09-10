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
    let concat = concat_map ~f:Fn.id

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
