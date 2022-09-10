open! Core

type elt = Multi_array.elt
type 'a dim = 'a Multi_array.Dim.t

type 'a kind = 'a Multi_array.Dim.kind =
  | One : elt array kind
  | Many : 'a array array kind

let max_width = Multi_array.Dim.max_width
let cols = Multi_array.Dim.cols
let next = Multi_array.Dim.next

let ( @> ) src x =
  let len = Array.length src in
  let dst = Array.create x ~len:(len + 1) in
  Array.unsafe_blit ~src ~src_pos:0 ~dst ~dst_pos:0 ~len;
  dst
;;

let ( <@ ) x src =
  let len = Array.length src in
  let dst = Array.create x ~len:(len + 1) in
  Array.unsafe_blit ~src ~src_pos:0 ~dst ~dst_pos:1 ~len;
  dst
;;

let[@inline] ( -$ ) x y = x - y

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

let empty = Base { len = 0; data = [||] }

let length (type a) (t : a t) =
  match t with
  | Base b -> b.len
  | Spine s -> s.prefix_len + s.data_len + s.suffix_len
;;

let rec get : 'a. 'a array t -> int -> dim:'a array dim -> elt =
  fun (type a) (t : a array t) (i : int) ~(dim : a array dim) : elt ->
   match t with
   | Base b -> Multi_array.get b.data i ~dim
   | Spine s ->
     (match i -$ s.prefix_len with
      | q when q < 0 -> Multi_array.get s.prefix i ~dim
      | i ->
        (match i -$ s.data_len with
         | q when q < 0 -> get s.data i ~dim:(next dim)
         | i -> Multi_array.get s.suffix i ~dim))
;;

let rec set : 'a. 'a array t -> int -> elt -> dim:'a array dim -> 'a array t =
  fun (type a) (t : a array t) (i : int) (elt : elt) ~(dim : a array dim) : a array t ->
   match t with
   | Base b -> Base { b with data = Multi_array.set b.data i elt ~dim }
   | Spine s ->
     (match i -$ s.prefix_len with
      | q when q < 0 -> Spine { s with prefix = Multi_array.set s.prefix i elt ~dim }
      | i ->
        (match i -$ s.data_len with
         | q when q < 0 -> Spine { s with data = set s.data i elt ~dim:(next dim) }
         | i -> Spine { s with suffix = Multi_array.set s.suffix i elt ~dim }))
;;

let rec cons : 'a. 'a -> 'a array t -> dim:'a array dim -> 'a array t =
  fun (type a) (elt : a) (t : a array t) ~(dim : a array dim) : a array t ->
   match t with
   | Base { len; data } ->
     if Array.length data < max_width - 2
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
     if Array.length data < max_width - 2
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
          'a array t -> f:(elt -> 'acc -> 'acc) -> init:'acc -> dim:'a array dim -> 'acc
  =
  fun (type a acc)
      (t : a array t)
      ~(f : elt -> acc -> acc)
      ~(init : acc)
      ~(dim : a array dim)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_right b.data ~f ~init ~dim
   | Spine s ->
     let init = Multi_array.fold_right s.suffix ~f ~init ~dim in
     let init = fold_right s.data ~f ~init ~dim:(next dim) in
     Multi_array.fold_right s.prefix ~f ~init ~dim
;;

module To_array = struct
  let[@inline] blit_helper ~src_len ~src_pos ~(dst : elt array) ~dst_pos ~len ~blit ~next =
    let written_from_src =
      match src_len -$ src_pos with
      | q when q < 0 -> 0
      | src_len ->
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

module Builder = struct
  type 'a spine = 'a t

  type _ node =
    | Empty : _ node
    | Base :
        { mutable len : int
        ; mutable data : 'data array
        }
        -> 'data array node
    | Spine :
        { mutable prefix_len : int
        ; mutable prefix : 'data
        ; mutable data : 'data array node
        ; mutable suffix_len : int
        ; mutable suffix : 'data
        }
        -> 'data node

  type t = elt array node

  let[@inline] trunc a ~len = if len = Array.length a then a else Array.sub a ~pos:0 ~len

  let[@inline] extend_nonempty src ~len =
    let src_len = Array.length src in
    if len = src_len
    then src
    else (
      let dst = Array.create src.(0) ~len in
      Array.blit ~src ~src_pos:1 ~dst ~dst_pos:1 ~len:(src_len - 1);
      dst)
  ;;

  let[@inline] set_maybe_extend src i x ~max_len =
    if i >= max_len
    then None
    else
      Some
        (let src_len = Array.length src in
         if i < src_len
         then (
           src.(i) <- x;
           src)
         else (
           let dst = Array.create x ~len:max_len in
           Array.blito ~src ~dst ();
           dst))
  ;;

  let rec add : 'a. 'a array node -> 'a -> 'a array node =
    fun (type a) (node : a array node) (elt : a) : a array node ->
     match node with
     | Empty -> Base { len = 1; data = Array.create elt ~len:(max_width - 2) }
     | Base b ->
       (match set_maybe_extend b.data b.len elt ~max_len:(max_width - 2) with
        | Some data ->
          b.data <- data;
          b.len <- b.len + 1;
          node
        | None ->
          Spine
            { prefix = b.data
            ; prefix_len = b.len
            ; data = Empty
            ; suffix = Array.create elt ~len:max_width
            ; suffix_len = 1
            })
     | Spine s ->
       (match set_maybe_extend s.suffix s.suffix_len elt ~max_len:max_width with
        | Some suffix ->
          s.suffix <- suffix;
          s.suffix_len <- s.suffix_len + 1;
          node
        | None ->
          s.data <- add s.data s.suffix;
          s.suffix <- Array.create elt ~len:max_width;
          s.suffix_len <- 1;
          node)
  ;;

  let rec add_arr : 'a. 'a array node -> 'a array -> pos:int -> len:int -> 'a array node =
    (* TODO: could probably avoid copying some arrays in here in special cases. *)
    fun (type a) (node : a array node) (a : a array) ~pos ~len : a array node ->
     if len = 0
     then node
     else (
       match node with
       | Empty ->
         let node = Base { len = 1; data = Array.create a.(pos) ~len:(max_width - 2) } in
         add_arr node a ~pos:(pos + 1) ~len:(len - 1)
       | Base b ->
         let added = min len (Array.length b.data - b.len) in
         Array.blit ~src:a ~src_pos:pos ~dst:b.data ~dst_pos:b.len ~len:added;
         b.len <- b.len + added;
         let pos = pos + added
         and len = len - added in
         if len = 0
         then node
         else (
           let node =
             Spine
               { prefix = b.data
               ; prefix_len = b.len
               ; data = Empty
               ; suffix = Array.create a.(pos) ~len:max_width
               ; suffix_len = 1
               }
           in
           add_arr node a ~pos:(pos + 1) ~len:(len - 1))
       | Spine s ->
         let added = min len (Array.length s.suffix - s.suffix_len) in
         Array.blit ~src:a ~src_pos:pos ~dst:s.suffix ~dst_pos:s.suffix_len ~len:added;
         s.suffix_len <- s.suffix_len + added;
         let pos = pos + added
         and len = len - added in
         if len = 0
         then node
         else (
           s.data <- add s.data s.suffix;
           s.suffix_len <- 1;
           s.suffix <- Array.create a.(pos) ~len:max_width;
           add_arr node a ~pos:(pos + 1) ~len:(len - 1)))
  ;;

  let rec to_spine : 'a. 'a array node -> dim:'a array dim -> 'a array spine =
    fun (type a) (node : a array node) ~(dim : a array dim) : a array spine ->
     match node with
     | Empty -> empty
     | Base { len; data } -> Base { len = len * cols dim; data = trunc data ~len }
     | Spine { prefix_len; prefix; data; suffix_len; suffix } ->
       let data = to_spine data ~dim:(next dim) in
       Spine
         { prefix_len = prefix_len * cols dim
         ; prefix = trunc prefix ~len:prefix_len
         ; suffix_len = suffix_len * cols dim
         ; suffix = trunc suffix ~len:suffix_len
         ; data
         ; data_len = length data
         }
  ;;

  let rec of_spine : 'a. 'a array spine -> dim:'a array dim -> 'a array node =
    fun (type a) (node : a array spine) ~(dim : a array dim) : a array node ->
     match node with
     | Base b ->
       (match Array.length b.data with
        | 0 -> Empty
        | len -> Base { len; data = extend_nonempty b.data ~len:(max_width - 2) })
     | Spine { prefix; data; suffix; _ } ->
       Spine
         { prefix_len = Array.length prefix
         ; prefix
         ; data = of_spine data ~dim:(next dim)
         ; suffix_len = Array.length suffix
         ; suffix
         }
  ;;

  let[@inline] add_arr node a = add_arr node a ~pos:0 ~len:(Array.length a)

  let rec add_multi_array : 'a. t -> 'a array -> dim:'a array dim -> t =
    fun (type a) (t : t) (arr : a array) ~(dim : a array dim) : t ->
     match Multi_array.Dim.kind dim with
     | One -> add_arr t arr
     | Many ->
       let dim = Multi_array.Dim.inner dim in
       Array.fold arr ~init:t ~f:(fun node arr -> add_multi_array node arr ~dim)
  ;;

  let rec add_spine : 'a. t -> 'a array spine -> dim:'a array dim -> t =
    fun (type a) (t : t) (spine : a array spine) ~(dim : a array dim) : t ->
     match spine with
     | Base b -> add_multi_array t b.data ~dim
     | Spine s ->
       let t = add_multi_array t s.prefix ~dim in
       let t = add_spine t s.data ~dim:(next dim) in
       add_multi_array t s.suffix ~dim
  ;;

  (* TODO: allow specifying pos/len (for better [sub] implementation) *)
  let add_spine t spine ~dim =
    match t with
    | Empty -> of_spine spine ~dim
    | t -> if phys_equal spine empty then t else add_spine t spine ~dim
  ;;

  let empty = Empty
end
