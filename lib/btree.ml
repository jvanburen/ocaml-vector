open! Core

module With = struct
  module Let_syntax = struct
    module Let_syntax = struct
      let bind t ~f = t f
    end
  end
end

let rec sexp_of_obj o =
  let tag = Obj.tag o in
  assert (tag <> Obj.unaligned_tag);
  if tag = Obj.int_tag
  then [%sexp (Obj.obj o : int)]
  else if tag = Obj.double_tag
  then [%sexp (Obj.obj o : float)]
  else if tag = Obj.double_array_tag
  then [%sexp (Obj.obj o : float array)]
  else if tag = Obj.string_tag
  then [%sexp (Obj.obj o : string)]
  else
    Sexp.List
      (if tag < Obj.no_scan_tag
      then List.init (Obj.size o) ~f:(fun i -> sexp_of_obj (Obj.field o i))
      else List.init (Obj.size o) ~f:(fun i -> [%sexp (Obj.raw_field o i : nativeint)]))
;;

type elt = private
  | Immediate
  | Not_a_float of int

let sexp_of_elt (e : elt) = sexp_of_obj (Obj.repr e)

type 'a node =
  { size : int
  ; storage : 'a array (* TODO: uniform array *)
  }

let sexp_of_node sexp_of_a { size; storage } =
  if size = 0
  then Sexp.unit
  else (
    let size = sprintf "#%d:" size in
    [%sexp (size : string), (storage : a array)])
;;

(** may have length up to [2*max_width] *)
type 'a wide = 'a array

let width (w : _ wide) = Array.length w

module Dim = struct
  type _ t =
    | One : int -> elt node t
    | S : int * 'a node t -> 'a node node t

  let max_width = 4
  let one = One 1

  let cols (type a) (t : a t) : int =
    match t with
    | One i -> i
    | S (i, _) -> i
  ;;

  let next (type a) (t : a t) : a node t =
    match t with
    | One i -> S (max_width * i, t)
    | S (i, _) -> S (max_width * i, t)
  ;;
end

type 'a dim = 'a Dim.t
type btree = Btree : 'a dim * 'a -> btree

let rec sexp_of_btree (Btree (dim, node)) =
  match dim with
  | One _ -> [%sexp (node : elt node)]
  | S (_, dim) ->
    let node =
      { node with storage = Array.map node.storage ~f:(fun node -> Btree (dim, node)) }
    in
    [%sexp (node : btree node)]
;;

let cols = Dim.cols
let next = Dim.next
let empty = { size = 0; storage = [||] }
let max_width = Dim.max_width
let min_width = Dim.max_width - 1
let increasing = Array.init (max_width + 1) ~f:Fn.id
let ( @ ) = Array.append
let ( += ) r x = r := !r + x
let ( -= ) r x = r := !r - x
let length t = t.size

(* let get_backtrace () = *)
(*   let bt = Backtrace.get () |> Backtrace.to_string_list in *)
(*   let bt = *)
(*     List.drop_while bt ~f:(fun s -> *)
(*       not (String.is_substring s ~substring:"get_backtrace")) *)
(*   in *)
(*   let bt = List.drop bt 1 in *)
(*   List.take_while bt ~f:(fun s -> not (String.is_substring s ~substring:"Or_error")) *)
(* ;; *)

let rec invariant : 't. 't -> strict:bool -> dim:'t dim -> unit =
  fun (type t) (t : t) ~strict ~(dim : t dim) : unit ->
   Invariant.invariant
     [%here]
     t
     (fun t -> [%sexp (Btree (dim, t) : btree) (* , (get_backtrace () : string list) *)])
     (fun () ->
       let check_width t =
         let width = Array.length t.storage in
         if strict && not (Int.between width ~low:min_width ~high:max_width)
         then raise_s [%sexp "badly sized level in tree", ~~(width : int)]
       in
       match dim with
       | One _ ->
         check_width t;
         [%test_result: int] t.size ~expect:(Array.length t.storage)
       | S (_, dim) ->
         let width = Array.length t.storage in
         check_width t;
         Array.iteri t.storage ~f:(fun i t -> invariant t ~dim ~strict:(i <> width - 1));
         [%test_result: int] t.size ~expect:(Array.sum (module Int) t.storage ~f:length))
;;

let invariant (type t) (t : t) ~(dim : t dim) = invariant t ~dim ~strict:false

let invariant_wide (type t) (w : t array) ~(dim : t node dim) =
  match dim with
  | One _ -> assert (Array.length w <= 2 * max_width)
  | S (_, dim) -> Array.invariant (invariant ~dim) w
;;

let show_in_backtrace name here ts dim f =
  try
    let ts = f () in
    (match ts with
     | First t -> invariant t ~dim
     | Second (t1, t2) ->
       invariant t1 ~dim;
       invariant t2 ~dim);
    ts
  with
  | exn ->
    let ts = List.map ts ~f:(fun t -> Btree (dim, t)) in
    let name = sprintf !"%s[%{Source_code_position}]" name here in
    raise_s [%sexp (name : string), (ts : btree list), "raised", (exn : Exn.t)]
;;

(** post-increment *)
let ( .++() ) r amount =
  let pre = !r in
  r := pre + amount;
  pre
;;

let rec get : 't. 't node -> int -> dim:'t node dim -> elt =
  fun (type t) (t : t node) (i : int) ~(dim : t node dim) : elt ->
   match dim with
   | One _ ->
     Exn.reraise_uncaught
       (sprintf !"get t.storage.(%d) = %{Sexp#mach}" i (sexp_of_obj (Obj.repr t.storage)))
       (fun () -> t.storage.(i))
   | S (_, dim) ->
     let j = ref 0 in
     let i = ref i in
     while !i >= t.storage.(!j).size do
       i -= t.storage.(j.++(1)).size
     done;
     get t.storage.(!j) !i ~dim
;;

let rec set : 't. 't node -> int -> elt -> dim:'t node dim -> 't node =
  fun (type t) (t : t node) (i : int) (elt : elt) ~(dim : t node dim) : t node ->
   match dim with
   | One _ ->
     let storage = Array.copy t.storage in
     storage.(i) <- elt;
     { t with storage }
   | S (_, dim) ->
     let j = ref 0 in
     let i = ref i in
     while !i >= t.storage.(!j).size do
       i -= t.storage.(j.++(1)).size
     done;
     let storage = Array.copy t.storage in
     storage.(!j) <- set t.storage.(!j) !i elt ~dim;
     { t with storage }
;;

let rec fold_left :
          't 'acc.
          't node -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'t node dim -> 'acc
  =
  fun (type t acc) (t : t node) ~(init : acc) ~(f : acc -> elt -> acc) ~(dim : t node dim)
    : acc ->
   match dim with
   | One _ -> Array.fold t.storage ~init ~f
   | S (_, dim) ->
     Array.fold t.storage ~init ~f:(fun init t' -> fold_left t' ~init ~f ~dim)
;;

let rec fold_right :
          't 'acc.
          't node -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'t node dim -> 'acc
  =
  fun (type t acc) (t : t node) ~(init : acc) ~(f : elt -> acc -> acc) ~(dim : t node dim)
    : acc ->
   match dim with
   | One _ -> Array.fold_right t.storage ~init ~f
   | S (_, dim) ->
     Array.fold_right t.storage ~init ~f:(fun t' init -> fold_right t' ~init ~f ~dim)
;;

(* TODO: return the same thing if the elements are phys_equal *)

let rec map : 't. 't node -> f:('a -> 'b) -> dim:'t node dim -> 't node =
  fun (type t) (t : t node) ~(f : elt -> elt) ~(dim : t node dim) : t node ->
   match dim with
   | One _ -> { t with storage = Array.map t.storage ~f }
   | S (_, dim) -> { t with storage = Array.map t.storage ~f:(fun t -> map t ~f ~dim) }
;;

(** peel a non-wide node off the front of a wide node *)
let lsplit2_wide (type a) (w : a wide) ~(dim : a node dim) : a node * a wide =
  let len = Int.min max_width (width w) in
  let storage = Array.subo w ~len in
  let t =
    { storage
    ; size =
        (match dim with
         | One _ -> Array.length storage
         | S _ -> Array.sum (module Int) storage ~f:length)
    }
  in
  t, Array.subo w ~pos:len
;;

(* TODO: use the sizes to construct the new node without so much copying *)

let rec append : 'a. 'a wide -> 'a wide -> dim:'a node dim -> 'a wide =
  fun (type a) (lhs : a wide) (rhs : a wide) ~(dim : a node dim) : a wide ->
   match dim with
   | One _ -> lhs @ rhs
   | S (_, dim) ->
     (match width lhs, width rhs with
      | _, 0 -> lhs
      | 0, _ -> rhs
      | lhs_len, rhs_len ->
        let prefix_len = lhs_len - 1 in
        let next = ref lhs.(prefix_len).storage in
        if width !next >= min_width
        then lhs @ rhs
        else (
          (* TODO: determine the length of [storage] in advance by using the sizes or something
             maybe this could be done by keeping track of the sum of widths of the child nodes
          *)
          let mid = Array.create empty ~len:(1 + rhs_len) in
          let mid_len = ref 0 in
          let rhs_pos = ref 0 in
          while width !next > 0 do
            if width !next < min_width && !rhs_pos < rhs_len
            then next := append !next rhs.(rhs_pos.++(1)).storage ~dim;
            assert (width !next >= min_width || !rhs_pos >= rhs_len);
            let l, r = lsplit2_wide !next ~dim in
            mid.(mid_len.++(1)) <- l;
            next := r
          done;
          let suffix_len = rhs_len - !rhs_pos in
          let dst = Array.create empty ~len:(prefix_len + !mid_len + suffix_len) in
          Array.blit ~src:lhs ~dst ~src_pos:0 ~dst_pos:0 ~len:prefix_len;
          Array.blit ~src:mid ~dst ~src_pos:0 ~dst_pos:prefix_len ~len:!mid_len;
          Array.blit
            ~src:rhs
            ~dst
            ~src_pos:!rhs_pos
            ~dst_pos:(prefix_len + !mid_len)
            ~len:suffix_len;
          dst))
;;

let create (type a) (storage : a array) ~(dim : a node dim) : a node =
  let size =
    match dim with
    | One _ -> Array.length storage
    | S _ -> Array.sum (module Int) storage ~f:length
  in
  let t = { size; storage } in
  invariant t ~dim;
  t
;;

let append (type a) (t1 : a node) (t2 : a node) ~fill ~(dim : a node dim)
  : (a node, a node * a node) Either.t
  =
  let%bind.With () = show_in_backtrace "append" [%here] [ t1; t2 ] dim in
  let appended = append t1.storage t2.storage ~dim in
  invariant_wide appended ~dim;
  let len = Array.length appended in
  if len <= max_width
  then First (create appended ~dim)
  else (
    assert (len <= max_width * 2);
    let i =
      match fill with
      | `Left -> max_width
      | `Split -> len / 2
      | `Right -> len - max_width
    in
    let lhs = create (Array.subo appended ~len:i) ~dim in
    let rhs = create (Array.subo appended ~pos:i) ~dim in
    Second (lhs, rhs))
;;

let append (type a) (t1 : a node) (t2 : a node) ~fill ~(dim : a node dim) =
  let t = append t1 t2 ~fill ~dim in
  [%test_result: int]
    (match t with
     | First t -> length t
     | Second (t1, t2) -> length t1 + length t2)
    ~expect:(length t1 + length t2);
  t
;;

let rec actual_len : 't. 't node -> dim:'t node dim -> int =
  let open Base in
  fun (type t) (t : t node) ~(dim : t node dim) : int ->
    let len =
      match dim with
      | One one ->
        assert (one = 1);
        Array.length t.storage
      | S (cols, dim) ->
        Array.fold t.storage ~init:0 ~f:(fun (* i *) acc t' ->
          (* [%test_result: int] t.prefix_sizes.(i) ~expect:acc; *)
          let len = actual_len t' ~dim in
          assert (len <= cols);
          acc + len)
    in
    [%test_result: int] len ~expect:t.size;
    (* [%test_result: int] t.prefix_sizes.(Array.length t.storage) ~expect:t.size; *)
    len
;;

let cons (type t) (x : t) (t : t node) ~(dim : t node dim) =
  let size =
    match dim with
    | One _ -> 1
    | S _ -> x.size
  in
  append { size; storage = [| x |] } t ~dim
;;

let snoc (type t) (t : t node) (x : t) ~(dim : t node dim) =
  let size =
    match dim with
    | One _ -> 1
    | S _ -> x.size
  in
  append t { size; storage = [| x |] } ~dim
;;

let singleton x ~dim = cons x empty ~dim

type _ finger =
  | Top : _ finger
  | Finger :
      { pos : int
      ; len : int
      ; arr : 'a node
      ; up : 'a node node finger
      }
      -> 'a node finger

let rec to_finger :
          't. 't node -> dim:'t node dim -> up:'t node node finger -> elt node finger
  =
  fun (type t) (t : t node) ~(dim : t node dim) ~(up : t node node finger)
    : elt node finger ->
   match Array.length t.storage with
   | 0 -> next_finger up ~dim:(next dim)
   | len ->
     (match dim with
      | One _ -> Finger { pos = 0; len; arr = t; up }
      | S (_, down) ->
        to_finger t.storage.(0) ~dim:down ~up:(Finger { pos = 0; len; arr = t; up }))

and next_finger : 't. 't node finger -> dim:'t node dim -> elt node finger =
  fun (type t) (f : t node finger) ~(dim : t node dim) : elt node finger ->
   match f with
   | Top -> Top
   | Finger ({ pos; len; arr; up } as f) ->
     if pos + 1 = len
     then next_finger up ~dim:(next dim)
     else (
       match dim with
       | One _ -> Top
       | S (_, down) ->
         let pos = pos + 1 in
         let next = Finger { f with pos } in
         to_finger arr.storage.(pos) ~dim:down ~up:next)
;;

let to_sequence (type t) (t : t node) ~(dim : t node dim) : elt Sequence.t =
  Sequence.unfold_step
    ~init:(to_finger t ~dim ~up:Top)
    ~f:(fun (finger : elt node finger) ->
    match finger with
    | Top -> Done
    | Finger { pos; arr; _ } as f -> Yield (arr.storage.(pos), next_finger f ~dim:Dim.one))
;;
