open! Core

let rrb_bits = 6
let rrb_max_height = 6
let rrb_branching = 1 lsl rrb_bits
let rrb_mask = rrb_branching - 1
let max_search_error = 2
let max_width = 4
let min_width = max_width - (max_search_error / 2)

module Id = Unique_id.Int ()

module Size_table = struct
  type t =
    { id : Id.t
    ; sizes : int array
    }

  let create len = { id = Id.create (); sizes = Array.create ~len 0 }
  let clone t = { id = Id.create (); sizes = Array.copy t.sizes }

  let inc t ~len =
    let dst = create len in
    Array.blit
      ~src:t.sizes
      ~src_pos:0
      ~dst:dst.sizes
      ~dst_pos:0
      ~len:(Int.max len (Array.length t.sizes));
    dst
  ;;
end

module Node = struct
  type (_, _) t =
    | Leaf :
        { len : int
        ; id : Id.t
        ; child : 'a array (* TODO: uniform array *)
        }
        -> ('a, 'a) t
    | Internal :
        { len : int
        ; id : Id.t
        ; size_table : Size_table.t option
        ; child : ('a, 'b) t array
        }
        -> ('a, ('a, 'b) t) t

  let len (type a b) (t : (a, b) t) =
    match t with
    | Leaf { len; _ } -> len
    | Internal { len; _ } -> len
  ;;

  let id (type a b) (t : (a, b) t) =
    match t with
    | Leaf { id; _ } -> id
    | Internal { id; _ } -> id
  ;;
end

module Shift : sig
  type (_, _) t = private
    | Z : { bits : int } -> ('a, ('a, 'a) Node.t) t
    | S :
        { bits : int
        ; child_shift : ('a, 'b) t
        }
        -> ('a, ('a, 'b) Node.t) t

  val bits : _ t -> int
  val parent : ('a, 'b) t -> ('a, ('a, 'b) Node.t) t
  val leaf : ('a, ('a, 'a) Node.t) t
  val one : ('a, ('a, ('a, 'a) Node.t) Node.t) t
end = struct
  type (_, _) t =
    | Z : { bits : int } -> ('a, ('a, 'a) Node.t) t
    | S :
        { bits : int
        ; child_shift : ('a, 'b) t
        }
        -> ('a, ('a, 'b) Node.t) t

  let bits (type a b) (t : (a, b) t) : int =
    match t with
    | Z { bits } -> bits
    | S { bits; child_shift = _ } -> bits
  ;;

  let parent (type a b) (t : (a, b) t) : (a, (a, b) Node.t) t =
    S { bits = rrb_bits + bits t; child_shift = t }
  ;;

  let leaf = Z { bits = 0 }
  let one = S { bits = rrb_bits; child_shift = Z { bits = 0 } }
end

module Tree_node = struct
  type 'a t = Node : ('a, _) Node.t -> 'a t [@@unboxed]
end

type size_table = Size_table.t =
  { id : Id.t
  ; sizes : int array
  }

type ('a, 'b) node = ('a, 'b) Node.t =
  | Leaf :
      { len : int
      ; id : Id.t
      ; child : 'a array (* TODO: uniform array *)
      }
      -> ('a, 'a) node
  | Internal :
      { len : int
      ; id : Id.t
      ; size_table : Size_table.t option
      ; child : ('a, 'b) node array
      }
      -> ('a, ('a, 'b) node) node

type (_, _) shift = private
  | Z : { bits : int } -> ('a, ('a, 'a) Node.t) shift
  | S :
      { bits : int
      ; child_shift : ('a, 'b) shift
      }
      -> ('a, ('a, 'b) Node.t) shift

type 'a leaf_node = ('a, 'a) Node.t
type 'a tree_node = 'a Tree_node.t = Node : ('a, _) Node.t -> 'a tree_node [@@unboxed]

let leaf child ~len =
  assert (len = Array.length child);
  Leaf { len; id = Id.create (); child }
;;

let leaf_children (Leaf { child; _ }) = child
let ( .&() ) (Leaf { child; _ }) i = child.(i)

type 'a t =
  { cnt : int
  ; shift : int
  ; tail_len : int
  ; tail : 'a leaf_node
  ; root : 'a tree_node
  }

let tail_id = Id.create ()
let empty_leaf = Leaf { len = 0; id = tail_id; child = [||] }

let empty =
  { cnt = 0; shift = 0; root = Node empty_leaf; tail_len = 0; tail = empty_leaf }
;;

let append_part_exn left right ~left_len ~len =
  assert (Int.between left_len ~low:0 ~high:(Array.length left));
  assert (len > left_len);
  let right_len = len - left_len in
  assert (right_len <= Array.length right);
  let dst = Array.create ~len right.(0) in
  Array.blit ~src:left ~src_pos:0 ~dst ~dst_pos:0 ~len:left_len;
  Array.blit ~src:right ~src_pos:0 ~dst ~dst_pos:left_len ~len:right_len;
  dst
;;

let rec size_sub_trie : 'a 'b. ('a, 'b) Node.t -> ('a, 'b) Shift.t -> acc:int -> int =
  fun (type a b) (node : (a, b) Node.t) ~(shift : (a, b) shift) ~(acc : int) ->
   match shift, node with
   | Leaf leaf ->
     assert (shift <= leaf_node_shift);
     leaf.len
   | Internal { size_table; len; child; _ } ->
     assert (shift > leaf_node_shift);
     (match size_table with
      | Some table -> table.sizes.(len - 1)
      | None ->
        size_sub_trie
          (Node child.(len - 1))
          ~shift:(dec_shift shift)
          ~acc:(acc + ((len - 1) lsl shift)))
;;

let size_sub_trie node ~shift = size_sub_trie (Node node) ~shift ~acc:0

let make_sizes children ~shift =
  let sum = ref 0 in
  let len = Array.length children in
  let table = Size_table.create len in
  let child_shift = dec_shift shift in
  for i = 0 to len - 1 do
    sum := !sum + size_sub_trie children.(i) ~shift:child_shift;
    table.sizes.(i) <- !sum
  done;
  table
;;

let concat left right =
  if left.cnt = 0
  then right
  else if right.cnt = 0
  then left
  else (
    match right.root with
    | Leaf _ as l when phys_equal l empty_leaf ->
      let cnt = left.cnt + right.cnt in
      if left.tail_len = rrb_branching
      then
        push_down_tail
          (left, { left with cnt };
           right.tail)
      else if left.tail_len + right.tail_len <= rrb_branching
      then
        { left with
          cnt
        ; tail_len = left.tail_len + right.tail_len
        ; tail = leaf_node_merge left.tail right.tail
        }
      else (
        let right_cut = rrb_branching - left.tail_len in
        let new_tail_len = right.tail_len - right_cut in
        assert (new_tail_len > 0);
        let elt = right.tail.&(right_cut) in
        let push_down =
          leaf
            ~len:rrb_branching
            (append_part_exn
               (leaf_children left.tail)
               (leaf_children right.tail)
               ~left_len:left.tail_len
               ~len:rrb_branching)
        in
        let new_tail =
          leaf
            ~len:new_tail_len
            (Array.sub (leaf_children right.tail) ~pos:right_cut ~len:new_tail_len)
        in
        let new_rrb =
          { cnt
          ; shift = left.shift
          ; tail_len = new_tail_len
          ; tail = new_tail
          ; root = left.root
          }
        in
        let left_imitation = { left with cnt = cnt - new_tail_len } in
        push_down_tail left_imitation new_rrb new_tail)
    | _ ->
      let left = push_down_tail left_imitation new_rrb None in
      let root_candidate =
        concat_sub_tree left.root left.shift right.root right.shift ~is_top:true
      in
      let shift = find_shift root_candidate in
      { cnt = left.cnt + right.cnt
      ; shift
      ; root = set_sizes root_candidate ~shift
      ; tail = right.tail
      ; tail_len = right.tail_len
      })
;;
