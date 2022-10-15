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

module Leaf = struct
  type 'a t =
    { len : int
    ; id : Id.t
    ; child : 'a array (* TODO: uniform array *)
    }

  let create child ~len =
    assert (len = Array.length child);
    { len; id = Id.create (); child }
  ;;

  let merge left right =
    create (Array.append left.child right.child) ~len:(left.len + right.len)
  ;;
end

module Internal = struct
  type 'a t =
    { len : int
    ; id : Id.t
    ; child : 'a array (* TODO: uniform array *)
    ; size_table : Size_table.t option
    }

  let create child ~len =
    assert (len = Array.length child);
    { len; id = Id.create (); child; size_table = None }
  ;;

  let singleton child = create [| child |] ~len:1
  let pair left right = create [| left; right |] ~len:2
  let empty_id = Id.create ()

  (** sentinel for [merge] *)
  let empty = { len = 1; id = empty_id; child = [||]; size_table = None }

  let merge left center right =
    assert (not (phys_equal center empty));
    let left_len = left.len - 1 in
    let right_len = right.len - 1 in
    let len = left_len + center.len + right_len in
    let child = Array.create center.child.(0) ~len in
    Array.blit ~src:left.child ~src_pos:0 ~dst:child ~dst_pos:0 ~len:left_len;
    Array.blit ~src:center.child ~src_pos:0 ~dst:child ~dst_pos:left_len ~len:center.len;
    Array.blit
      ~src:right.child
      ~src_pos:0
      ~dst:child
      ~dst_pos:(left_len + center.len)
      ~len:right_len;
    create child ~len
  ;;
end

type 'a leaf_node = 'a Leaf.t =
  { len : int
  ; id : Id.t
  ; child : 'a array (* TODO: uniform array *)
  }

type 'a internal_node = 'a Internal.t =
  { len : int
  ; id : Id.t
  ; child : 'a array (* TODO: uniform array *)
  ; size_table : Size_table.t option
  }

module Shift : sig
  type (_, _) t = private
    | Leaf : unit -> ('a, 'a leaf_node) t
    | Internal :
        { bits : int
        ; child_shift : ('a, 'b) t
        }
        -> ('a, 'b internal_node) t

  (* type (_, _, _) diff = private *)
  (*   | Same : ('a, 'b) t -> ('a, 'b, 'b) diff *)
  (*   | Left_higher : *)
  (*       { left : ('a, 'l internal_node) t *)
  (*       ; right : ('a, 'r) t *)
  (*       ; child_diff : ('a, 'l, 'r) diff *)
  (*       } *)
  (*       -> ('a, 'l internal_node, 'r) diff *)
  (*   | Right_higher : *)
  (*       { left : ('a, 'l) t *)
  (*       ; right : ('a, 'r internal_node) t *)
  (*       ; child_diff : ('a, 'l, 'r) diff *)
  (*       } *)
  (*       -> ('a, 'l, 'r internal_node) diff *)

  type ('a, 'l, 'r) eq =
    | Lt : ('a, 'l, _ internal_node) eq
    | Gt : ('a, _ internal_node, 'r) eq
    | Eq : ('a, 'b) t -> ('a, 'b, 'b) eq

  val eq : ('a, 'l) t -> ('a, 'r) t -> ('a, 'l, 'r) eq
  val bits : _ t -> int
  val parent : ('a, 'b) t -> ('a, 'b internal_node) t
  val child : ('a, 'b internal_node) t -> ('a, 'b) t
  val leaf : ('a, 'a leaf_node) t
  val one : ('a, 'a leaf_node internal_node) t
end = struct
  type (_, _) t =
    | Leaf : unit -> ('a, 'a leaf_node) t
    | Internal :
        { bits : int
        ; child_shift : ('a, 'b) t
        }
        -> ('a, 'b internal_node) t

  (* type (_, _, _) geq = *)
  (*   | Eq : ('a, 'b, 'b) geq *)
  (*   | Gt : ('a, 'l, 'r) geq -> ('a, 'l internal_node, 'r) geq *)

  (* type (_, _, _) cmp = *)
  (*   | Eq : ('a, 'b, 'b) cmp *)
  (*   | Gt : ('a, 'l, 'r) geq -> ('a, 'l, 'r) cmp *)
  (*   | Lt : ('a, 'r, 'l) geq -> ('a, 'l, 'r) cmp *)

  (* type (_, _, _) diff = *)
  (*   | Same : ('a, 'b) t -> ('a, 'b, 'b) diff *)
  (*   | Left_higher : *)
  (*       { left : ('a, 'l internal_node) t *)
  (*       ; child_diff : ('a, 'l, 'r) diff *)
  (*       } *)
  (*       -> ('a, 'l internal_node, 'r) diff *)
  (*   | Right_higher : *)
  (*       { right : ('a, 'r internal_node) t *)
  (*       ; child_diff : ('a, 'l, 'r) diff *)
  (*       } *)
  (*       -> ('a, 'l, 'r internal_node) diff *)

  external unit_to_zero : unit -> int = "%identity"

  let bits (type a b) (t : (a, b) t) : int =
    match t with
    | Leaf bits -> unit_to_zero bits
    | Internal { bits; child_shift = _ } -> bits
  ;;

  let parent (type a b) (t : (a, b) t) : (a, b internal_node) t =
    Internal { bits = rrb_bits + bits t; child_shift = t }
  ;;

  type ('a, 'l, 'r) eq =
    | Lt : ('a, 'l, _ internal_node) eq
    | Gt : ('a, _ internal_node, 'r) eq
    | Eq : ('a, 'b) t -> ('a, 'b, 'b) eq

  let eq (type a l r) (left : (a, l) t) (right : (a, r) t) : (a, l, r) eq =
    match Ordering.of_int (compare (bits left) (bits right)) with
    | Equal -> Obj.magic (Eq left)
    | Greater -> Obj.magic Gt
    | Less -> Obj.magic Lt
  ;;

  (* let rec diff : 'a 'l 'r. ('a, 'l) t -> ('a, 'r) t -> ('a, 'l, 'r) diff = *)
  (*   fun (type a l r) (left : (a, l) t) (right : (a, r) t) : (a, l, r) diff -> *)
  (*    match left, right with *)
  (*    | Leaf (), Leaf () -> Same (Leaf ()) *)
  (*    | (Internal { bits = _; child_shift = left_child } as left), Leaf () -> *)
  (*      Left_higher { left; child_diff = diff left_child right } *)
  (*    | Leaf (), (Internal { bits = _; child_shift = right_child } as right) -> *)
  (*      Right_higher { right; child_diff = diff left right_child } *)
  (*    | ( (Internal { bits = _; child_shift = left_child } as left) *)
  (*      , (Internal { bits = _; child_shift = right_child } as right) ) -> *)
  (*      (match diff left_child right_child with *)
  (*       | Left_higher { left; _ } as child_diff -> *)
  (*         Left_higher { left = parent left; child_diff } *)
  (*       | Right_higher _ as child_diff -> Right_higher { right; child_diff }) *)
  (* ;; *)

  let parent (type a b) (t : (a, b) t) : (a, b internal_node) t =
    Internal { bits = rrb_bits + bits t; child_shift = t }
  ;;

  let leaf = Leaf ()
  let one = Internal { bits = rrb_bits; child_shift = Leaf () }
  let child (Internal { bits = _; child_shift }) = child_shift
end

module Tree_node = struct
  type 'a t = Node : 'node * ('a, 'node) Shift.t -> 'a t

  let bits (type a) (Node (_, shift) : a t) = Shift.bits shift

  let is_empty (type a) (Node (node, shift) : a t) =
    match shift with
    | Leaf () -> node.len = 0
    | Internal _ -> false
  ;;
end

type size_table = Size_table.t =
  { id : Id.t
  ; sizes : int array
  }

type ('a, 'b) shift = ('a, 'b) Shift.t = private
  | Leaf : unit -> ('a, 'a leaf_node) shift
  | Internal :
      { bits : int
      ; child_shift : ('a, 'b) shift
      }
      -> ('a, 'b internal_node) shift

type 'a tree_node = 'a Tree_node.t = Node : 'node * ('a, 'node) Shift.t -> 'a tree_node

type 'a t =
  { cnt : int
  ; tail_len : int
  ; tail : 'a leaf_node
  ; root : 'a tree_node
  }

let tail_id = Id.create ()
let empty_leaf = { len = 0; id = tail_id; child = [||] }

let empty =
  { cnt = 0; root = Node (empty_leaf, Shift.leaf); tail_len = 0; tail = empty_leaf }
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

let rec size_sub_trie : 'a 'node. 'node -> shift:('a, 'node) Shift.t -> acc:int -> int =
  fun (type a node) (node : node) ~(shift : (a, node) shift) ~(acc : int) ->
   match shift with
   | Leaf () -> node.len
   | Internal { bits; child_shift } ->
     let len = node.len in
     (match node.size_table with
      | Some table -> table.sizes.(len - 1)
      | None ->
        size_sub_trie
          node.child.(len - 1)
          ~shift:child_shift
          ~acc:(acc + ((len - 1) lsl bits)))
;;

let size_sub_trie node ~shift = size_sub_trie node ~shift ~acc:0

let make_sizes children ~shift:(Internal { bits = _; child_shift }) =
  let sum = ref 0 in
  let len = Array.length children in
  let table = Size_table.create len in
  for i = 0 to len - 1 do
    sum := !sum + size_sub_trie children.(i) ~shift:child_shift;
    table.sizes.(i) <- !sum
  done;
  table
;;

let rebalance
  (type a b)
  (_ : b Internal.t)
  (_ : b Internal.t)
  (_ : b Internal.t)
  ~shift:(_ : (a, b Internal.t) Shift.t)
  ~is_top:(_ : bool)
  : b Internal.t
  =
  assert false
;;

let rec concat_sub_tree
  : type a. a Tree_node.t -> a Tree_node.t -> is_top:bool -> a Tree_node.t
  =
  fun (type a)
      (Node (left, left_shift) as left_node : a Tree_node.t)
      (Node (right, right_shift) as right_node : a Tree_node.t)
      ~is_top
    : a Tree_node.t ->
   match Shift.eq left_shift right_shift with
   | Eq (Leaf ()) ->
     let node =
       if is_top && left.len + right.len <= rrb_branching
       then Internal.singleton (Leaf.merge left right)
       else Internal.pair left right
     in
     Node (node, Shift.one)
   | Eq (Internal { bits = _; child_shift } as shift) ->
     let center =
       concat_sub_tree
         (Node (left.child.(left.len - 1), child_shift))
         (Node (right.child.(0), child_shift))
         ~is_top:false
     in
     rebalance left center right ~shift ~is_top
   | Gt ->
     let center =
       concat_sub_tree
         (Node (left.child.(left.len - 1), Shift.child left_shift))
         right_node
         ~is_top:false
     in
     rebalance left center None ~shift:left_shift ~is_top
   | Lt ->
     let center =
       concat_sub_tree
         left_node
         (Node (right.child.(0), Shift.child right_shift))
         ~is_top:false
     in
     rebalance None center right ~shift:right_shift ~is_top
;;

let concat left right =
  if left.cnt = 0
  then right
  else if right.cnt = 0
  then left
  else if not (Tree_node.is_empty right.root)
  then (
    let left = push_down_tail left { left with cnt = left.cnt } None in
    { cnt = left.cnt + right.cnt
    ; root = concat_sub_tree left.root right.root ~is_top:true
    ; tail = right.tail
    ; tail_len = right.tail_len
    })
  else (
    let cnt = left.cnt + right.cnt in
    if left.tail_len = rrb_branching
    then push_down_tail left { left with cnt } right.tail
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
      let push_down =
        Leaf.create
          ~len:rrb_branching
          (append_part_exn
             left.tail.child
             right.tail.child
             ~left_len:left.tail_len
             ~len:rrb_branching)
      in
      let new_tail =
        Leaf.create
          ~len:new_tail_len
          (Array.sub right.tail.child ~pos:right_cut ~len:new_tail_len)
      in
      let new_rrb =
        { cnt; tail_len = new_tail_len; tail = push_down; root = left.root }
      in
      push_down_tail { left with cnt = cnt - new_tail_len } new_rrb new_tail))
;;
