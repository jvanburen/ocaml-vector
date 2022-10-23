open! Core

let rrb_bits = 5
let rrb_branching = 1 lsl rrb_bits
let rrb_mask = rrb_branching - 1
let rrb_invariant = 1
let rrb_extras = 2
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

type z = Z
type 'n s = S : 'n -> 'n s
type one = z s

type (_, _, _) node =
  | Leaf :
      { len : int
      ; id : Id.t
      ; child : 'a array (* TODO: uniform array *)
      }
      -> ('a, 'a, z) node
  | Internal :
      { len : int
      ; id : Id.t
      ; child : ('a, 'b, 'n) node array
      ; size_table : Size_table.t option
      }
      -> ('a, ('a, 'b, 'n) node, 'n s) node

type (_, _, _) node_property =
  | Len : (_, _, int) node_property
  | Id : (_, _, Id.t) node_property
  | Child : ('a, _, 'a array) node_property
  | Size_table : (_, _ s, Size_table.t option) node_property

let len (type a b c) (node : (a, b, c) node) =
  match node with
  | Leaf leaf -> leaf.len
  | Internal node -> node.len
;;

let id (type a b c) (node : (a, b, c) node) =
  match node with
  | Leaf leaf -> leaf.id
  | Internal node -> node.id
;;

let children (type a b c) (node : (a, b, c) node) : b array =
  match node with
  | Leaf leaf -> leaf.child
  | Internal node -> node.child
;;

let child node i = (children node).(i)
let last_child node = child node (len node - 1)
let size_table (Internal node) = node.size_table

let ( .&() ) (type a b c d) (node : (a, b, c) node) (prop : (b, c, d) node_property) : d =
  match prop with
  | Len -> len node
  | Id -> id node
  | Child -> children node
  | Size_table ->
    (match node with
     | Internal node -> node.size_table)
;;

module Shift : sig
  type (_, _, _) t = private
    | Leaf : unit -> ('a, 'a, z) t
    | Internal :
        { bits : int
        ; child_shift : ('a, 'b, 'c) t
        }
        -> ('a, ('a, 'b, 'c) node, 'c s) t

  type (_, _, _, _, _, _, _) max =
    | Eq : ('a, 'b, 'c, 'b, 'c, 'b, 'c) max
    | Gt :
        ('a, 'lb, 'lc, 'rb, 'rc, 'lb, 'lc) max
        -> ('a, ('a, 'lb, 'lc) node, 'lc s, 'rb, 'rc, ('a, 'lb, 'lc) node, 'lc s) max
    | Lt :
        ('a, 'lb, 'lc, 'rb, 'rc, 'rb, 'rc) max
        -> ('a, 'lb, 'lc, ('a, 'rb, 'rc) node, 'rc s, ('a, 'rb, 'rc) node, 'rc s) max

  type (_, _, _, _, _) packed_max =
    | Max : ('a, 'lb, 'lc, 'rb, 'rc, _, _) max -> ('a, 'lb, 'lc, 'rb, 'rc) packed_max

  val cmp
    : 'a
    'lb
    'lc
    'rb
    'rc.
    ('a, 'lb, 'lc) t -> ('a, 'rb, 'rc) t -> ('a, 'lb, 'lc, 'rb, 'rc) packed_max

  val bits : _ t -> int
  val parent : ('a, 'b, 'c) t -> ('a, ('a, 'b, 'c) node, 'c s) t
  val child : ('a, ('a, 'b, 'c) node, 'c s) t -> ('a, 'b, 'c) t
  val leaf : ('a, 'a, z) t
  val one : ('a, ('a, 'a, z) node, one) t

  type ('a, 'b, 'c) internal = ('a, ('a, 'b, 'c) node, 'c s) t
end = struct
  type (_, _, _) t =
    | Leaf : unit -> ('a, 'a, z) t
    | Internal :
        { bits : int
        ; child_shift : ('a, 'b, 'c) t
        }
        -> ('a, ('a, 'b, 'c) node, 'c s) t

  type (_, _, _, _, _, _, _) max =
    | Eq : ('a, 'b, 'c, 'b, 'c, 'b, 'c) max
    | Gt :
        ('a, 'lb, 'lc, 'rb, 'rc, 'lb, 'lc) max
        -> ('a, ('a, 'lb, 'lc) node, 'lc s, 'rb, 'rc, ('a, 'lb, 'lc) node, 'lc s) max
    | Lt :
        ('a, 'lb, 'lc, 'rb, 'rc, 'rb, 'rc) max
        -> ('a, 'lb, 'lc, ('a, 'rb, 'rc) node, 'rc s, ('a, 'rb, 'rc) node, 'rc s) max

  type (_, _, _, _, _) packed_max =
    | Max : ('a, 'lb, 'lc, 'rb, 'rc, _, _) max -> ('a, 'lb, 'lc, 'rb, 'rc) packed_max

  let rec max_succ
    : type a lb lc rb rc ob oc.
      (a, lb, lc, rb, rc, ob, oc) max
      -> (a, (a, lb, lc) node, lc s, (a, rb, rc) node, rc s, (a, ob, oc) node, oc s) max
    = function
    | Eq -> Eq
    | Gt max -> Gt (max_succ max)
    | Lt max -> Lt (max_succ max)
  ;;

  let rec gt : type a b c. (a, b, c) t -> (a, b, c, a, z, b, c) max = function
    | Leaf () -> Eq
    | Internal { bits = _; child_shift } -> Gt (gt child_shift)
  ;;

  let rec lt : type a b c. (a, b, c) t -> (a, a, z, b, c, b, c) max = function
    | Leaf () -> Eq
    | Internal { bits = _; child_shift } -> Lt (lt child_shift)
  ;;

  let rec cmp
    : type a lb lc rb rc. (a, lb, lc) t -> (a, rb, rc) t -> (a, lb, lc, rb, rc) packed_max
    =
   fun t1 t2 ->
    match t1, t2 with
    | t1, Leaf () -> Max (gt t1)
    | Leaf (), t2 -> Max (lt t2)
    | Internal { bits = _; child_shift = t1 }, Internal { bits = _; child_shift = t2 } ->
      let (Max max) = cmp t1 t2 in
      Max (max_succ max)
 ;;

  let bits (type a b c) (t : (a, b, c) t) : int =
    match t with
    | Leaf () -> 0
    | Internal { bits; child_shift = _ } -> bits
  ;;

  let parent (type a b c) (t : (a, b, c) t) : (a, (a, b, c) node, c s) t =
    Internal { bits = rrb_bits + bits t; child_shift = t }
  ;;

  let leaf = Leaf ()
  let one = Internal { bits = rrb_bits; child_shift = Leaf () }
  let child (Internal { bits = _; child_shift }) = child_shift

  type nonrec ('a, 'b, 'c) internal = ('a, ('a, 'b, 'c) node, 'c s) t
end

module Tree_node = struct
  type 'a t = Node : ('a, 'b, 'c) node * ('a, 'b, 'c) Shift.t -> 'a t

  let bits (type a) (Node (_, shift) : a t) = Shift.bits shift

  let is_empty (type a) (Node (node, shift) : a t) =
    match shift with
    | Leaf () -> len node = 0
    | Internal _ ->
      assert (len node > 0);
      false
  ;;
end

type size_table = Size_table.t =
  { id : Id.t
  ; sizes : int array
  }

type ('a, 'b, 'c) shift = ('a, 'b, 'c) Shift.t = private
  | Leaf : unit -> ('a, 'a, z) shift
  | Internal :
      { bits : int
      ; child_shift : ('a, 'b, 'c) shift
      }
      -> ('a, ('a, 'b, 'c) node, 'c s) shift

type 'a tree_node = 'a Tree_node.t =
  | Node : ('a, 'b, 'c) node * ('a, 'b, 'c) Shift.t -> 'a tree_node

let rec size_sub_trie
  : type a b c. (a, b, c) node -> shift:(a, b, c) Shift.t -> acc:int -> int
  =
 fun node ~shift ~acc ->
  match shift, node with
  | Leaf (), Leaf { len; _ } -> len
  | Internal { bits; child_shift }, Internal { size_table; len; child; _ } ->
    (match size_table with
     | Some table -> table.sizes.(len - 1)
     | None ->
       size_sub_trie child.(len - 1) ~shift:child_shift ~acc:(acc + ((len - 1) lsl bits)))
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

module Leaf = struct
  type 'a t = ('a, 'a, z) node

  let create child ~len : _ node =
    assert (len = Array.length child);
    Leaf { len; id = Id.create (); child }
  ;;

  let merge
    (Leaf { child = left_child; len = left_len; _ } : 'a t)
    (Leaf { child = right_child; len = right_len; _ } : 'a t)
    : 'a t
    =
    create (Array.append left_child right_child) ~len:(left_len + right_len)
  ;;
end

module Internal = struct
  type ('a, 'b, 'c) t = ('a, ('a, 'b, 'c) node, 'c s) node

  let create ~with_sizes child ~len : _ t =
    assert (len = Array.length child);
    Internal
      { len
      ; id = Id.create ()
      ; child
      ; size_table =
          (match with_sizes with
           | None -> None
           | Some shift -> Some (make_sizes child ~shift))
      }
  ;;

  let singleton child = create [| child |] ~len:1
  let pair left right = create [| left; right |] ~len:2
  let empty_id = Id.create ()

  (** sentinel for [merge] *)
  let none : _ node = Internal { len = 1; id = empty_id; child = [||]; size_table = None }

  let merge
    (type a b c)
    ~with_sizes
    (Internal { len = left_len; child = left_child; _ } : (a, b, c) t)
    (Internal { len = center_len; child = center_child; _ } as center : (a, b, c) t)
    (Internal { len = right_len; child = right_child; _ } : (a, b, c) t)
    =
    let left_len = left_len - 1 in
    let right_len = right_len - 1 in
    assert (not (phys_equal center none));
    let len = left_len + center_len + right_len in
    let child = Array.create center_child.(0) ~len in
    Array.blit ~src:left_child ~src_pos:0 ~dst:child ~dst_pos:0 ~len:left_len;
    Array.blit ~src:center_child ~src_pos:0 ~dst:child ~dst_pos:left_len ~len:center_len;
    Array.blit
      ~src:right_child
      ~src_pos:0
      ~dst:child
      ~dst_pos:(left_len + center_len)
      ~len:right_len;
    create ~with_sizes child ~len
  ;;

  (* TODO: optimize computing with_sizes? *)
  let sub ~with_sizes t ~pos ~len =
    create ~with_sizes ~len (Array.sub (children t) ~pos ~len)
  ;;
end

type 'a t =
  { cnt : int
  ; tail_len : int
  ; tail : 'a Leaf.t
  ; root : 'a tree_node
  }

let tail_id = Id.create ()
let empty_leaf : _ Leaf.t = Leaf { len = 0; id = tail_id; child = [||] }

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

let create_concat_plan (Internal _ as all : _ node) =
  let node_count = Array.map (children all) ~f:len in
  let total_nodes = Array.sum (module Int) node_count ~f:Fn.id in
  let optimal_slots = ((total_nodes - 1) / rrb_branching) + 1 in
  let shuffled_len = ref (len all) in
  let i = ref 0 in
  while optimal_slots + rrb_extras < !shuffled_len do
    while node_count.(!i) > rrb_branching - rrb_invariant do
      incr i
    done;
    let remaining_nodes = ref node_count.(!i) in
    let min_size = Int.min rrb_branching (!remaining_nodes + node_count.(!i + 1)) in
    remaining_nodes := !remaining_nodes + node_count.(!i + 1) - min_size;
    incr i;
    while !remaining_nodes > 0 do
      let min_size = Int.min rrb_branching (!remaining_nodes + node_count.(!i + 1)) in
      remaining_nodes := !remaining_nodes + node_count.(!i + 1) - min_size;
      incr i
    done;
    Array.blit
      ~src:node_count
      ~src_pos:(!i + 1)
      ~dst:node_count
      ~dst_pos:!i
      ~len:(!shuffled_len - 1);
    decr shuffled_len;
    decr i
  done;
  node_count, !shuffled_len
;;

let execute_concat_plan
  (type a b c)
  (all : (a, b, c) Internal.t)
  ~node_size
  ~slen
  ~(shift : (a, b, c) Shift.internal)
  ~with_sizes
  : (a, b, c) Internal.t
  =
  let children : (a, b, c) node array =
    match Shift.child shift with
    | Internal _ as child_shift ->
      let idx = ref 0 in
      let offset = ref 0 in
      Array.map node_size ~f:(fun new_size ->
        let old = child all !idx in
        if !offset = 0 && new_size = len old
        then (
          incr idx;
          old)
        else (
          let dst = Array.create (child old 0) ~len:new_size in
          let cur_size = ref 0 in
          while !cur_size < new_size do
            assert (!idx < len all);
            let old = child all !idx in
            let remaining_in_dst = new_size - !cur_size in
            let remaining_in_old = len old - !offset in
            let copied = Int.min remaining_in_dst remaining_in_old in
            Array.blit
              ~src:(children old)
              ~src_pos:!offset
              ~dst
              ~dst_pos:!cur_size
              ~len:copied;
            cur_size := !cur_size + copied;
            if remaining_in_dst >= remaining_in_old
            then (
              incr idx;
              offset := 0)
            else offset := !offset + copied
          done;
          Internal.create dst ~len:new_size ~with_sizes:(Some child_shift)))
    | Leaf () ->
      let idx = ref 0 in
      let offset = ref 0 in
      Array.map node_size ~f:(fun new_size ->
        let old : b Leaf.t = child all !idx in
        if !offset = 0 && new_size = len old
        then (
          incr idx;
          old)
        else (
          let dst = Array.create (child old 0) ~len:new_size in
          let cur_size = ref 0 in
          while !cur_size < new_size do
            assert (!idx < len all);
            let old = child all !idx in
            let remaining_in_dst = new_size - !cur_size in
            let remaining_in_old = len old - !offset in
            let copied = Int.min remaining_in_dst remaining_in_old in
            Array.blit
              ~src:(children old)
              ~src_pos:!offset
              ~dst
              ~dst_pos:!cur_size
              ~len:copied;
            cur_size := !cur_size + copied;
            if remaining_in_dst >= remaining_in_old
            then (
              incr idx;
              offset := 0)
            else offset := !offset + copied
          done;
          Leaf { len = new_size; id = Id.create (); child = dst }))
  in
  Internal.create children ~len:slen ~with_sizes:(Option.some_if with_sizes shift)
;;

type (_, _, _, _) is_top =
  | Top : ('a, 'b, 'c, (('a, 'b, 'c) node, ('a, 'b, 'c) Internal.t) Either.t) is_top
  | Not_top : ('a, 'b, 'c, ('a, 'b, 'c) Internal.t) is_top

let rebalance
  (type a b c d)
  (left : (a, (a, b, c) node, c s) node)
  (center : (a, (a, b, c) node, c s) node)
  (right : (a, (a, b, c) node, c s) node)
  ~(shift : (a, (a, b, c) node, c s) Shift.t)
  ~(is_top : (a, (a, b, c) node, c s, d) is_top)
  : d
  =
  let all = Internal.merge left center right ~with_sizes:None in
  let node_count, top_len = create_concat_plan all in
  let new_all =
    execute_concat_plan
      all
      ~node_size:node_count
      ~slen:top_len
      ~shift
      ~with_sizes:
        (top_len <= rrb_branching
        &&
        match is_top with
        | Top -> false
        | Not_top -> true)
  in
  let split () =
    let left = Internal.sub new_all ~pos:0 ~len:rrb_branching ~with_sizes:(Some shift) in
    let right =
      Internal.sub
        new_all
        ~pos:rrb_branching
        ~len:(top_len - rrb_branching)
        ~with_sizes:(Some shift)
    in
    Internal.pair left right ~with_sizes:None
  in
  match is_top with
  | Not_top ->
    if top_len <= rrb_branching
    then Internal.singleton new_all ~with_sizes:(Some (Shift.parent shift))
    else split ()
  | Top -> if top_len <= rrb_branching then First new_all else Second (split ())
;;

let rec concat_sub_tree_eq
  : type a b c d.
    (a, b, c) node
    -> (a, b, c) node
    -> shift:(a, b, c) Shift.t
    -> is_top:(a, b, c, d) is_top
    -> d
  =
 fun left right ~shift ~is_top ->
  match shift with
  | Internal { bits = _; child_shift } as shift ->
    let center =
      concat_sub_tree_eq
        (last_child left)
        (child right 0)
        ~shift:child_shift
        ~is_top:Not_top
    in
    rebalance left center right ~shift ~is_top
  | Leaf () ->
    (match is_top with
     | Not_top -> Internal.pair left right ~with_sizes:(Some (Shift.parent shift))
     | Top ->
       if len left + len right <= rrb_branching
       then First (Leaf.merge left right)
       else Second (Internal.pair left right ~with_sizes:(Some (Shift.parent shift))))
;;

let rec concat_sub_tree
  : type a lb lc rb rc b c d.
    (a, lb, lc) node
    -> (a, lb, lc) shift
    -> (a, rb, rc) node
    -> (a, rb, rc) shift
    -> (a, lb, lc, rb, rc, b, c) Shift.max
    -> is_top:(a, b, c, d) is_top
    -> d
  =
 fun left left_shift right right_shift max ~is_top ->
  match max with
  | Eq -> concat_sub_tree_eq left right ~shift:left_shift ~is_top
  | Gt max ->
    let center : (a, _, _) Internal.t =
      concat_sub_tree
        (last_child left)
        (Shift.child left_shift)
        right
        right_shift
        max
        ~is_top:Not_top
    in
    rebalance left center Internal.none ~shift:left_shift ~is_top
  | Lt max ->
    let center =
      concat_sub_tree
        left
        left_shift
        (child right 0)
        (Shift.child right_shift)
        max
        ~is_top:Not_top
    in
    rebalance Internal.none center right ~shift:right_shift ~is_top
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
