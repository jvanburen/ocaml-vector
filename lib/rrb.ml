open! Core
open! Expect_test_helpers_core

let max_search_error = 2
let max_width = 3
let rrb_branching = max_width

let%test "max_width" = max_width >= 2
let%test "max_search_error" = max_search_error < max_width

(* let rrb_bits = 5 *)
(* let rrb_branching = 1 lsl rrb_bits *)
(* let rrb_mask = rrb_branching - 1 *)
let rrb_invariant = 1
let rrb_extras = max_search_error

module Size_table = struct
  type t = { sizes : int array } [@@deriving sexp_of]

  let create len = { sizes = Array.create ~len 0 }
  let clone t = { sizes = Array.copy t.sizes }

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
      ; child : 'a array (* TODO: uniform array *)
      }
      -> ('a, 'a, z) node
  | Internal :
      { len : int
      ; child : ('a, 'b, 'n) node array
      ; size_table : Size_table.t option
      }
      -> ('a, ('a, 'b, 'n) node, 'n s) node

type (_, _, _) node_property =
  | Len : (_, _, int) node_property
  | Child : ('a, _, 'a array) node_property
  | Size_table : (_, _ s, Size_table.t option) node_property

let len (type a b c) (node : (a, b, c) node) =
  match node with
  | Leaf leaf -> leaf.len
  | Internal node -> node.len
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
  | Child -> children node
  | Size_table ->
    (match node with
     | Internal node -> node.size_table)
;;

module Shift : sig
  type (_, _, _) level =
    | Leaf : ('a, 'a, z) level
    | Internal : ('a, ('a, 'b, 'c) node, 'c s) level

  (* TODO: make this opaque and just expose a [level] GADT that says leaf or internal *)
  type (_, _, _) t

  val level : ('a, 'b, 'c) t -> ('a, 'b, 'c) level

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

  val expected_child_index : _ internal -> int -> int
end = struct
  type (_, _, _) level =
    | Leaf : ('a, 'a, z) level
    | Internal : ('a, ('a, 'b, 'c) node, 'c s) level

  type (_, _, _) t =
    | Leaf : unit -> ('a, 'a, z) t
    | Internal :
        { bits : int
        ; child_shift : ('a, 'b, 'c) t
        }
        -> ('a, ('a, 'b, 'c) node, 'c s) t

  let level (type a b c) (t : (a, b, c) t) : (a, b, c) level =
    match t with
    | Leaf () -> Leaf
    | Internal _ -> Internal
  ;;

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
    | Leaf () -> 1
    | Internal { bits; child_shift = _ } -> bits
  ;;

  let parent (type a b c) (t : (a, b, c) t) : (a, (a, b, c) node, c s) t =
    Internal { bits = rrb_branching * bits t; child_shift = t }
  ;;

  let leaf = Leaf ()
  let one = Internal { bits = rrb_branching; child_shift = Leaf () }
  let child (Internal { bits = _; child_shift }) = child_shift

  let expected_child_index (Internal { bits; child_shift = _ }) i =
    assert (bits > 0);
    i / bits mod rrb_branching
  ;;

  type nonrec ('a, 'b, 'c) internal = ('a, ('a, 'b, 'c) node, 'c s) t
end

type size_table = Size_table.t = { sizes : int array }

type ('a, 'b, 'c) level = ('a, 'b, 'c) Shift.level =
  | Leaf : ('a, 'a, z) level
  | Internal : ('a, ('a, 'b, 'c) node, 'c s) level

let rec size_sub_trie
  : type a b c. (a, b, c) node -> shift:(a, b, c) Shift.t -> acc:int -> int
  =
 fun node ~shift ~acc ->
  let len = len node in
  match Shift.level shift with
  | Leaf -> len
  | Internal ->
    (match size_table node with
     | Some table -> table.sizes.(len - 1)
     | None ->
       size_sub_trie
         (child node (len - 1))
         ~shift:(Shift.child shift)
         ~acc:(acc + (rrb_branching * (len - 1))))
;;

let size_sub_trie node ~shift = size_sub_trie node ~shift ~acc:0

let make_sizes children ~shift =
  let sum = ref 0 in
  let len = Array.length children in
  let table = Size_table.create len in
  for i = 0 to len - 1 do
    sum := !sum + size_sub_trie children.(i) ~shift:(Shift.child shift);
    table.sizes.(i) <- !sum
  done;
  table
;;

module Leaf = struct
  type 'a t = ('a, 'a, z) node

  let create child ~len : _ node =
    assert (len = Array.length child);
    Leaf { len; child }
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

  let create ~with_sizes child ~len:n : _ t =
    if true
    then (
      assert (Int.between n ~low:1 ~high:rrb_branching);
      assert (n = Array.length child);
      let needs_sizes =
        Array.existsi child ~f:(fun i c ->
          not (i = Array.length child - 1 || len c = rrb_branching))
      in
      assert (needs_sizes ==> Option.is_some with_sizes));
    Internal
      { len = n
      ; child
      ; size_table =
          (match with_sizes with
           | None -> None
           | Some shift -> Some (make_sizes child ~shift))
      }
  ;;

  let singleton child = create [| child |] ~len:1 ~with_sizes:None
  let pair left right ~with_sizes = create [| left; right |] ~len:2 ~with_sizes

  (** sentinel for [merge] *)
  let none : _ node = Internal { len = 1; child = [||]; size_table = None }

  let merge
    (type a b c)
    (Internal { len = left_len; child = left_child; _ } : (a, b, c) t)
    (Internal { len = center_len; child = center_child; _ } as center : (a, b, c) t)
    (Internal { len = right_len; child = right_child; _ } as right : (a, b, c) t)
    =
    if not (phys_equal right none)
    then [%test_result: int] right_len ~expect:(Array.length right_child);
    let left_len = left_len - 1 in
    let right_len = right_len - 1 in
    assert (not (phys_equal center none));
    let len = left_len + center_len + right_len in
    let child = Array.create center_child.(0) ~len in
    Array.blit ~src:left_child ~src_pos:0 ~dst:child ~dst_pos:0 ~len:left_len;
    Array.blit ~src:center_child ~src_pos:0 ~dst:child ~dst_pos:left_len ~len:center_len;
    if not (phys_equal right none)
    then
      Array.blit
        ~src:right_child
        ~src_pos:1
        ~dst:child
        ~dst_pos:(left_len + center_len)
        ~len:right_len;
    child
  ;;
end

type ('a, 'b, 'c) rrb =
  { cnt : int
  ; root : ('a, 'b, 'c) node
  ; shift : ('a, 'b, 'c) Shift.t
  }

type 'a t = Rrb : ('a, _, _) rrb -> 'a t

module Debug = struct
  type nonrec 'a t = 'a t

  let rec sexp_of_node : type a b c. (a -> Sexp.t) -> (a, b, c) node -> Sexp.t =
   fun sexp_of_a node ->
    match node with
    | Leaf { len = _; child } -> [%sexp Leaf (child : a array)]
    | Internal { len = _; child; size_table } ->
      let child = Array.map child ~f:(sexp_of_node sexp_of_a) in
      [%sexp Internal { size_table : Size_table.t option; child : Sexp.t array }]
 ;;

  let sexp_of_t sexp_of_a (Rrb { cnt; root; shift = _ }) =
    [%sexp { cnt : int; root = (sexp_of_node sexp_of_a root : Sexp.t) }]
  ;;

  module Max = struct
    type t = int

    let zero = 0
    let ( + ) = Int.max
  end

  let rec height : type a b c. (a, b, c) node -> int =
   fun rrb ->
    match rrb with
    | Leaf _ -> 0
    | Internal i -> 1 + Array.sum (module Max) i.child ~f:height
 ;;

  let opt_width (type a b c) (node : (a, b, c) Internal.t) =
    let m = rrb_branching in
    let s =
      Array.sum (module Int) (children node) ~f:(fun node -> Array.length (children node))
    in
    (s + m - 1) / m
  ;;

  let width node = Array.length (children node)

  let rec is_search_step_relaxed : type a b c. (a, b, c) node -> bool =
   fun node ->
    width node <= rrb_branching
    &&
    match node with
    | Leaf _ -> true
    | Internal n as node ->
      width node < opt_width node + rrb_extras
      && Array.for_all n.child ~f:is_search_step_relaxed
 ;;

  let rec count : type a b c. (a, b, c) node -> f:(a -> bool) -> int =
   fun node ~f ->
    match node with
    | Leaf l -> Array.count l.child ~f
    | Internal n -> Array.sum (module Int) n.child ~f:(count ~f)
 ;;

  let invariant (Rrb { cnt; root; shift = _ } as t) =
    Invariant.invariant [%here] t [%sexp_of: _ t] (fun () ->
      [%test_result: int] cnt ~expect:(count root ~f:(Fn.const true));
      assert (is_search_step_relaxed root))
  ;;
end

let empty_leaf : _ Leaf.t = Leaf { len = 0; child = [||] }
let empty = Rrb { cnt = 0; root = empty_leaf; shift = Shift.leaf }
let length (Rrb t) = t.cnt

let rec node_to_list : type a b c. (a, b, c) node -> a list -> a list =
 fun node init ->
  match node with
  | Leaf l -> Array.fold_right l.child ~init ~f:List.cons
  | Internal n -> Array.fold_right n.child ~init ~f:node_to_list
;;

let to_list (Rrb rrb) = node_to_list rrb.root []

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

let create_concat_plan (all : _ node array) =
  let node_count = Array.map all ~f:len in
  let total_nodes = Array.sum (module Int) node_count ~f:Fn.id in
  let optimal_slots = ((total_nodes - 1) / rrb_branching) + 1 in
  let shuffled_len = ref (Array.length all) in
  let i = ref 0 in
  while optimal_slots + rrb_extras < !shuffled_len do
    while node_count.(!i) > rrb_branching - rrb_invariant do
      incr i
    done;
    let remaining_nodes = ref node_count.(!i) in
    let update_remaining_nodes () =
      let min_size = Int.min rrb_branching (!remaining_nodes + node_count.(!i + 1)) in
      node_count.(!i) <- min_size;
      remaining_nodes := !remaining_nodes + node_count.(!i + 1) - min_size;
      incr i
    in
    update_remaining_nodes ();
    while !remaining_nodes > 0 do
      update_remaining_nodes ()
    done;
    Array.blit
      ~src:node_count
      ~src_pos:(!i + 1)
      ~dst:node_count
      ~dst_pos:!i
      ~len:(!shuffled_len - (!i + 1));
    decr shuffled_len;
    decr i
  done;
  let out = Array.subo node_count ~len:!shuffled_len in
  [%test_result: int] (Array.sum (module Int) out ~f:Fn.id) ~expect:total_nodes;
  out
;;

let execute_concat_plan
  (type a b c)
  (all : (a, b, c) node array)
  ~node_size
  ~(shift : (a, b, c) Shift.internal)
  : (a, b, c) node array
  =
  let children : (a, b, c) node array =
    let child_shift = Shift.child shift in
    let idx = ref 0 in
    let offset = ref 0 in
    Array.map node_size ~f:(fun new_size ->
      let old = all.(!idx) in
      if !offset = 0 && new_size = len old
      then (
        incr idx;
        old)
      else (
        let dst = Array.create (child old 0) ~len:new_size in
        let cur_size = ref 0 in
        while !cur_size < new_size do
          let old = all.(!idx) in
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
          if remaining_in_old < remaining_in_dst
          then (
            incr idx;
            offset := 0)
          else offset := !offset + copied
        done;
        match Shift.level child_shift with
        | Internal -> Internal.create dst ~len:new_size ~with_sizes:(Some child_shift)
        | Leaf -> Leaf.create dst ~len:new_size))
  in
  let () =
    let actual = Array.fold_right children ~init:[] ~f:node_to_list in
    let expect = Array.fold_right all ~init:[] ~f:node_to_list in
    try [%test_result: int list] (Obj.magic actual) ~expect:(Obj.magic expect) with
    | exn ->
      let input = Array.map all ~f:(fun n : int list -> Obj.magic node_to_list n []) in
      let output =
        Array.map children ~f:(fun n : int list -> Obj.magic (node_to_list n []))
      in
      raise_s
        [%message
          (input : int list array)
            (output : int list array)
            (node_size : int array)
            (exn : Exn.t)]
  in
  children
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
  let all = Internal.merge left center right in
  let node_count = create_concat_plan all in
  let new_all = execute_concat_plan all ~node_size:node_count ~shift in
  if Array.length new_all <= rrb_branching
  then (
    let t =
      Internal.create new_all ~len:(Array.length new_all) ~with_sizes:(Some shift)
    in
    match is_top with
    | Not_top -> Internal.singleton t
    | Top -> First t)
  else (
    (* TODO: optimize computing with_sizes? *)
    let left =
      Internal.create
        (Array.subo new_all ~len:rrb_branching)
        ~len:rrb_branching
        ~with_sizes:(Some shift)
    in
    let right =
      Internal.create
        (Array.subo new_all ~pos:rrb_branching)
        ~len:(Array.length new_all - rrb_branching)
        ~with_sizes:(Some shift)
    in
    let node = Internal.pair left right ~with_sizes:(Some (Shift.parent shift)) in
    match is_top with
    | Not_top -> node
    | Top -> Second node)
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
  match Shift.level shift with
  | Internal ->
    let center =
      concat_sub_tree_eq
        (last_child left)
        (child right 0)
        ~shift:(Shift.child shift)
        ~is_top:Not_top
    in
    rebalance left center right ~shift ~is_top
  | Leaf ->
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
    -> (a, lb, lc) Shift.t
    -> (a, rb, rc) node
    -> (a, rb, rc) Shift.t
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

let concat_top
  : type a lb lc rb rc b c.
    (a, lb, lc) node
    -> (a, lb, lc) Shift.t
    -> (a, rb, rc) node
    -> (a, rb, rc) Shift.t
    -> (a, lb, lc, rb, rc, b, c) Shift.max
    -> cnt:int
    -> a t
  =
 fun left left_shift right right_shift max ~cnt ->
  let shift : (a, b, c) Shift.t =
    match max with
    | Gt _ -> left_shift
    | Eq -> left_shift
    | Lt _ -> right_shift
  in
  match concat_sub_tree left left_shift right right_shift max ~is_top:Top with
  | First root -> Rrb { cnt; root; shift }
  | Second root -> Rrb { cnt; root; shift = Shift.parent shift }
;;

let concat (Rrb l as left) (Rrb r as right) =
  if length left = 0
  then right
  else if length right = 0
  then left
  else (
    let (Max max) = Shift.cmp l.shift r.shift in
    concat_top l.root l.shift r.root r.shift max ~cnt:(l.cnt + r.cnt))
;;

let rec get : type a b c. (a, b, c) node -> int -> (a, b, c) Shift.t -> a =
 fun node i shift ->
  (* print_s [%sexp Get { i : int; node : _ Debug.node }]; *)
  try
    match Shift.level shift with
    | Leaf ->
      let (Leaf l) = node in
      (* print_s [%sexp Get_leaf, (i mod rrb_branching : int)]; *)
      (try l.child.(i mod rrb_branching) with
       | exn -> raise_s [%sexp (exn : Exn.t), ~~(i : int), (l.len : int)])
    | Internal ->
      let (Internal node) = node in
      let subidx = ref (Shift.expected_child_index shift i) in
      (match node.size_table with
       | None -> get node.child.(!subidx) i (Shift.child shift)
       | Some { sizes } ->
         while sizes.(!subidx) <= i do
           incr subidx
         done;
         let i = if !subidx = 0 then i else i - sizes.(!subidx - 1) in
         get node.child.(!subidx) i (Shift.child shift))
  with
  | exn -> raise_s [%sexp { node : _ Debug.node; i : int; exn : Exn.t }]
;;

let get (Rrb { cnt; root; shift }) i =
  print_endline "";
  (* print_s [%sexp GET { i : int; t : _ Debug.t }]; *)
  if i < 0
  then invalid_arg "Rrb.get: negative index"
  else if i >= cnt
  then invalid_arg "Rrb.get: out-of-bounds index"
  else get root i shift
;;

let rec set
  : type a b c. (a, b, c) node -> int -> a -> (a, b, c) Shift.t -> (a, b, c) node
  =
 fun node i x shift ->
  match Shift.level shift with
  | Leaf ->
    let (Leaf l) = node in
    let i = i mod rrb_branching in
    if phys_equal x l.child.(i)
    then node
    else (
      let child = Array.copy l.child in
      child.(i) <- x;
      Leaf { l with child })
  | Internal ->
    let (Internal n) = node in
    let subidx = ref (Shift.expected_child_index shift i) in
    let child_index, i =
      match size_table node with
      | None -> !subidx, i
      | Some { sizes } ->
        while sizes.(!subidx) <= i do
          incr subidx
        done;
        !subidx, if !subidx = 0 then i else i - sizes.(!subidx - 1)
    in
    let child = n.child.(child_index) in
    let new_child = set child i x (Shift.child shift) in
    if phys_equal child new_child
    then node
    else (
      let child = Array.copy n.child in
      child.(child_index) <- new_child;
      Internal { n with child })
;;

let set (Rrb { cnt; root; shift } as t) i x =
  if i < 0
  then invalid_arg "Rrb.set: negative index"
  else if i >= cnt
  then invalid_arg "Rrb.set: out-of-bounds index"
  else (
    let new_root = set root i x shift in
    if phys_equal root new_root then t else Rrb { cnt; root = new_root; shift })
;;

let singleton x = Rrb { cnt = 1; root = Leaf.create [| x |] ~len:1; shift = Shift.leaf }
let cons x t = concat (singleton x) t
let snoc t x = concat t (singleton x)
let of_list l = List.fold l ~init:empty ~f:snoc

let init n ~f =
  let rec go i t = if i >= n then t else go (i + 1) (snoc t (f i)) in
  go 0 empty
;;

include
  Quickcheckable.Of_quickcheckable1
    (List)
    (struct
      type nonrec 'a t = 'a t

      let to_quickcheckable = to_list
      let of_quickcheckable = of_list
    end)

let%test_module _ =
  (module struct
    let quickcheck_generator =
      let rec go ~size ~random ~start =
        match size with
        | 0 -> empty
        | 1 -> singleton start
        | n ->
          let i = Splittable_random.int random ~lo:1 ~hi:(n - 1) in
          let r2 = Splittable_random.State.split random in
          concat
            (go ~size:i ~random ~start)
            (go ~start:(start + i) ~size:(n - i) ~random:r2)
      in
      Quickcheck.Generator.create (go ~start:1)
    ;;

    let quickcheck_generator_int = Int.gen_incl 0 9

    (* TODO: balancing invariant sometimes fails, is it correct? *)

    let%test_unit "list conversions" =
      for i = 0 to rrb_branching * (rrb_branching + 1) do
        let l = List.init i ~f:succ in
        let t = of_list l in
        (* Debug.invariant t; *)
        try [%test_result: int list] (to_list t) ~expect:l with
        | exn -> raise_s [%sexp (t : int Debug.t), (exn : Exn.t)]
      done
    ;;

    let%test_unit "concat" =
      Quickcheck.test
        [%quickcheck.generator: t * t]
        ~shrinker:[%quickcheck.shrinker: int t * int t]
        ~sexp_of:[%sexp_of: int Debug.t * int Debug.t]
        ~f:(fun (x, y) ->
        let t = concat x y in
        try
          let expect = to_list x @ to_list y in
          [%test_result: int] (length t) ~expect:(List.length expect);
          for i = 0 to length t - 1 do
            Exn.reraise_uncaught (Int.to_string i) (fun () ->
              [%test_result: int] (get t i) ~expect:(List.nth_exn expect i))
          done;
          [%test_result: int list] (to_list t) ~expect
        with
        | exn -> raise_s [%sexp ~~(t : int Debug.t), (exn : Exn.t)])
    ;;

    let%expect_test "get" =
      Quickcheck.test
        [%quickcheck.generator: t]
        ~sexp_of:[%sexp_of: int Debug.t]
        ~f:(fun t ->
        for i = 0 to length t - 1 do
          [%test_result: int] (get t i) ~expect:(i + 1)
        done)
    ;;

    let%test_unit "list conversions" =
      Quickcheck.test
        ~examples:(List.init 10 ~f:(List.init ~f:succ))
        [%quickcheck.generator: int list]
        ~sexp_of:[%sexp_of: int list]
        ~f:(fun l ->
          let t = of_list l in
          (* Debug.invariant t; *)
          try [%test_result: int list] (to_list t) ~expect:l with
          | exn -> raise_s [%sexp (t : int Debug.t), (exn : Exn.t)])
    ;;
  end)
;;
