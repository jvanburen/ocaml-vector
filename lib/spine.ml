open! Core

(* TODO: rename multi_array -> tree *)
module Tree = Multi_array

type elt = Multi_array.elt
type 'a node = 'a Multi_array.node [@@deriving sexp_of]

type 'a dim = 'a Multi_array.Dim.t =
  | One : int -> elt node dim
  | S : int * 'a node dim -> 'a node node dim

let max_width = Multi_array.Dim.max_width
let cols = Multi_array.Dim.cols
let next = Multi_array.Dim.next
let[@inline] ( .+() ) a (i, dim) = Multi_array.get a i ~dim
let[@inline] ( .+()<- ) a (i, dim) x = Multi_array.set a i x ~dim
let ( -$ ) x y = if x >= y then Some (x - y) else None

(* TODO: store pre/pre+data/total lengths instead of pre/data/suff *)
type _ t =
  | Base : 'data node -> 'data node t
  | Spine :
      { prefix_len : int
      ; prefix : 'data
      ; data_len : int
      ; data : 'data node t
      ; suffix_len : int
      ; suffix : 'data
      }
      -> 'data t

let rec sexp_of_t : 'arr. ('arr -> Sexp.t) -> 'arr t -> Sexp.t =
  fun (type arr) (sexp_of_arr : arr -> Sexp.t) (t : arr t) : Sexp.t ->
   match t with
   | Base data -> [%sexp (data : arr)]
   | Spine { prefix_len; data_len; suffix_len; prefix; suffix; data } ->
     [%sexp
       { prefix : arr
       ; prefix_len : int
       ; data : arr node t
       ; data_len : int
       ; suffix : arr
       ; suffix_len : int
       }]
;;

let empty = Base Multi_array.empty

let length (type a) (t : a t) =
  match t with
  | Base b -> b.size
  | Spine s -> s.prefix_len + s.data_len + s.suffix_len
;;

let rec get : 'a. 'a node t -> int -> dim:'a node dim -> elt =
  fun (type a) (t : a node t) (i : int) ~(dim : a node dim) : elt ->
   Exn.reraise_uncaught (sprintf "get %d" i) (fun () ->
     match t with
     | Base b -> Multi_array.get b i ~dim
     | Spine s ->
       (match i -$ s.prefix_len with
        | None -> s.prefix.+(i, dim)
        | Some i ->
          Exn.reraise_uncaught (sprintf "get data %d" i) (fun () ->
            match i -$ s.data_len with
            | None -> get s.data i ~dim:(next dim)
            | Some i ->
              Exn.reraise_uncaught (sprintf "get suffix %d" i) (fun () ->
                s.suffix.+(i, dim)))))
;;

let rec set : 'a. 'a node t -> int -> elt -> dim:'a node dim -> 'a node t =
  fun (type a) (t : a node t) (i : int) (elt : elt) ~(dim : a node dim) : a node t ->
   match t with
   | Base b -> Base (Multi_array.set b i elt ~dim)
   | Spine s ->
     (match i -$ s.prefix_len with
      | None -> Spine { s with prefix = s.prefix.+(i, dim) <- elt }
      | Some i ->
        (match i -$ s.data_len with
         | None -> Spine { s with data = set s.data i elt ~dim:(next dim) }
         | Some i -> Spine { s with suffix = s.suffix.+(i, dim) <- elt }))
;;

let rec cons : 'a. 'a -> 'a node t -> dim:'a node dim -> 'a node t =
  fun (type a) (elt : a) (t : a node t) ~(dim : a node dim) : a node t ->
   match t with
   | Base data ->
     if Array.length data.storage < max_width - 2
     then (
       let data = Multi_array.cons elt data ~dim in
       Base data)
     else
       (* TODO: should this really be in suffix? why not data? *)
       Spine
         { prefix = Multi_array.singleton elt ~dim
         ; prefix_len = cols dim
         ; data = empty
         ; data_len = 0
         ; suffix = data
         ; suffix_len = Multi_array.length data
         }
   | Spine s ->
     if Array.length s.prefix.storage < max_width
     then (
       let prefix = Multi_array.cons elt s.prefix ~dim in
       Spine { s with prefix_len = prefix.size; prefix })
     else (
       let prefix = Multi_array.singleton elt ~dim in
       Spine
         { prefix_len = prefix.size
         ; prefix
         ; data_len = s.prefix_len + s.data_len
         ; data = cons s.prefix s.data ~dim:(next dim)
         ; suffix_len = s.suffix_len
         ; suffix = s.suffix
         })
;;

let rec snoc : 'a. 'a node t -> 'a -> dim:'a node dim -> 'a node t =
  fun (type a) (t : a node t) (elt : a) ~(dim : a node dim) : a node t ->
   match t with
   | Base data ->
     if Array.length data.storage < max_width - 2
     then Base (Multi_array.snoc data elt ~dim)
     else (
       (* TODO: should this really be in suffix? why not data? *)
       let suffix = Multi_array.singleton elt ~dim in
       Spine
         { prefix = data
         ; prefix_len = Multi_array.length data
         ; data = empty
         ; data_len = 0
         ; suffix
         ; suffix_len = suffix.size
         })
   | Spine s ->
     if Array.length s.suffix.storage < max_width
     then (
       let suffix = Multi_array.snoc s.suffix elt ~dim in
       Spine { s with suffix_len = suffix.size; suffix })
     else (
       let suffix = Multi_array.singleton elt ~dim in
       Spine
         { prefix_len = s.prefix_len
         ; prefix = s.prefix
         ; data_len = s.suffix_len + s.data_len
         ; data = snoc s.data s.suffix ~dim:(next dim)
         ; suffix_len = suffix.size
         ; suffix
         })
;;

(* let rec append_tree_widths : 'a. 'a node -> 'a node  -> dim:'a node dim -> 'a node = *)
(*   fun (type a) (t1 : a Tree.wide) (t2 : a Tree.wide) ~(dim : a node dim) : a node -> *)
(*   let w1 = Tree.width t1 *)
(*   and w2 = Tree.width t2 in *)
(*   match dim with *)
(*   | One _ -> *)
(*     let total_width = Tree.width t1 + Tree.width t2 in *)
(*     if total_width <= max_width then [| total_width |] else [| max_width; total_width - max_width|] *)
(*   | Many (_, dim) -> *)
(*     if Array.is_empty t1.storage then t2.prefix_sizes  *)
(*     else if Array.is_empty t2.storage then t1.prefix_sizes else *)
(*       let sizes = Array.create 0 ~len:(w1 + w2) in *)
(*       Array.blito ~src:t1.prefix_sizes ~dst:sizes(); *)
(*       let dst_pos = ref w1 in *)
(*       let last_size = ref (Tree.length t1) in *)
(*       let last_width = ref (Tree.width t1.storage.(Tree.width t1 - 1)) in *)
(*       for i = 0 to Tree.width t2 - 1 do *)
(*         let w = Tree.width t2.storage.(i) in *)
(*         if !last_width + w > max_width then ( *)
(*           sizes.(!dst_pos) <- last_size + *)
(*           last_width := !last_width + w - max_width; *) 
(*         ) *)
(*       done *)

(*       Array.iteri t2.storage ~f:() *)
(*       while !src_pos < Tree.width t2 do *)

(*       let dst = Array.create 0 ~len:() in *)
(*     Array.blito ~src:t1.prefix_sizes ~dst; *)
(*     let last_size = ref (Tree.width t1) in *)
(*     let dst = ref (Tree.width t1) in *)

(*   (\*   let rec append_trees : 'a. 'a node -> 'a node -> dim:'a node dim -> 'a node t = *\) *)
(*   (\* fun (type a) (t1 : a node) (t2 : a node) ~(dim : a node dim) : a node t -> *\) *)
(*   (\* match dim with *\) *)
(*   (\* | One _ -> *\) *)

(* ;; *)

let rec append : 'a. 'a node t -> 'a node t -> dim:'a node dim -> 'a node t =
  fun (type a) (t1 : a node t) (t2 : a node t) ~(dim : a node dim) : a node t ->
   match t1, t2 with
   | Base b1, Base b2 ->
     (match Tree.append b1 b2 ~dim ~max_width with
      | First b -> Base b
      | Second (prefix, suffix) ->
        Spine
          { prefix_len = Tree.length prefix
          ; prefix
          ; data_len = 0
          ; data = empty
          ; suffix
          ; suffix_len = Tree.length suffix
          })
   | Base b1, Spine s2 ->

     (* TODO: make the RHS bigger than the RHS while merging *)
     match Tree.append b1 s2.prefix ~dim  with




;;

let rec map : 'a. 'a node t -> f:(elt -> elt) -> dim:'a node dim -> 'a node t =
  fun (type a) (t : a node t) ~(f : elt -> elt) ~(dim : a node dim) : a node t ->
   match t with
   | Base b -> if Multi_array.length b = 0 then t else Base (Multi_array.map b ~f ~dim)
   | Spine s ->
     let prefix = Multi_array.map s.prefix ~f ~dim in
     let data = map s.data ~f ~dim:(next dim) in
     let suffix = Multi_array.map s.suffix ~f ~dim in
     Spine { s with prefix; data; suffix }
;;

(* let rec rev : 'a. 'a node t -> dim:'a node dim -> 'a node t = *)
(*   fun (type a) (t : a node t) ~(dim : a node dim) : a node t -> *)
(*    match t with *)
(*    | Base b -> if b.len = 0 then t else Base { b with data = Multi_array.rev b.data ~dim } *)
(*    | Spine { prefix_len; prefix; data_len; data; suffix_len; suffix } -> *)
(*      Spine *)
(*        { prefix_len = suffix_len *)
(*        ; prefix = Multi_array.rev suffix ~dim *)
(*        ; data_len *)
(*        ; data = rev data ~dim:(next dim) *)
(*        ; suffix_len = prefix_len *)
(*        ; suffix = Multi_array.rev prefix ~dim *)
(*        } *)
(* ;; *)

let rec fold_left :
          'a 'acc.
          'a node t -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'a node dim -> 'acc
  =
  fun (type a acc)
      (t : a node t)
      ~(init : acc)
      ~(f : acc -> elt -> acc)
      ~(dim : a node dim)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_left b ~init ~f ~dim
   | Spine s ->
     let init = Multi_array.fold_left s.prefix ~init ~f ~dim in
     let init = fold_left s.data ~init ~f ~dim:(next dim) in
     Multi_array.fold_left s.suffix ~init ~f ~dim
;;

let rec fold_right :
          'a 'acc.
          'a node t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'a node dim -> 'acc
  =
  fun (type a acc)
      (t : a node t)
      ~(init : acc)
      ~(f : elt -> acc -> acc)
      ~(dim : a node dim)
    : acc ->
   match t with
   | Base b -> Multi_array.fold_right b ~init ~f ~dim
   | Spine s ->
     let init = Multi_array.fold_right s.suffix ~init ~f ~dim in
     let init = fold_right s.data ~init ~f ~dim:(next dim) in
     Multi_array.fold_right s.prefix ~init ~f ~dim
;;

(* module To_node = struct *)
(*   let[@inline] blit_helper ~src_len ~src_pos ~(dst : elt node) ~dst_pos ~len ~blit ~next = *)
(*     let written_from_src = *)
(*       match src_len -$ src_pos with *)
(*       | None -> 0 *)
(*       | Some src_len -> *)
(*         let len = min len src_len in *)
(*         blit ~src_pos ~dst ~dst_pos ~len; *)
(*         len *)
(*     in *)
(*     let src_pos = max 0 (src_pos - src_len) in *)
(*     let dst_pos = dst_pos + written_from_src in *)
(*     let len = len - written_from_src in *)
(*     if len > 0 then next ~src_pos ~dst ~dst_pos ~len *)
(*   ;; *)

(*   let rec unchecked_blit : *)
(*             'a. *)
(*             src:'a node t *)
(*             -> src_pos:int *)
(*             -> dst:elt node *)
(*             -> dst_pos:int *)
(*             -> len:int *)
(*             -> dim:'a node dim *)
(*             -> unit *)
(*     = *)
(*     fun (type a) *)
(*         ~(src : a node t) *)
(*         ~src_pos *)
(*         ~(dst : elt node) *)
(*         ~dst_pos *)
(*         ~len *)
(*         ~(dim : a node dim) *)
(*       : unit -> *)
(*      match src with *)
(*      | Base b -> *)
(*        Multi_array.To_node.unchecked_blit ~src:b.data ~src_pos ~dst ~dst_pos ~len ~dim *)
(*      | Spine s -> *)
(*        blit_helper *)
(*          ~src_len:s.prefix_len *)
(*          ~src_pos *)
(*          ~dst *)
(*          ~dst_pos *)
(*          ~len *)
(*          ~blit:(Multi_array.To_node.unchecked_blit ~src:s.prefix ~dim) *)
(*          ~next: *)
(*            (blit_helper *)
(*               ~src_len:s.data_len *)
(*               ~blit:(unchecked_blit ~src:s.data ~dim:(next dim)) *)
(*               ~next: *)
(*                 (blit_helper *)
(*                    ~src_len:s.suffix_len *)
(*                    ~blit:(Multi_array.To_node.unchecked_blit ~src:s.suffix ~dim) *)
(*                    ~next:(fun ~src_pos:_ ~dst:_ ~dst_pos:_ ~len:_ -> ()))) *)
(*   ;; *)
(* end *)

let rec actual_len : 'arr. 'arr node t -> dim:'arr node dim -> int =
  fun (type arr) (t : arr node t) ~(dim : arr node dim) : int ->
   match t with
   | Base data -> Multi_array.actual_len data ~dim
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

(* TODO: re-implement this *)
module Builder = struct
  type nonrec t = Builder of elt node t [@@unboxed]

  let empty = Builder empty
  let of_spine t ~dim:_ = Builder t
  let to_spine (Builder t) ~dim:_ = t
  let add (Builder t) elt = Builder (snoc t elt ~dim:Multi_array.Dim.one)
  let add_arr t other = Array.fold other ~init:t ~f:add
  let add_spine t other ~dim = fold_left other ~init:t ~f:add ~dim
end

module To_array = struct
  let unchecked_blit ~src ~src_pos ~dst ~dst_pos ~len ~dim =
    let l = fold_right src ~init:[] ~f:List.cons ~dim in
    let a = Array.of_list l in
    Array.blit ~src:a ~src_pos ~dst ~dst_pos ~len
  ;;
end

(* module Builder = struct *)
(*   type 'a spine = 'a t *)

(*   type _ node = *)
(*     | Empty : _ node *)
(*     | Base : *)
(*         { mutable len : int *)
(*         ; mutable data : 'data Multi_array.node *)
(*         } *)
(*         -> 'data array node *)
(*     | Spine : *)
(*         { mutable prefix_len : int *)
(*         ; mutable prefix : 'data *)
(*         ; mutable data : 'data array node *)
(*         ; mutable suffix_len : int *)
(*         ; mutable suffix : 'data *)
(*         } *)
(*         -> 'data node *)

(*   type t = elt array node *)

(*   let[@inline] trunc a ~len = if len = Array.length a then a else Array.sub a ~pos:0 ~len *)

(*   let[@inline] extend_nonempty src ~len = *)
(*     let src_len = Array.length src in *)
(*     if len = src_len *)
(*     then src *)
(*     else ( *)
(*       let dst = Array.create src.(0) ~len in *)
(*       Array.blit ~src ~src_pos:1 ~dst ~dst_pos:1 ~len:(src_len - 1); *)
(*       dst) *)
(*   ;; *)

(*   let[@inline] set_maybe_extend src i x ~max_len = *)

(*     if i >= max_len *)
(*     then None *)
(*     else *)
(*       Some *)
(*         (let src_len = Array.length src in *)
(*          if i < src_len *)
(*          then ( *)
(*            src.(i) <- x; *)
(*            src) *)
(*          else ( *)
(*            let dst = Array.create x ~len:max_len in *)
(*            Array.blito ~src ~dst (); *)
(*            dst)) *)
(*   ;; *)

(*   let create_empty_node (type t) (t : t) ~(dim : t Multi_array.node dim) *)
(*     : t Multi_array.node *)
(*     = *)
(*     let width = max_width - 2 in *)
(*     match dim with *)
(*     | One _ -> *)
(*       { size = -1 *)
(*       ; prefix_sizes = Array.init width ~f:(fun i -> i) *)
(*       ; storage = Array.create t ~len:width *)
(*       } *)
(*     | S (_, _) -> *)
(*       { size = -1 *)
(*       ; prefix_sizes = Array.init width ~f:(fun i -> i * t.size) *)
(*       ; storage = Array.create t ~len:width *)
(*       } *)
(*   ;; *)

(*   let truncate (type t) (t : t Multi_array.node) ~width = *)
(*     if width = Array.length t.storage *)
(*     then t *)
(*     else *)
(*       { size = t.prefix_sizes.(width) *)
(*       ; prefix_sizes = Array.sub t.prefix_sizes ~pos:0 ~len:width *)
(*       ; storage = Array.sub t.storage ~pos:0 ~len:width *)
(*       } *)
(*   ;; *)

(*   let rec add : 'a. 'a array node -> 'a -> 'a array node = *)
(*     fun (type a) (node : a array node) (elt : a) : a array node -> *)
(*      match node with *)
(*      | Empty -> *)
(*        Base *)
(*          { len = 1 *)
(*          ; data = *)
(*              { size = max_width - 2 *)
(*              ; prefix_sizes = Array.init (max_width - 2) ~f:Fn.id *)
(*              ; storage = Array.create elt ~len:(max_width - 2) *)
(*              } *)
(*          } *)
(*      | Base b -> *)
(*        (match set_maybe_extend b.data b.len elt ~max_len:(max_width - 2) with *)
(*         | Some data -> *)
(*           b.data <- data; *)
(*           b.len <- b.len + 1; *)
(*           node *)
(*         | None -> *)
(*           Spine *)
(*             { prefix = b.data *)
(*             ; prefix_len = b.len *)
(*             ; data = Empty *)
(*             ; suffix = Array.create elt ~len:max_width *)
(*             ; suffix_len = 1 *)
(*             }) *)
(*      | Spine s -> *)
(*        (match set_maybe_extend s.suffix s.suffix_len elt ~max_len:max_width with *)
(*         | Some suffix -> *)
(*           s.suffix <- suffix; *)
(*           s.suffix_len <- s.suffix_len + 1; *)
(*           node *)
(*         | None -> *)
(*           s.data <- add s.data s.suffix; *)
(*           s.suffix <- Array.create elt ~len:max_width; *)
(*           s.suffix_len <- 1; *)
(*           node) *)
(*   ;; *)

(*   let rec add_arr : 'a. 'a array node -> 'a array -> pos:int -> len:int -> 'a array node = *)
(*     (\* TODO: could probably avoid copying some arrays in here in special cases. *\) *)
(*     fun (type a) (node : a array node) (a : a array) ~pos ~len : a array node -> *)
(*      if len = 0 *)
(*      then node *)
(*      else ( *)
(*        match node with *)
(*        | Empty -> *)
(*          let node = Base { len = 1; data = Array.create a.(pos) ~len:(max_width - 2) } in *)
(*          add_arr node a ~pos:(pos + 1) ~len:(len - 1) *)
(*        | Base b -> *)
(*          let added = min len (Array.length b.data - b.len) in *)
(*          Array.blit ~src:a ~src_pos:pos ~dst:b.data ~dst_pos:b.len ~len:added; *)
(*          b.len <- b.len + added; *)
(*          let pos = pos + added *)
(*          and len = len - added in *)
(*          if len = 0 *)
(*          then node *)
(*          else ( *)
(*            let node = *)
(*              Spine *)
(*                { prefix = b.data *)
(*                ; prefix_len = b.len *)
(*                ; data = Empty *)
(*                ; suffix = Array.create a.(pos) ~len:max_width *)
(*                ; suffix_len = 1 *)
(*                } *)
(*            in *)
(*            add_arr node a ~pos:(pos + 1) ~len:(len - 1)) *)
(*        | Spine s -> *)
(*          let added = min len (Array.length s.suffix - s.suffix_len) in *)
(*          Array.blit ~src:a ~src_pos:pos ~dst:s.suffix ~dst_pos:s.suffix_len ~len:added; *)
(*          s.suffix_len <- s.suffix_len + added; *)
(*          let pos = pos + added *)
(*          and len = len - added in *)
(*          if len = 0 *)
(*          then node *)
(*          else ( *)
(*            s.data <- add s.data s.suffix; *)
(*            s.suffix_len <- 1; *)
(*            s.suffix <- Array.create a.(pos) ~len:max_width; *)
(*            add_arr node a ~pos:(pos + 1) ~len:(len - 1))) *)
(*   ;; *)

(*   let rec to_spine : 'a. 'a array node -> dim:'a array dim -> 'a Multi_array.node spine = *)
(*     fun (type a) (node : a array node) ~(dim : a array dim) : a Multi_array.node spine -> *)
(*      match node with *)
(*      | Empty -> empty *)
(*      | Base { len; data } -> Base { len = len * cols dim; data = trunc data ~len } *)
(*      | Spine { prefix_len; prefix; data; suffix_len; suffix } -> *)
(*        let data = to_spine data ~dim:(next dim) in *)
(*        Spine *)
(*          { prefix_len = prefix_len * cols dim *)
(*          ; prefix = trunc prefix ~len:prefix_len *)
(*          ; suffix_len = suffix_len * cols dim *)
(*          ; suffix = trunc suffix ~len:suffix_len *)
(*          ; data *)
(*          ; data_len = length data *)
(*          } *)
(*   ;; *)

(*   let rec of_spine : 'a. 'a node spine -> dim:'a node dim -> 'a node node = *)
(*     fun (type a) (node : a node spine) ~(dim : a node dim) : a node node -> *)
(*      match node with *)
(*      | Base b -> *)
(*        (match Array.length b.data with *)
(*         | 0 -> Empty *)
(*         | len -> Base { len; data = extend_nonempty b.data ~len:(max_width - 2) }) *)
(*      | Spine { prefix; data; suffix; _ } -> *)
(*        Spine *)
(*          { prefix_len = Array.length prefix *)
(*          ; prefix *)
(*          ; data = of_spine data ~dim:(next dim) *)
(*          ; suffix_len = Array.length suffix *)
(*          ; suffix *)
(*          } *)
(*   ;; *)

(*   let[@inline] add_arr node a = add_arr node a ~pos:0 ~len:(Array.length a) *)

(*   let rec add_multi_node : 'a. t -> 'a node -> dim:'a node dim -> t = *)
(*     fun (type a) (t : t) (arr : a node) ~(dim : a node dim) : t -> *)
(*      match dim with *)
(*      | S (_, Z) -> add_arr t arr *)
(*      | S (_, (S _ as dim)) -> *)
(*        Array.fold arr ~init:t ~f:(fun node arr -> add_multi_node node arr ~dim) *)
(*   ;; *)

(*   let rec add_spine : 'a. t -> 'a node spine -> dim:'a node dim -> t = *)
(*     fun (type a) (t : t) (spine : a node spine) ~(dim : a node dim) : t -> *)
(*      match spine with *)
(*      | Base b -> add_multi_node t b.data ~dim *)
(*      | Spine s -> *)
(*        let t = add_multi_node t s.prefix ~dim in *)
(*        let t = add_spine t s.data ~dim:(next dim) in *)
(*        add_multi_node t s.suffix ~dim *)
(*   ;; *)

(*   (\* TODO: allow specifying pos/len (for better [sub] implementation) *\) *)
(*   let add_spine t spine ~dim = *)
(*     match t with *)
(*     | Empty -> of_spine spine ~dim *)
(*     | t -> if phys_equal spine empty then t else add_spine t spine ~dim *)
(*   ;; *)

(*   let empty = Empty *)
(* end *)
