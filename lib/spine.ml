open! Core

module With = struct
  module Let_syntax = struct
    module Let_syntax = struct
      let bind t ~f = t f
    end
  end
end

type elt = Btree.elt [@@deriving sexp_of]
type 'a btree = 'a Btree.node [@@deriving sexp_of]

type 'a dim = 'a Btree.Dim.t = private
  | One : int -> elt btree dim
  | S : int * 'a btree dim -> 'a btree btree dim

let max_width = Btree.max_width
let cols = Btree.Dim.cols
let next = Btree.Dim.next
let[@inline] ( .+() ) a (i, dim) = Btree.get a i ~dim
let[@inline] ( .+()<- ) a (i, dim) x = Btree.set a i x ~dim
let ( -$ ) x y = if x >= y then Some (x - y) else None

(* TODO: store pre/pre+data/total lengths instead of pre/data/suff *)
type _ t =
  | Base : 'data btree -> 'data btree t
  | Spine :
      { size : int
      ; prefix : 'data
      ; data : 'data btree t
      ; suffix : 'data
      }
      -> 'data t

let rec sexp_of_t : 'arr. ('arr -> Sexp.t) -> 'arr t -> Sexp.t =
  fun (type arr) (sexp_of_arr : arr -> Sexp.t) (t : arr t) : Sexp.t ->
   match t with
   | Base data -> [%sexp (data : arr)]
   | Spine { size; prefix; suffix; data } ->
     [%sexp { size : int; prefix : arr; data : arr btree t; suffix : arr }]
;;

type spine = Sp : 'a btree dim * 'a btree t -> spine

let rec sexp_of_spine (Sp (dim, t)) =
  match t with
  | Base data -> [%sexp Base (Btree (dim, data) : Btree.btree)]
  | Spine { size; prefix; suffix; data } ->
    [%sexp
      Spine
        { size : int
        ; prefix = (Btree (dim, prefix) : Btree.btree)
        ; data = (Sp (next dim, data) : spine)
        ; suffix = (Btree (dim, suffix) : Btree.btree)
        }]
;;

let empty = Base Btree.empty

let length (type a) (t : a t) =
  match t with
  | Base b -> b.size
  | Spine s -> s.size
;;

let rec invariant : 'a. 'a btree t -> dim:'a btree dim -> unit =
  fun (type a) (t : a btree t) ~(dim : a btree dim) : unit ->
   Invariant.invariant
     [%here]
     (Sp (dim, t))
     [%sexp_of: spine]
     (fun () ->
       match t with
       | Base tree -> Btree.invariant tree ~dim
       | Spine { size; prefix; data; suffix } ->
         Btree.invariant prefix ~dim;
         invariant data ~dim:(next dim);
         Btree.invariant suffix ~dim;
         [%test_result: int]
           size
           ~expect:(Btree.length prefix + length data + Btree.length suffix))
;;

let show_in_backtrace name here ts dim f =
  try
    let t = f () in
    invariant t ~dim;
    t
  with
  | exn ->
    let ts = List.map ts ~f:(fun t -> Sp (dim, t)) in
    let name = sprintf !"%s[%{Source_code_position}]" name here in
    raise_s [%sexp (name : string), (ts : spine list), "raised", (exn : Exn.t)]
;;

let spine ~prefix ~data ~suffix =
  let size = Btree.length prefix + length data + Btree.length suffix in
  Spine { size; prefix; data; suffix }
;;

let rec get : 'a. 'a btree t -> int -> dim:'a btree dim -> elt =
  fun (type a) (t : a btree t) (i : int) ~(dim : a btree dim) : elt ->
   Exn.reraise_uncaught (sprintf "get %d" i) (fun () ->
     match t with
     | Base b -> Btree.get b i ~dim
     | Spine s ->
       let prefix_len = Btree.length s.prefix in
       (match i -$ prefix_len with
        | None -> s.prefix.+(i, dim)
        | Some i ->
          let data_len = s.size - prefix_len - Btree.length s.suffix in
          Exn.reraise_uncaught (sprintf "get data %d" i) (fun () ->
            match i -$ data_len with
            | None -> get s.data i ~dim:(next dim)
            | Some i ->
              Exn.reraise_uncaught (sprintf "get suffix %d" i) (fun () ->
                s.suffix.+(i, dim)))))
;;

let rec set : 'a. 'a btree t -> int -> elt -> dim:'a btree dim -> 'a btree t =
  fun (type a) (t : a btree t) (i : int) (elt : elt) ~(dim : a btree dim) : a btree t ->
   match t with
   | Base b -> Base (Btree.set b i elt ~dim)
   | Spine s ->
     let prefix_len = Btree.length s.prefix in
     (match i -$ prefix_len with
      | None -> Spine { s with prefix = s.prefix.+(i, dim) <- elt }
      | Some i ->
        let data_len = s.size - prefix_len - Btree.length s.suffix in
        (match i -$ data_len with
         | None -> Spine { s with data = set s.data i elt ~dim:(next dim) }
         | Some i -> Spine { s with suffix = s.suffix.+(i, dim) <- elt }))
;;

let rec map : 'a. 'a btree t -> f:(elt -> elt) -> dim:'a btree dim -> 'a btree t =
  fun (type a) (t : a btree t) ~(f : elt -> elt) ~(dim : a btree dim) : a btree t ->
   match t with
   | Base b -> if Btree.length b = 0 then t else Base (Btree.map b ~f ~dim)
   | Spine { size; prefix; data; suffix } ->
     Spine
       { size
       ; prefix = Btree.map prefix ~f ~dim
       ; data = map data ~f ~dim:(next dim)
       ; suffix = Btree.map suffix ~f ~dim
       }
;;

let rec cons : 'a. 'a -> 'a btree t -> dim:'a btree dim -> 'a btree t =
  fun (type a) (elt : a) (t : a btree t) ~(dim : a btree dim) : a btree t ->
   (* let%bind.With () = show_in_backtrace "cons" [%here] [ t ] dim in *)
   let size =
     length t
     +
     match dim with
     | One _ -> 1
     | S (_, _) -> Btree.length elt
   in
   match t with
   | Base data ->
     (match Btree.cons elt data ~fill:`Split ~dim with
      | First data -> Base data
      | Second (x, y) -> Spine { prefix = x; data = empty; suffix = y; size })
     (* if Array.length data.storage < max_width - 2 *)
     (* then ( *)
     (*   let data =  in *)
     (*   Base data) *)
     (* else *)
     (*   (\* TODO: should this really be in suffix? why not data? *\) *)
     (*   Spine { prefix = Btree.singleton elt ~dim; data = empty; suffix = data; size } *)
   | Spine s ->
     (* if Array.length s.prefix.storage < max_width *)
     (* then ( *)
     (*   let prefix = Btree.cons elt s.prefix ~dim in *)
     (*   Spine { s with size; prefix }) *)
     (* else ( *)
     (*   let prefix = Btree.singleton elt ~dim in *)
     (*   Spine *)
     (*     { prefix; data = cons s.prefix s.data ~dim:(next dim); suffix = s.suffix; size }) *)
     (match Btree.cons elt s.prefix ~fill:`Right ~dim with
      | First prefix -> Spine { size; prefix; data = s.data; suffix = s.suffix }
      | Second (prefix, lhs) ->
        Spine { prefix; data = cons lhs s.data ~dim:(next dim); suffix = s.suffix; size })
;;

let rec snoc : 'a. 'a btree t -> 'a -> dim:'a btree dim -> 'a btree t =
  fun (type a) (t : a btree t) (elt : a) ~(dim : a btree dim) : a btree t ->
   (* let%bind.With () = show_in_backtrace "snoc" [%here] [ t ] dim in *)
   let size =
     length t
     +
     match dim with
     | One _ -> 1
     | S (_, _) -> Btree.length elt
   in
   match t with
   | Base data ->
     (* if Array.length data.storage < max_width - 2 *)
     (* then Base (Btree.snoc data elt ~dim) *)
     (* else ( *)
     (*   (\* TODO: should this really be in suffix? why not data? *\) *)
     (*   let suffix = Btree.singleton elt ~dim in *)
     (*   Spine { prefix = data; data = empty; suffix; size }) *)
     (match Btree.snoc data elt ~fill:`Split ~dim with
      | First data -> Base data
      | Second (prefix, suffix) -> Spine { size; prefix; suffix; data = empty })
   | Spine s ->
     (* if Array.length s.suffix.storage < max_width *)
     (* then ( *)
     (*   let suffix = Btree.snoc s.suffix elt ~dim in *)
     (*   Spine { s with size; suffix }) *)
     (* else ( *)
     (*   let suffix = Btree.singleton elt ~dim in *)
     (*   Spine *)
     (*     { prefix = s.prefix; data = snoc s.data s.suffix ~dim:(next dim); suffix; size }) *)
     (match Btree.snoc s.suffix elt ~fill:`Right ~dim with
      | First suffix -> Spine { size; prefix = s.prefix; data = s.data; suffix }
      | Second (rhs, suffix) ->
        Spine { prefix = s.prefix; data = snoc s.data rhs ~dim:(next dim); suffix; size })
;;

let rec append : 'a. 'a btree t -> 'a btree t -> dim:'a btree dim -> 'a btree t =
  fun (type a) (t1 : a btree t) (t2 : a btree t) ~(dim : a btree dim) : a btree t ->
   (* let%bind.With () = show_in_backtrace "append" [%here] [ t1; t2 ] dim in *)
   if am_running_test
   then (
     invariant t1 ~dim;
     invariant t2 ~dim);
   let size = length t1 + length t2 in
   match t1, t2 with
   | Base b1, Base b2 ->
     (match Btree.append b1 b2 ~fill:`Split ~dim with
      | First b -> Base b
      | Second (prefix, suffix) -> Spine { size; prefix; data = empty; suffix })
   | Base b1, Spine s2 ->
     (match Btree.append b1 s2.prefix ~fill:`Right ~dim with
      | First prefix -> Spine { s2 with size; prefix }
      | Second (prefix, lhs) ->
        Spine
          { size; prefix; data = cons lhs s2.data ~dim:(next dim); suffix = s2.suffix })
   | Spine s1, Base b2 ->
     (match Btree.append s1.suffix b2 ~fill:`Left ~dim with
      | First suffix -> Spine { s1 with size; suffix }
      | Second (rhs, suffix) ->
        Spine
          { size; prefix = s1.prefix; data = snoc s1.data rhs ~dim:(next dim); suffix })
   | Spine s1, Spine s2 ->
     (* TODO: special cases *)
     let data =
       match Btree.append s1.suffix s2.prefix ~fill:`Right ~dim, next dim with
       | First mid, dim -> append (snoc s1.data mid ~dim) s2.data ~dim
       | Second (lhs, rhs), dim ->
         append (snoc s1.data lhs ~dim) (cons rhs s2.data ~dim) ~dim
     in
     if am_running_test then invariant data ~dim:(next dim);
     Spine { size; prefix = s1.prefix; data; suffix = s2.suffix }
;;

(* let rec rev : 'a. 'a btree t -> dim:'a btree dim -> 'a btree t = *)
(*   fun (type a) (t : a btree t) ~(dim : a btree dim) : a btree t -> *)
(*    match t with *)
(*    | Base b -> if b.len = 0 then t else Base { b with data = Btree.rev b.data ~dim } *)
(*    | Spine { prefix_len; prefix; data_len; data; suffix_len; suffix } -> *)
(*      Spine *)
(*        { prefix_len = suffix_len *)
(*        ; prefix = Btree.rev suffix ~dim *)
(*        ; data_len *)
(*        ; data = rev data ~dim:(next dim) *)
(*        ; suffix_len = prefix_len *)
(*        ; suffix = Btree.rev prefix ~dim *)
(*        } *)
(* ;; *)

let rec fold_left :
          'a 'acc.
          'a btree t -> init:'acc -> f:('acc -> elt -> 'acc) -> dim:'a btree dim -> 'acc
  =
  fun (type a acc)
      (t : a btree t)
      ~(init : acc)
      ~(f : acc -> elt -> acc)
      ~(dim : a btree dim)
    : acc ->
   match t with
   | Base b -> Btree.fold_left b ~init ~f ~dim
   | Spine s ->
     let init = Btree.fold_left s.prefix ~init ~f ~dim in
     let init = fold_left s.data ~init ~f ~dim:(next dim) in
     Btree.fold_left s.suffix ~init ~f ~dim
;;

let rec fold_right :
          'a 'acc.
          'a btree t -> init:'acc -> f:(elt -> 'acc -> 'acc) -> dim:'a btree dim -> 'acc
  =
  fun (type a acc)
      (t : a btree t)
      ~(init : acc)
      ~(f : elt -> acc -> acc)
      ~(dim : a btree dim)
    : acc ->
   match t with
   | Base b -> Btree.fold_right b ~init ~f ~dim
   | Spine s ->
     let init = Btree.fold_right s.suffix ~init ~f ~dim in
     let init = fold_right s.data ~init ~f ~dim:(next dim) in
     Btree.fold_right s.prefix ~init ~f ~dim
;;

(* module To_btree = struct *)
(*   let[@inline] blit_helper ~src_len ~src_pos ~(dst : elt btree) ~dst_pos ~len ~blit ~next = *)
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
(*             src:'a btree t *)
(*             -> src_pos:int *)
(*             -> dst:elt btree *)
(*             -> dst_pos:int *)
(*             -> len:int *)
(*             -> dim:'a btree dim *)
(*             -> unit *)
(*     = *)
(*     fun (type a) *)
(*         ~(src : a btree t) *)
(*         ~src_pos *)
(*         ~(dst : elt btree) *)
(*         ~dst_pos *)
(*         ~len *)
(*         ~(dim : a btree dim) *)
(*       : unit -> *)
(*      match src with *)
(*      | Base b -> *)
(*        Btree.To_btree.unchecked_blit ~src:b.data ~src_pos ~dst ~dst_pos ~len ~dim *)
(*      | Spine s -> *)
(*        blit_helper *)
(*          ~src_len:s.prefix_len *)
(*          ~src_pos *)
(*          ~dst *)
(*          ~dst_pos *)
(*          ~len *)
(*          ~blit:(Btree.To_btree.unchecked_blit ~src:s.prefix ~dim) *)
(*          ~next: *)
(*            (blit_helper *)
(*               ~src_len:s.data_len *)
(*               ~blit:(unchecked_blit ~src:s.data ~dim:(next dim)) *)
(*               ~next: *)
(*                 (blit_helper *)
(*                    ~src_len:s.suffix_len *)
(*                    ~blit:(Btree.To_btree.unchecked_blit ~src:s.suffix ~dim) *)
(*                    ~next:(fun ~src_pos:_ ~dst:_ ~dst_pos:_ ~len:_ -> ()))) *)
(*   ;; *)
(* end *)

(* TODO: re-implement this *)
module Builder = struct
  type nonrec t = Builder of elt btree t [@@unboxed]
  type one = One

  let empty = Builder empty
  let of_spine t ~dim:One = Builder t
  let to_spine (Builder t) ~dim:One = t
  let add (Builder t) elt ~dim:One = Builder (snoc t elt ~dim:Btree.Dim.one)
  let add_arr t other ~dim:One = Array.fold other ~init:t ~f:(add ~dim:One)

  let add_spine t other ~dim:One =
    fold_left other ~init:t ~f:(add ~dim:One) ~dim:Btree.Dim.one
  ;;
end

module To_array = struct
  let unchecked_blit ~src ~src_pos ~dst ~dst_pos ~len ~dim =
    let l = fold_right src ~init:[] ~f:List.cons ~dim in
    let a = Array.of_list l in
    Array.blit ~src:a ~src_pos ~dst ~dst_pos ~len
  ;;
end

module Builder2 = struct
  type 'a imm_spine = 'a t

  type 'a tree =
    { mutable size : int
    ; mutable width : int
    ; storage : 'a array
    }

  type ('a, 'b) dim =
    | One : (elt tree, elt btree) dim
    | S : ('a tree, 'b btree) dim -> ('a tree tree, 'b btree btree) dim

  type _ spine =
    | Base : 'data tree -> 'data tree spine
    | Spine :
        { mutable size : int
        ; mutable prefix : 'data
        ; mutable data : 'data tree spine
        ; mutable suffix : 'data
        }
        -> 'data spine

  let empty = Obj.magic (Base { size = 0; width = 0; storage = [||] })
  let empty_tree = Obj.magic { size = 0; width = 0; storage = [||] }

  let singleton (type a b) (elt : a) ~(dim : (a tree, b) dim) =
    let size =
      match dim with
      | One -> 1
      | S _ -> elt.size
    in
    { size; width = 1; storage = Array.create elt ~len:max_width }
  ;;

  let sub (type a b) (src : a array) ~pos ~len ~(dim : (a, b) dim) =
    let size =
      match dim with
      | One -> len
      | S _ ->
        let size = ref 0 in
        for i = 0 to len - 1 do
          size := !size + src.(pos + i).size
        done;
        !size
    in
    let storage =
      if pos = 0 && len = max_width
      then src
      else if len = 0
      then [||]
      else (
        let dst = Array.create src.(0) ~len:max_width in
        Array.blit ~src ~dst ~src_pos:pos ~dst_pos:1 ~len:(len - 1);
        dst)
    in
    { size; width = len; storage }
  ;;

  type 'a t = 'a tree spine

  let try_snoc (type a b) (b : a tree) (elt : a) ~(dim : (a tree, b) dim) =
    let elt_size =
      match dim with
      | One -> 1
      | S _ -> elt.size
    in
    if Array.length b.storage < max_width
    then (
      let storage = Array.create elt ~len:max_width in
      Array.blito ~src:b.storage ~dst:storage ~src_len:b.width ();
      Some { size = b.size + elt_size; width = b.width; storage })
    else if b.width < max_width
    then (
      b.size <- b.size + elt_size;
      b.storage.(b.width) <- elt;
      b.width <- b.width + 1;
      Some b)
    else None
  ;;

  let try_extend
    (type a b)
    (b : a tree)
    (src : a array)
    ~pos
    ~len
    ~(dim : (a tree, b) dim)
    =
    let[@local] extend dst =
      let remaining_space = b.width - max_width in
      let added = min len remaining_space in
      let size =
        match dim with
        | One ->
          Array.blit ~src ~src_pos:pos ~dst:dst.storage ~dst_pos:b.width ~len:added;
          b.size + added
        | S _ ->
          let size = ref b.size in
          for i = 0 to added - 1 do
            let elt = src.(pos + i) in
            size := !size + elt.size;
            dst.storage.(b.width + i) <- elt
          done;
          !size
      in
      dst.size <- size;
      dst.width <- b.width + added;
      dst, added
    in
    if b.width = max_width
    then b, 0
    else if Array.length b.storage = max_width
    then extend b
    else (
      let dst = Array.create (Obj.magic 0) ~len:max_width in
      Array.blito ~src:b.storage ~dst ~src_len:b.width ();
      extend { b with storage = dst })
  ;;

  let rec add : 'a 'b. 'a t -> 'a -> dim:('a tree, 'b btree) dim -> 'a t =
    fun (type a b) (t : a t) (elt : a) ~(dim : (a tree, b btree) dim) : a t ->
     match t with
     | Base (b : a tree) ->
       (match try_snoc b elt ~dim with
        | Some b -> Base b
        | None ->
          let suffix = singleton elt ~dim in
          Spine { size = b.size + suffix.size; prefix = b; data = empty; suffix })
     | Spine s ->
       let () =
         match try_snoc s.suffix elt ~dim with
         | Some b -> s.suffix <- b
         | None ->
           s.data <- add s.data s.suffix ~dim:(S dim);
           s.suffix <- singleton elt ~dim
       in
       t
  ;;

  let rec to_btree : 'a 'b. 'a tree -> dim:('a tree, 'b btree) dim -> 'b btree =
    fun (type a b) ({ size; width; storage } : a tree) ~(dim : (a tree, b btree) dim)
      : b btree ->
     match dim with
     | One -> { size; width; storage }
     | S dim ->
       if width = 0
       then Btree.empty
       else (
         let dst = Array.create (Obj.magic 0) ~len:width in
         for i = 0 to width - 1 do
           let b = to_btree storage.(i) ~dim in
           dst.(i) <- b
         done;
         { size; width; storage = dst })
  ;;

  let rec to_spine : 'a 'b. 'a t -> dim:('a tree, 'b btree) dim -> 'b btree imm_spine =
    fun (type a b) (t : a t) ~(dim : (a tree, b btree) dim) : b btree imm_spine ->
     match t with
     | Base data -> Base (to_btree data ~dim)
     | Spine { prefix; data; suffix; size } ->
       Spine
         { size
         ; prefix = to_btree prefix ~dim
         ; data = to_spine data ~dim:(S dim)
         ; suffix = to_btree suffix ~dim
         }
  ;;

  let rec add_arr :
            'a 'b.
            'a t -> 'a array -> pos:int -> len:int -> dim:('a tree, 'b btree) dim -> 'a t
    =
    fun (type a b) (t : a t) (a : a array) ~pos ~len ~(dim : (a tree, b btree) dim) : a t ->
     if len = 0
     then t
     else (
       match t with
       | Base b ->
         let b, added = try_extend b a ~pos ~len ~dim in
         let pos = pos + added
         and len = len - added in
         if len = 0
         then Base b
         else (
           let t =
             Spine { prefix = b; data = empty; suffix = empty_tree; size = b.size }
           in
           add_arr t a ~pos ~len ~dim)
       | Spine s ->
         let suffix, added = try_extend s.suffix a ~pos ~len ~dim in
         let pos = pos + added
         and len = len - added in
         s.size <- s.size - s.suffix.size + suffix.size;
         s.suffix <- suffix;
         if len = 0
         then t
         else (
           s.data <- add s.data s.suffix ~dim:(S dim);
           s.suffix <- empty_tree;
           add_arr t a ~pos ~len ~dim))
  ;;

  external tree_of_btree : 'a btree -> 'a tree = "%opaque"

  (* let rec of_spine : 'a 'b. 'a btree imm_spine -> dim:'a btree dim -> 'a btree btree = *)
  (*   fun (type a) (btree : a btree imm_spine) ~(dim : a btree dim) : a btree btree -> *)
  (*    match btree with *)
  (*    | Base b -> *)
  (*      (match Array.length b.data with *)
  (*       | 0 -> Empty *)
  (*       | len -> Base { len; data = extend_nonempty b.data ~len:(max_width - 2) }) *)
  (*    | Spine { prefix; data; suffix; _ } -> *)
  (*      Spine *)
  (*        { prefix = tree_of_btree prefix *)
  (*        ; data = of_spine data ~dim:(next dim) *)
  (*        ; suffix_len = Array.length suffix *)
  (*        ; suffix = tree_of_btree suffix *)
  (*        } *)
  (* ;; *)

  let[@inline] add_arr btree a ~dim : _ t =
    add_arr btree a ~pos:0 ~len:(Array.length a) ~dim
  ;;

  (* let rec add_btree : 'a 'b. 'a t -> 'b btree -> dim:('a tree, 'b btree) dim -> 'a t = *)
  (*   fun (type a b) (t : a t) (b : b btree) ~(dim : (a tree, b btree) dim) : a t -> *)
  (*    match dim with *)
  (*    | One -> add_arr t b.storage ~dim *)
  (*    | S dim -> *)
  (*      (\* match  *\) *)
  (*      Array.fold b.storage ~init:t ~f:(fun t b -> add_btree t b ~dim) *)
  (* ;; *)

  (* let rec add_multi_btree : 'a. 'a tree -> 'a btree -> dim:'a btree dim -> t = *)
  (*   fun (type a) (t : t) (arr : a btree) ~(dim : a btree dim) : t -> *)
  (*    match dim with *)
  (*    | S (_, Z) -> add_arr t arr *)
  (*    | S (_, (S _ as dim)) -> *)
  (*      Array.fold arr ~init:t ~f:(fun btree arr -> add_multi_btree btree arr ~dim) *)
  (* ;; *)

  (* let rec add_spine : 'a. t -> 'a btree spine -> dim:'a btree dim -> t = *)
  (*   fun (type a) (t : t) (spine : a btree spine) ~(dim : a btree dim) : t -> *)
  (*    match spine with *)
  (*    | Base b -> add_multi_btree t b.data ~dim *)
  (*    | Spine s -> *)
  (*      let t = add_multi_btree t s.prefix ~dim in *)
  (*      let t = add_spine t s.data ~dim:(next dim) in *)
  (*      add_multi_btree t s.suffix ~dim *)
  (* ;; *)

  (* (\* TODO: allow specifying pos/len (for better [sub] implementation) *\) *)
  (* let add_spine t spine ~dim = *)
  (*   match t with *)
  (*   | Empty -> of_spine spine ~dim *)
  (*   | t -> if phys_equal spine empty then t else add_spine t spine ~dim *)
  (* ;; *)
end
