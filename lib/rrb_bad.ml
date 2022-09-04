type elt = private Block of Obj.t
type arr1 = elt array
type arr2 = elt array array
type arr3 = elt array array array

type bigvector =
  { prefix1 : elt array
  ; suffix1 : elt array
  ; length0 : int
  }

let bits = 5
let width = 1 lsl bits
let mask = width - 1
let bits2 = bits * 2
let width2 = 1 lsl bits2
let bits3 = bits * 3
let width3 = 1 lsl bits3

(* // compile-time numeric constants
   final val BITS = 5
   final val WIDTH = 1 << BITS
   final val MASK = WIDTH - 1
   final val BITS2 = BITS * 2
   final val WIDTH2 = 1 << BITS2
   final val BITS3 = BITS * 3
   final val WIDTH3 = 1 << BITS3
   final val BITS4 = BITS * 4
   final val WIDTH4 = 1 << BITS4
   final val BITS5 = BITS * 5
   final val WIDTH5 = 1 << BITS5
   final val BITS6 = BITS * 6
   final val WIDTH6 = 1 << BITS6
   final val LASTWIDTH = WIDTH << 1 // 1 extra bit in the last level to go up to Int.MaxValue (2^31-1) instead of 2^30:
   final val Log2ConcatFaster = 5

   type Arr1 = Array[AnyRef]
   type Arr2 = Array[Array[AnyRef]]
   type Arr3 = Array[Array[Array[AnyRef]]]
   type Arr4 = Array[Array[Array[Array[AnyRef]]]]
   type Arr5 = Array[Array[Array[Array[Array[AnyRef]]]]]
   type Arr6 = Array[Array[Array[Array[Array[Array[AnyRef]]]]]] *)

let arrset a i x =
  let dst = Array.copy a in
  dst.(i) <- x;
  dst
;;

type _ depth =
  | Flat : elt array depth
  | Nested : int * 'a depth -> 'a array depth

type spine =
  | Base of arr1
  | Spine of
      { len : int
      ; prefix : arr1
      ; suffix : arr1
      ; data : spine
      }

type _ spine1 =
  | Base : 'a -> 'a spine1
  | Spine :
      { len : int
      ; prefix : 'data array
      ; suffix : 'data array
      ; data : 'data array spine1
      }
      -> 'data spine1

let rec get_index : 'a. 'a depth -> int -> int =
  fun (type a) (depth : a depth) i ->
   match depth with
   | Flat -> i land mask
   | Nested (_, depth) -> get_index depth (i lsr bits)
;;

let rec get_multi : 'a. 'a depth -> 'a -> int -> elt =
  fun (type a) (depth : a depth) (a : a) i ->
   match depth with
   | Flat -> a.(i)
   | Nested (_, d) -> get_multi d a.(get_index depth i) i
;;

type t =
  | Empty of unit
  | One of { prefix1 : elt array }
  | Two of
      { prefix1 : arr1
      ; len1 : int
      ; data2 : arr2
      ; suffix1 : arr1
      ; length0 : int
      }

let[@inline never] ioob () = invalid_arg "index out of bounds"

let length (t : spine) =
  match t with
  | Base a -> Array.length a
  | Spine s -> s.len
;;

let ( -$ ) x y = if x >= y then Some (x - y) else None

let rec get (t : spine) i =
  match t with
  | Base a -> a.(i)
  | Spine { len = _; prefix; suffix; data } ->
    (match i -$ Array.length prefix with
     | None -> prefix.(i)
     | Some i ->
       (match i -$ length data with
        | None -> get data i
        | Some i -> suffix.(i)))
;;

(* let rec set (t : spine) i x = *)
(*   match t with *)
(*   | Base a -> Base (arrset a i x) *)
(*   | Spine ({ len = _; prefix; suffix; data } as s) -> *)
(*     (match i -$ Array.length prefix with *)
(*      | None -> Spine { s with prefix = arrset prefix i x } *)
(*      | Some i -> *)
(*        (match i -$ length data with *)
(*         | None -> Spine { s with data = set data i x } *)
(*         | Some i -> Spine { s with suffix = arrset suffix i x })) *)
(* ;; *)

(* let get t i =  *)
(*   match t with   *)
(*   | Empty () -> ioob () *)
(*   | One {prefix1} ->  prefix1.(i) *)
(*   | Two {prefix1; len1; data2; suffix1; length0} -> *)
(*     if not (i >= 0 && i <= length0) then ioob (); *)
(*     let io = i - len1 in *)
(*     if io >= 0 then *)
(*       let i2 = io asr bits in  *)
(*       let i1 = io land mask in *)
(*       if i2 < Array.length data2 then data2.(i2).(i1) *)
(*       else suffix1.(io land mask)  *)
(*     else prefix1.(i) *)
(*     (\* if(index >= 0 && index < length0) { *)
(*       val io = index - len1 *)
(*       if(io >= 0) { *)
(*         val i2 = io >>> BITS *)
(*         val i1 = io & MASK *)
(*         if(i2 < data2.length) data2(i2)(i1) *)
(*         else suffix1(io & MASK) *)
(*       } else prefix1(index) *)
(*     }.asInstanceOf[A] else throw ioob(index) *\) *)

(* override def updated[B >: A](index: Int, elem: B): Vector[B] = {
     if(index >= 0 && index < length0) {
       if(index >= len12) {
         val io = index - len12
         val i3 = io >>> BITS2
         val i2 = (io >>> BITS) & MASK
         val i1 = io & MASK
         if     (i3 < data3.length  ) copy(data3   = copyUpdate(data3, i3, i2, i1, elem))
         else if(i2 < suffix2.length) copy(suffix2 = copyUpdate(suffix2, i2, i1, elem))
         else                         copy(suffix1 = copyUpdate(suffix1, i1, elem))
       } else if(index >= len1) {
         val io = index - len1
         copy(prefix2 = copyUpdate(prefix2, io >>> BITS, io & MASK, elem))
       } else {
         copy(prefix1 = copyUpdate(prefix1, index, elem))
       }
     } else throw ioob(index)
   } *)

(* let set t i x =  *)
(*   match t with  *)
(*   |Empty () -> ioob() *)
(*   | Two {prefix1; len1; data2; suffix1; length0} -> *)
