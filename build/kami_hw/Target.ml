
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

(** val add : int -> int -> int **)

let rec add = (+)

(** val tail_add : int -> int -> int **)

let rec tail_add n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n0 -> tail_add n0 (Stdlib.Int.succ m))
    n

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n0 -> tail_addmul (tail_add m r) n0 m)
    n

(** val tail_mul : int -> int -> int **)

let tail_mul n m =
  tail_addmul 0 n m

(** val of_uint_acc : uint -> int -> int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

type t =
| F1 of int
| FS of int * t

type 'a t0 =
| Nil1
| Cons of 'a * int * 'a t0

(** val nth : int -> 'a1 t0 -> t -> 'a1 **)

let rec nth _ v p =
  match v with
  | Nil1 -> assert false (* absurd case *)
  | Cons (x, _, v') ->
    (match p with
     | F1 _ -> x
     | FS (n0, p') -> nth (pred (Stdlib.Int.succ n0)) v' p')

(** val map0 : ('a1 -> 'a2) -> int -> 'a1 t0 -> 'a2 t0 **)

let rec map0 f _ = function
| Nil1 -> Nil1
| Cons (a, n0, v') -> Cons ((f a), n0, (map0 f n0 v'))

(** val ascii_eq : char -> char -> bool **)

let ascii_eq a1 a2 =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b1 b2 b3 b4 b5 b6 b7 b8 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun c1 c2 c3 c4 c5 c6 c7 c8 ->
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&) ((&&) ((&&) (eqb b1 c1) (eqb b2 c2)) (eqb b3 c3))
                (eqb b4 c4)) (eqb b5 c5)) (eqb b6 c6)) (eqb b7 c7))
        (eqb b8 c8))
      a2)
    a1

(** val string_eq : char list -> char list -> bool **)

let rec string_eq s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | a1::s1' ->
    (match s2 with
     | [] -> false
     | a2::s2' -> (&&) (ascii_eq a1 a2) (string_eq s1' s2'))

(** val mod2 : int -> bool **)

let rec mod2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' -> mod2 n')
      n0)
    n

type word =
| WO
| WS of bool * int * word

(** val natToWord : int -> int -> word **)

let rec natToWord sz n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> WO)
    (fun sz' -> WS ((mod2 n), sz', (natToWord sz' (Nat.div2 n))))
    sz

(** val wzero : int -> word **)

let wzero sz =
  natToWord sz 0

type 'a attribute = { attrName : char list; attrType : 'a }

(** val vector_find' : ('a1 -> bool) -> int -> 'a1 t0 -> __ **)

let rec vector_find' f _ = function
| Nil1 -> Obj.magic ()
| Cons (h, n1, t1) ->
  if f h
  then Obj.magic (F1 n1)
  else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (F1 0))
          (fun n2 ->
          Obj.magic (FS ((Stdlib.Int.succ n2),
            (Obj.magic vector_find' f (Stdlib.Int.succ n2) t1))))
          n1)

(** val vector_find : ('a1 -> bool) -> int -> 'a1 t0 -> t **)

let vector_find f n v =
  Obj.magic vector_find' f (Stdlib.Int.succ n) v

type ('a, 'b) ilist =
| Inil
| Icons of 'a * int * 'a t0 * 'b * ('a, 'b) ilist

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

(** val replicate : 'a1 -> int -> 'a1 vec **)

let rec replicate v n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Vec0 v)
    (fun m -> VecNext (m, (replicate v m), (replicate v m)))
    n

type kind =
| Bool
| Bit of int
| Vector of kind * int
| Struct of int * kind attribute t0
| Array of kind * int

type fullKind =
| SyntaxKind of kind
| NativeKind of __

type constT =
| ConstBool of bool
| ConstBit of int * word
| ConstVector of kind * int * constT vec
| ConstStruct of int * kind attribute t0 * (kind attribute, constT) ilist
| ConstArray of kind * int * constT t0

type constFullT =
| SyntaxConst of kind * constT
| NativeConst of __ * __

(** val vector_repeat : int -> 'a1 -> 'a1 t0 **)

let rec vector_repeat n a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil1)
    (fun m -> Cons (a, m, (vector_repeat m a)))
    n

(** val getDefaultConst : kind -> constT **)

let rec getDefaultConst = function
| Bool -> ConstBool false
| Bit n -> ConstBit (n, (wzero n))
| Vector (k0, n) -> ConstVector (k0, n, (replicate (getDefaultConst k0) n))
| Struct (n, ls) ->
  ConstStruct (n, ls,
    (let rec help _ = function
     | Nil1 -> Inil
     | Cons (x, m, xs) ->
       Icons (x, m, xs, (getDefaultConst x.attrType), (help m xs))
     in help n ls))
| Array (k0, n) -> ConstArray (k0, n, (vector_repeat n (getDefaultConst k0)))

type signatureT = { arg : kind; ret : kind }

type uniBoolOp =
| NegB

type binBoolOp =
| AndB
| OrB

type uniBitOp =
| Inv of int
| Neg of int
| ConstExtract of int * int * int
| Trunc of int * int
| ZeroExtendTrunc of int * int
| SignExtendTrunc of int * int
| TruncLsb of int * int

type binSign =
| SignSS
| SignSU
| SignUU

type binBitOp =
| Add of int
| Sub of int
| Mul of int * binSign
| Div of int * bool
| Rem of int * bool
| Band of int
| Bor of int
| Bxor of int
| Sll of int * int
| Srl of int * int
| Sra of int * int
| Concat of int * int

type binBitBoolOp =
| Lt of int
| Slt of int

type 'ty fullType = __

(** val fieldKind : int -> kind attribute t0 -> t -> kind **)

let fieldKind n ls i =
  nth n (map0 (fun a -> a.attrType) n ls) i

type 'ty expr =
| Var of fullKind * 'ty fullType
| Const of kind * constT
| UniBool of uniBoolOp * 'ty expr
| BinBool of binBoolOp * 'ty expr * 'ty expr
| UniBit of int * int * uniBitOp * 'ty expr
| BinBit of int * int * int * binBitOp * 'ty expr * 'ty expr
| BinBitBool of int * int * binBitBoolOp * 'ty expr * 'ty expr
| ITE of fullKind * 'ty expr * 'ty expr * 'ty expr
| Eq of kind * 'ty expr * 'ty expr
| ReadIndex of int * kind * 'ty expr * 'ty expr
| ReadField of int * kind attribute t0 * t * 'ty expr
| BuildVector of kind * int * 'ty expr vec
| BuildStruct of int * kind attribute t0 * (kind attribute, 'ty expr) ilist
| UpdateVector of int * kind * 'ty expr * 'ty expr * 'ty expr
| ReadArrayIndex of int * kind * int * 'ty expr * 'ty expr
| BuildArray of kind * int * 'ty expr t0
| UpdateArray of kind * int * int * 'ty expr * 'ty expr * 'ty expr

type bitFormat =
| Binary
| Decimal
| Hex

type fullBitFormat = int * bitFormat

type 'ty disp =
| DispBool of fullBitFormat * 'ty expr
| DispBit of fullBitFormat * int * 'ty expr
| DispStruct of int * fullBitFormat t0 * kind attribute t0 * 'ty expr
| DispArray of fullBitFormat * kind * int * 'ty expr

type 'ty actionT =
| MCall of char list * signatureT * 'ty expr * ('ty -> 'ty actionT)
| Let_ of fullKind * 'ty expr * ('ty fullType -> 'ty actionT)
| ReadNondet of fullKind * ('ty fullType -> 'ty actionT)
| ReadReg of char list * fullKind * ('ty fullType -> 'ty actionT)
| WriteReg of char list * fullKind * 'ty expr * 'ty actionT
| IfElse of 'ty expr * kind * 'ty actionT * 'ty actionT * ('ty -> 'ty actionT)
| Assert_ of 'ty expr * 'ty actionT
| Displ of 'ty disp list * 'ty actionT
| Return of 'ty expr

type action = __ -> __ actionT

type methodT = __ -> __ -> __ actionT

type regInitValue =
| RegInitCustom of (fullKind, constFullT) sigT
| RegInitDefault of fullKind

type regInitT = regInitValue attribute

type defMethT = (signatureT, methodT) sigT attribute

(** val void : kind **)

let void =
  Bit 0

type primitiveModule = { pm_name : char list; pm_regInits : regInitT list;
                         pm_rules : action attribute list;
                         pm_methods : defMethT list }

type modules =
| PrimMod of primitiveModule
| Mod of regInitT list * action attribute list * defMethT list
| ConcatMod of modules * modules

(** val fieldAccessor : char list -> 'a1 attribute -> bool **)

let fieldAccessor fn x =
  string_eq fn x.attrName

type moduleElt =
| MERegister of regInitT
| MERule of action attribute
| MEMeth of defMethT

type inModule =
| NilInModule
| ConsInModule of moduleElt * inModule

(** val makeModule' :
    inModule -> (regInitT list * action attribute list) * defMethT list **)

let rec makeModule' = function
| NilInModule -> (([], []), [])
| ConsInModule (e, i) ->
  let (p, imeths) = makeModule' i in
  let (iregs, irules) = p in
  (match e with
   | MERegister mreg -> (((mreg :: iregs), irules), imeths)
   | MERule mrule -> ((iregs, (mrule :: irules)), imeths)
   | MEMeth mmeth -> ((iregs, irules), (mmeth :: imeths)))

(** val makeModule : inModule -> modules **)

let makeModule im =
  let (p, meths) = makeModule' im in
  let (regs, rules) = p in Mod (regs, rules, meths)

(** val makeConst : kind -> constT -> constFullT **)

let makeConst k c =
  SyntaxConst (k, c)

type tyS = int

type exprS = tyS expr

type actionS =
| MCallS of char list * signatureT * exprS * int * actionS
| LetS_ of fullKind * exprS * int * actionS
| ReadNondetS of int * actionS
| ReadRegS of char list * int * actionS
| WriteRegS of char list * fullKind * exprS * actionS
| IfElseS of exprS * kind * actionS * actionS * int * actionS
| AssertS_ of exprS * actionS
| ReturnS of exprS

(** val getActionS : int -> kind -> tyS actionT -> int * actionS **)

let rec getActionS n lret = function
| MCall (meth, s, e, c) ->
  let (m, a') = getActionS (Stdlib.Int.succ n) lret (c n) in
  (m, (MCallS (meth, s, e, n, a')))
| Let_ (lret', e, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match lret' with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match lret' with
   | SyntaxKind _ -> ((fst v), (LetS_ (lret', e, n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| ReadNondet (k, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match k with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match k with
   | SyntaxKind _ -> ((fst v), (ReadNondetS (n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| ReadReg (r, k, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match k with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match k with
   | SyntaxKind _ -> ((fst v), (ReadRegS (r, n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| WriteReg (r, k, e, c) ->
  let (m, a') = getActionS n lret c in (m, (WriteRegS (r, k, e, a')))
| IfElse (e, k, ta, fa, c) ->
  let (tm, ta') = getActionS n k ta in
  let (fm, fa') = getActionS tm k fa in
  let (m, a') = getActionS (Stdlib.Int.succ fm) lret (c fm) in
  (m, (IfElseS (e, k, ta', fa', fm, a')))
| Assert_ (e, c) ->
  let (m, a') = getActionS n lret c in (m, (AssertS_ (e, a')))
| Displ (_, c) -> getActionS n lret c
| Return e -> (n, (ReturnS e))

type methodTS = actionS

type defMethTS = (signatureT, methodTS) sigT attribute

type modulesS =
| PrimModS of char list * signatureT attribute list
| ModS of regInitT list * actionS attribute list * defMethTS list
| ConcatModsS of modulesS * modulesS

(** val getMethS :
    (signatureT, methodT) sigT -> (signatureT, methodTS) sigT **)

let getMethS = function
| ExistT (arg0, meth) ->
  ExistT (arg0,
    (snd (getActionS (Stdlib.Int.succ 0) arg0.ret (Obj.magic meth __ 0))))

(** val getModuleS : modules -> modulesS **)

let rec getModuleS = function
| PrimMod prim ->
  PrimModS (prim.pm_name,
    (map (fun dm -> { attrName = dm.attrName; attrType =
      (projT1 dm.attrType) }) prim.pm_methods))
| Mod (regs, rules, dms) ->
  ModS (regs,
    (map (fun a -> { attrName = a.attrName; attrType =
      (snd (getActionS 0 void ((Obj.magic a).attrType __))) }) rules),
    (map (fun a -> { attrName = a.attrName; attrType =
      (getMethS a.attrType) }) dms))
| ConcatMod (m1, m2) -> ConcatModsS ((getModuleS m1), (getModuleS m2))

(** val mapVec : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec **)

let rec mapVec map1 _ = function
| Vec0 e -> Vec0 (map1 e)
| VecNext (n', v1, v2) ->
  VecNext (n', (mapVec map1 n' v1), (mapVec map1 n' v2))

type bExpr =
| BVar of int
| BConst of kind * constT
| BUniBool of uniBoolOp * bExpr
| BBinBool of binBoolOp * bExpr * bExpr
| BUniBit of int * int * uniBitOp * bExpr
| BBinBit of int * int * int * binBitOp * bExpr * bExpr
| BBinBitBool of int * int * binBitBoolOp * bExpr * bExpr
| BITE of bExpr * bExpr * bExpr
| BEq of bExpr * bExpr
| BReadIndex of bExpr * bExpr
| BReadField of char list * bExpr
| BBuildVector of int * bExpr vec
| BBuildStruct of int * kind attribute t0 * bExpr attribute list
| BUpdateVector of bExpr * bExpr * bExpr
| BReadReg of char list
| BReadArrayIndex of bExpr * bExpr
| BBuildArray of int * bExpr t0
| BUpdateArray of bExpr * bExpr * bExpr

type bAction =
| BMCall of int * char list * signatureT * bExpr
| BBCall of int * char list * bool * bExpr list
| BLet of int * kind option * bExpr
| BWriteReg of char list * bExpr
| BIfElse of bExpr * int * kind * bAction list * bAction list
| BAssert of bExpr
| BReturn of bExpr

type bRule = bAction list attribute

type bMethod = (signatureT * bAction list) attribute

type bModule =
| BModulePrim of char list * signatureT attribute list
| BModuleB of regInitT list * bRule list * bMethod list

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind oa f =
  match oa with
  | Some a -> f a
  | None -> None

(** val bindVec : int -> 'a1 option vec -> 'a1 vec option **)

let rec bindVec _ = function
| Vec0 oa -> bind oa (fun a -> Some (Vec0 a))
| VecNext (n0, v1, v2) ->
  bind (bindVec n0 v1) (fun bv1 ->
    bind (bindVec n0 v2) (fun bv2 -> Some (VecNext (n0, bv1, bv2))))

(** val bindVector : int -> 'a1 option t0 -> 'a1 t0 option **)

let rec bindVector _ = function
| Nil1 -> Some Nil1
| Cons (a, n, vs) ->
  bind a (fun bv1 ->
    bind (bindVector n vs) (fun bv2 -> Some (Cons (bv1, n, bv2))))

(** val exprSToBExpr : fullKind -> exprS -> bExpr option **)

let rec exprSToBExpr _ = function
| Var (vk, i) ->
  (match vk with
   | SyntaxKind _ -> Some (BVar (Obj.magic i))
   | NativeKind _ -> None)
| Const (k, c) -> Some (BConst (k, c))
| UniBool (op, se) ->
  bind (exprSToBExpr (SyntaxKind Bool) se) (fun be -> Some (BUniBool (op,
    be)))
| BinBool (op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind Bool) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind Bool) e2) (fun be2 -> Some (BBinBool (op,
      be1, be2))))
| UniBit (n1, n2, op, e0) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e0) (fun be -> Some (BUniBit (n1,
    n2, op, be)))
| BinBit (n1, n2, n3, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some (BBinBit
      (n1, n2, n3, op, be1, be2))))
| BinBitBool (n1, n2, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some
      (BBinBitBool (n1, n2, op, be1, be2))))
| ITE (k0, ce, te, fe) ->
  bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
    bind (exprSToBExpr k0 te) (fun bte ->
      bind (exprSToBExpr k0 fe) (fun bfe -> Some (BITE (bce, bte, bfe)))))
| Eq (k0, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind k0) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind k0) e2) (fun be2 -> Some (BEq (be1, be2))))
| ReadIndex (i, k0, ie, ve) ->
  bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
    bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve -> Some
      (BReadIndex (bie, bve))))
| ReadField (n, ls, i, e0) ->
  bind (exprSToBExpr (SyntaxKind (Struct (n, ls))) e0) (fun be -> Some
    (BReadField ((nth n (map0 (fun a -> a.attrName) n ls) i), be)))
| BuildVector (n, lgn, v) ->
  bind (bindVec lgn (mapVec (exprSToBExpr (SyntaxKind n)) lgn v)) (fun bv ->
    Some (BBuildVector (lgn, bv)))
| BuildStruct (n, attrs, st) ->
  bind
    (let rec help _ _ = function
     | Inil -> Some []
     | Icons (k, na, vs, h, t1) ->
       (match exprSToBExpr (SyntaxKind k.attrType) h with
        | Some v ->
          bind (help na vs t1) (fun bl -> Some ({ attrName = k.attrName;
            attrType = v } :: bl))
        | None -> None)
     in help n attrs st) (fun bl -> Some (BBuildStruct (n, attrs, bl)))
| UpdateVector (i, k0, ve, ie, ke) ->
  bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve ->
    bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
      bind (exprSToBExpr (SyntaxKind k0) ke) (fun bke -> Some (BUpdateVector
        (bve, bie, bke)))))
| ReadArrayIndex (i, k0, sz, ie, ve) ->
  bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
    bind (exprSToBExpr (SyntaxKind (Array (k0, (Stdlib.Int.succ sz)))) ve)
      (fun bve -> Some (BReadArrayIndex (bie, bve))))
| BuildArray (n0, n, v) ->
  bind (bindVector n (map0 (exprSToBExpr (SyntaxKind n0)) n v)) (fun bv ->
    Some (BBuildArray (n, bv)))
| UpdateArray (k0, sz, i, ve, ie, ke) ->
  bind (exprSToBExpr (SyntaxKind (Array (k0, (Stdlib.Int.succ sz)))) ve)
    (fun bve ->
    bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
      bind (exprSToBExpr (SyntaxKind k0) ke) (fun bke -> Some (BUpdateArray
        (bve, bie, bke)))))

(** val actionSToBAction : kind -> actionS -> bAction list option **)

let rec actionSToBAction k = function
| MCallS (name, msig, arge, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind msig.arg) arge) (fun be -> Some ((BMCall
      (idx, name, msig, be)) :: bc)))
| LetS_ (lretT', e0, idx, cont) ->
  (match lretT' with
   | SyntaxKind k0 ->
     bind (actionSToBAction k cont) (fun bc ->
       bind (exprSToBExpr (SyntaxKind k0) e0) (fun be -> Some ((BLet (idx,
         (Some k0), be)) :: bc)))
   | NativeKind _ -> None)
| ReadNondetS (_, _) -> None
| ReadRegS (reg, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc -> Some ((BLet (idx, None, (BReadReg
    reg))) :: bc))
| WriteRegS (reg, k0, e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr k0 e0) (fun be -> Some ((BWriteReg (reg, be)) :: bc)))
| IfElseS (ce, iretK, ta, fa, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
      bind (actionSToBAction iretK ta) (fun bta ->
        bind (actionSToBAction iretK fa) (fun bfa -> Some ((BIfElse (bce,
          idx, iretK, bta, bfa)) :: bc)))))
| AssertS_ (e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) e0) (fun be -> Some ((BAssert
      be) :: bc)))
| ReturnS e0 ->
  bind (exprSToBExpr (SyntaxKind k) e0) (fun be -> Some ((BReturn be) :: []))

(** val rulesToBRules :
    actionS attribute list -> bAction list attribute list option **)

let rec rulesToBRules = function
| [] -> Some []
| a :: rs ->
  let { attrName = rn; attrType = rb } = a in
  bind (rulesToBRules rs) (fun brs ->
    bind (actionSToBAction void rb) (fun brb -> Some ({ attrName = rn;
      attrType = brb } :: brs)))

(** val methsToBMethods : defMethTS list -> bMethod list option **)

let rec methsToBMethods = function
| [] -> Some []
| d :: ms ->
  let { attrName = mn; attrType = attrType0 } = d in
  let ExistT (sig0, mb) = attrType0 in
  bind (methsToBMethods ms) (fun bms ->
    bind (actionSToBAction sig0.ret mb) (fun bmb -> Some ({ attrName = mn;
      attrType = (sig0, bmb) } :: bms)))

(** val modulesSToBModules : modulesS -> bModule list option **)

let rec modulesSToBModules = function
| PrimModS (pname, ifc) -> Some ((BModulePrim (pname, ifc)) :: [])
| ModS (regs, rules, dms) ->
  bind (rulesToBRules rules) (fun brules ->
    bind (methsToBMethods dms) (fun bdms -> Some ((BModuleB (regs, brules,
      bdms)) :: [])))
| ConcatModsS (m1, m2) ->
  bind (modulesSToBModules m1) (fun bm1 ->
    bind (modulesSToBModules m2) (fun bm2 -> Some (app bm1 bm2)))

(** val regIdxSz : int **)

let regIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val memAddrSz : int **)

let memAddrSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val wordSz : int **)

let wordSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))

(** val opcodeSz : int **)

let opcodeSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val costSz : int **)

let costSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val muTensorIdxSz : int **)

let muTensorIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val pTableIdxSz : int **)

let pTableIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val pT_NEXT_ID_INIT : word **)

let pT_NEXT_ID_INIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_CHSH_VAL : word **)

let eRR_CHSH_VAL =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_BIANCHI_VAL : word **)

let eRR_BIANCHI_VAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_LOGIC_VAL : word **)

let eRR_LOGIC_VAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val cHSH_X1_SURCHARGE : word **)

let cHSH_X1_SURCHARGE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val oP_PNEW : word **)

let oP_PNEW =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PSPLIT : word **)

let oP_PSPLIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PMERGE : word **)

let oP_PMERGE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LASSERT : word **)

let oP_LASSERT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LJOIN : word **)

let oP_LJOIN =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MDLACC : word **)

let oP_MDLACC =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PDISCOVER : word **)

let oP_PDISCOVER =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XFER : word **)

let oP_XFER =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LOAD_IMM : word **)

let oP_LOAD_IMM =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_CHSH_TRIAL : word **)

let oP_CHSH_TRIAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_LOAD : word **)

let oP_XOR_LOAD =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_ADD : word **)

let oP_XOR_ADD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_SWAP : word **)

let oP_XOR_SWAP =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_RANK : word **)

let oP_XOR_RANK =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_EMIT : word **)

let oP_EMIT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_REVEAL : word **)

let oP_REVEAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_ORACLE_HALTS : word **)

let oP_ORACLE_HALTS =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LOAD : word **)

let oP_LOAD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_STORE : word **)

let oP_STORE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_ADD : word **)

let oP_ADD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_SUB : word **)

let oP_SUB =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_JUMP : word **)

let oP_JUMP =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_JNEZ : word **)

let oP_JNEZ =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_CALL : word **)

let oP_CALL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_RET : word **)

let oP_RET =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_HALT : word **)

let oP_HALT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))

(** val instrSz : int **)

let instrSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))

(** val loadInstrPort : kind attribute t0 **)

let loadInstrPort =
  Cons ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (Bit
    memAddrSz) }, (Stdlib.Int.succ 0), (Cons ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = (Bit instrSz) }, 0, Nil1)))

(** val logicRespPort : kind attribute t0 **)

let logicRespPort =
  Cons ({ attrName = ('v'::('a'::('l'::('i'::('d'::[]))))); attrType =
    Bool }, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (Cons ({ attrName =
    ('e'::('r'::('r'::('o'::('r'::[]))))); attrType = Bool },
    (Stdlib.Int.succ 0), (Cons ({ attrName =
    ('v'::('a'::('l'::('u'::('e'::[]))))); attrType = (Bit wordSz) }, 0,
    Nil1)))))

(** val sP_IDX : word **)

let sP_IDX =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))

(** val thieleCore : modules **)

let thieleCore =
  makeModule (ConsInModule ((MERegister { attrName = ('p'::('c'::[]));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName = ('m'::('u'::[])); attrType = (RegInitDefault
    (SyntaxKind (Bit wordSz))) }), (ConsInModule ((MERegister { attrName =
    ('e'::('r'::('r'::[]))); attrType = (RegInitCustom (ExistT ((SyntaxKind
    Bool), (makeConst Bool (ConstBool false))))) }), (ConsInModule
    ((MERegister { attrName = ('h'::('a'::('l'::('t'::('e'::('d'::[]))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName = ('r'::('e'::('g'::('s'::[])))); attrType = (RegInitDefault
    (SyntaxKind (Vector ((Bit wordSz), regIdxSz)))) }), (ConsInModule
    ((MERegister { attrName = ('m'::('e'::('m'::[]))); attrType =
    (RegInitDefault (SyntaxKind (Vector ((Bit wordSz), memAddrSz)))) }),
    (ConsInModule ((MERegister { attrName = ('i'::('m'::('e'::('m'::[]))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz)))) }), (ConsInModule ((MERegister { attrName =
    ('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[])))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))); attrType =
    (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule ((MERegister
    { attrName =
    ('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('o'::('p'::('c'::('o'::('d'::('e'::[]))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit opcodeSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('p'::('a'::('y'::('l'::('o'::('a'::('d'::[])))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('e'::('r'::('r'::('o'::('r'::[]))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('p'::('t'::('_'::('s'::('i'::('z'::('e'::('s'::[])))))))); attrType =
    (RegInitDefault (SyntaxKind (Vector ((Bit wordSz), pTableIdxSz)))) }),
    (ConsInModule ((MERegister { attrName =
    ('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit wordSz)),
    (makeConst (Bit wordSz) (ConstBit (wordSz, pT_NEXT_ID_INIT)))))) }),
    (ConsInModule ((MERule { attrName = ('s'::('t'::('e'::('p'::[]))));
    attrType = (fun _ -> ReadReg
    (('h'::('a'::('l'::('t'::('e'::('d'::[])))))), (SyntaxKind Bool),
    (fun halted_v -> Assert_ ((UniBool (NegB, (Var ((SyntaxKind Bool),
    halted_v)))), (ReadReg (('e'::('r'::('r'::[]))), (SyntaxKind Bool),
    (fun err_v -> Assert_ ((UniBool (NegB, (Var ((SyntaxKind Bool),
    err_v)))), (ReadReg (('p'::('c'::[])), (SyntaxKind (Bit wordSz)),
    (fun pc_v -> ReadReg (('m'::('u'::[])), (SyntaxKind (Bit wordSz)),
    (fun mu_v -> ReadReg (('r'::('e'::('g'::('s'::[])))), (SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), (fun regs_v -> ReadReg
    (('m'::('e'::('m'::[]))), (SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), (fun mem_v -> ReadReg (('i'::('m'::('e'::('m'::[])))),
    (SyntaxKind (Vector ((Bit instrSz), memAddrSz))), (fun imem_v -> ReadReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun partition_ops_v -> ReadReg
    (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (fun mdl_ops_v -> ReadReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun info_gain_v -> ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun error_code_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun logic_acc_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))))))),
    (SyntaxKind Bool), (fun logic_req_valid_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('o'::('p'::('c'::('o'::('d'::('e'::[])))))))))))))))),
    (SyntaxKind (Bit opcodeSz)), (fun logic_req_opcode_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('p'::('a'::('y'::('l'::('o'::('a'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun logic_req_payload_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))))))))),
    (SyntaxKind Bool), (fun logic_resp_valid_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('e'::('r'::('r'::('o'::('r'::[])))))))))))))))),
    (SyntaxKind Bool), (fun logic_resp_error_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('u'::('e'::[])))))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun logic_resp_value_v -> ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun mu_tensor_v ->
    ReadReg (('p'::('t'::('_'::('s'::('i'::('z'::('e'::('s'::[])))))))),
    (SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (fun pt_sizes_v ->
    ReadReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun pt_next_id_v -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t2 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t3 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t4 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t5 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t6 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t7 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t8 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t9 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t10 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t11 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t12 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t13 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t14 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t15 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t16 ->
    Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), t1)), (Var
    ((SyntaxKind (Bit wordSz)), t2)))), (Var ((SyntaxKind (Bit wordSz)),
    t3)))), (Var ((SyntaxKind (Bit wordSz)), t4)))), (Var ((SyntaxKind (Bit
    wordSz)), t5)))), (Var ((SyntaxKind (Bit wordSz)), t6)))), (Var
    ((SyntaxKind (Bit wordSz)), t7)))), (Var ((SyntaxKind (Bit wordSz)),
    t8)))), (Var ((SyntaxKind (Bit wordSz)), t9)))), (Var ((SyntaxKind (Bit
    wordSz)), t10)))), (Var ((SyntaxKind (Bit wordSz)), t11)))), (Var
    ((SyntaxKind (Bit wordSz)), t12)))), (Var ((SyntaxKind (Bit wordSz)),
    t13)))), (Var ((SyntaxKind (Bit wordSz)), t14)))), (Var ((SyntaxKind (Bit
    wordSz)), t15)))), (Var ((SyntaxKind (Bit wordSz)), t16)))),
    (fun tensor_total -> Let_ ((SyntaxKind Bool), (BinBitBool (wordSz,
    wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Var
    ((SyntaxKind (Bit wordSz)), tensor_total)))), (fun bianchi_violation ->
    Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))), memAddrSz, (Trunc
    (memAddrSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), pc_v)))), (fun pc_addr -> Let_ ((SyntaxKind (Bit instrSz)),
    (ReadIndex (memAddrSz, (Bit instrSz), (Var ((SyntaxKind (Bit memAddrSz)),
    pc_addr)), (Var ((SyntaxKind (Vector ((Bit instrSz), memAddrSz))),
    imem_v)))), (fun instr_v -> Let_ ((SyntaxKind (Bit opcodeSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))))))))))) (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) 0),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), 0)), (Var ((SyntaxKind (Bit instrSz)), instr_v)))),
    (fun opcode -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), (Var ((SyntaxKind (Bit instrSz)), instr_v)))), (fun op_a ->
    Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit instrSz)), instr_v)))),
    (fun op_b -> Let_ ((SyntaxKind (Bit costSz)), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Trunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    instrSz)), instr_v)))), (fun cost_v -> Let_ ((SyntaxKind (Bit wordSz)),
    (UniBit (costSz, wordSz, (ZeroExtendTrunc (costSz, wordSz)), (Var
    ((SyntaxKind (Bit costSz)), cost_v)))), (fun cost32 -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), mu_v)), (Var ((SyntaxKind (Bit wordSz)),
    cost32)))), (fun new_mu -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    pc_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun pc_plus_1 -> Let_
    ((SyntaxKind (Bit regIdxSz)), (UniBit
    ((add regIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    regIdxSz, (Trunc (regIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun dst_idx -> Let_ ((SyntaxKind (Bit regIdxSz)), (UniBit
    ((add regIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    regIdxSz, (Trunc (regIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun src_idx -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))) 0), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstExtract
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), 0)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun op_b_hi -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Trunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))), (fun op_b_lo ->
    Let_ ((SyntaxKind (Bit regIdxSz)), (UniBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), regIdxSz,
    (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), regIdxSz)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), op_b_hi)))), (fun rs1_idx -> Let_ ((SyntaxKind (Bit regIdxSz)),
    (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), regIdxSz, (ZeroExtendTrunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), regIdxSz)),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), op_b_lo)))), (fun rs2_idx -> Let_ ((SyntaxKind
    (Bit wordSz)), (ReadIndex (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    regIdxSz)), rs1_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)))), (fun rs1_val -> Let_ ((SyntaxKind (Bit wordSz)),
    (ReadIndex (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)),
    rs2_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    regs_v)))), (fun rs2_val -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)))),
    (fun dst_val -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex (regIdxSz,
    (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)), src_idx)), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)))),
    (fun src_val -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), wordSz, (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz)), (Var ((SyntaxKind
    (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun imm32 -> Let_ ((SyntaxKind (Bit memAddrSz)),
    (UniBit ((add memAddrSz 0), memAddrSz, (Trunc (memAddrSz, 0)), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun mem_addr -> Let_
    ((SyntaxKind (Bit memAddrSz)), (UniBit ((add memAddrSz 0), memAddrSz,
    (Trunc (memAddrSz, 0)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun mem_addr_a -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (memAddrSz, (Bit wordSz), (Var ((SyntaxKind (Bit memAddrSz)), mem_addr)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v)))),
    (fun mem_val -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun pt_probe_idx -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pt_probe_idx)), (Var ((SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))),
    (fun pt_probe_size -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), wordSz, (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz)), (Var ((SyntaxKind
    (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun jnez_target -> Let_ ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (BinBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))), (Concat ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun jump_target_16 -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))), wordSz, (ZeroExtendTrunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    jump_target_16)))), (fun jump_target -> Let_ ((SyntaxKind (Bit wordSz)),
    (ReadIndex (regIdxSz, (Bit wordSz), (Const ((Bit regIdxSz), (ConstBit
    (regIdxSz, sP_IDX)))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)))), (fun sp_val -> Let_ ((SyntaxKind (Bit
    memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))), memAddrSz, (Trunc
    (memAddrSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), sp_val)))), (fun sp_addr -> Let_ ((SyntaxKind (Bit wordSz)),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), sp_val)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun sp_inc -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Sub
    wordSz), (Var ((SyntaxKind (Bit wordSz)), sp_val)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (fun sp_dec -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))), memAddrSz, (Trunc
    (memAddrSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), sp_dec)))), (fun sp_dec_addr -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex (memAddrSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    memAddrSz)), sp_dec_addr)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), mem_v)))), (fun ret_pc -> Let_ ((SyntaxKind (Bit wordSz)),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), rs1_val)), (Var ((SyntaxKind (Bit wordSz)), rs2_val)))),
    (fun add_result -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Sub wordSz), (Var ((SyntaxKind (Bit wordSz)), rs1_val)),
    (Var ((SyntaxKind (Bit wordSz)), rs2_val)))), (fun sub_result -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Bxor
    wordSz), (Var ((SyntaxKind (Bit wordSz)), dst_val)), (Var ((SyntaxKind
    (Bit wordSz)), src_val)))), (fun xor_result -> Let_ ((SyntaxKind Bool),
    (let e1 = Var ((SyntaxKind (Bit wordSz)), dst_val) in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))), (fun jnez_taken -> Let_
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), src_val)),
    (fun pop_val -> Let_ ((SyntaxKind (Bit wordSz)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask1 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)),
    pop_val)), (Var ((SyntaxKind (Bit wordSz)), pop_mask1)))),
    (fun pop_s1a -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Band wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), wordSz, (Srl
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var ((SyntaxKind (Bit
    wordSz)), pop_val)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), pop_mask1)))),
    (fun pop_s1b -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_s1a)), (Var
    ((SyntaxKind (Bit wordSz)), pop_s1b)))), (fun pop_2 -> Let_ ((SyntaxKind
    (Bit wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask2 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_2)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask2)))), (fun pop_n1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), wordSz, (Srl
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var ((SyntaxKind (Bit
    wordSz)), pop_2)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), pop_mask2)))),
    (fun pop_n2 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_n1)), (Var
    ((SyntaxKind (Bit wordSz)), pop_n2)))), (fun pop_4 -> Let_ ((SyntaxKind
    (Bit wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask3 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_4)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask3)))), (fun pop_b1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), wordSz, (Srl
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var ((SyntaxKind (Bit
    wordSz)), pop_4)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), pop_mask3)))),
    (fun pop_b2 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_b1)), (Var
    ((SyntaxKind (Bit wordSz)), pop_b2)))), (fun pop_8 -> Let_ ((SyntaxKind
    (Bit wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask4 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_8)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask4)))), (fun pop_h1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), wordSz, (Srl
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var ((SyntaxKind (Bit
    wordSz)), pop_8)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), pop_mask4)))),
    (fun pop_h2 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_h1)), (Var
    ((SyntaxKind (Bit wordSz)), pop_h2)))), (fun pop_16 -> Let_ ((SyntaxKind
    (Bit wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask5 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_16)), (BinBit (wordSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (Var ((SyntaxKind (Bit wordSz)), pop_16)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask5)))), (fun popcount -> Let_
    ((SyntaxKind Bool), (BinBitBool ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Lt
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))))),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun chsh_outcomes_bad -> Let_
    ((SyntaxKind Bool), (BinBitBool ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Lt
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))))),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)))), (fun chsh_x1 -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (Var ((SyntaxKind Bool), chsh_x1)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), tensor_total)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))))),
    (fun chsh_cert_missing -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (Var
    ((SyntaxKind Bool), chsh_outcomes_bad)), (Var ((SyntaxKind Bool),
    chsh_cert_missing)))), (fun chsh_bits_bad -> Let_ ((SyntaxKind Bool),
    (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LASSERT)))))),
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LJOIN)))))))),
    (fun is_logic_op -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (BinBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))), (Concat ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun lpayload16 -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))), wordSz, (ZeroExtendTrunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    lpayload16)))), (fun lpayload32 -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), logic_req_valid_v)), (UniBool (NegB, (Var
    ((SyntaxKind Bool), logic_resp_valid_v)))))), (fun logic_rsp_pending ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    logic_req_valid_v)), (Var ((SyntaxKind Bool), logic_resp_valid_v)))),
    (fun logic_rsp_fire -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_logic_op)), (UniBool (NegB, (Var ((SyntaxKind
    Bool), logic_req_valid_v)))))), (fun logic_issue -> Let_ ((SyntaxKind
    (Bit muTensorIdxSz)), (UniBit
    ((add muTensorIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))), muTensorIdxSz, (Trunc (muTensorIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun tensor_idx -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (muTensorIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit muTensorIdxSz)),
    tensor_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))),
    mu_tensor_v)))), (fun tensor_old -> Let_ ((SyntaxKind (Bit wordSz)),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), tensor_old)), (Var ((SyntaxKind (Bit wordSz)), cost32)))),
    (fun tensor_new_val -> Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind
    (Bit wordSz)), (BinBool (OrB, (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool), logic_rsp_pending)))), (Var
    ((SyntaxKind (Bit wordSz)), pc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_HALT)))))), (Var ((SyntaxKind
    (Bit wordSz)), pc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_JUMP)))))), (Var ((SyntaxKind (Bit
    wordSz)), jump_target)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_CALL)))))), (Var ((SyntaxKind (Bit
    wordSz)), jump_target)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_RET)))))), (Var ((SyntaxKind (Bit
    wordSz)), ret_pc)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_JNEZ)))))), (Var ((SyntaxKind
    Bool), jnez_taken)))), (Var ((SyntaxKind (Bit wordSz)), jnez_target)),
    (Var ((SyntaxKind (Bit wordSz)), pc_plus_1)))))))))))))), (fun new_pc ->
    Let_ ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (UpdateVector
    (regIdxSz, (Bit wordSz), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    src_val)))), (Var ((SyntaxKind (Bit regIdxSz)), src_idx)), (Var
    ((SyntaxKind (Bit wordSz)), dst_val)))), (fun swap_regs -> Let_
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (ITE ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LOAD_IMM)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), imm32)))), (ITE ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_ADD)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    add_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_SUB)))))), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), sub_result)))), (ITE ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_XFER)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit
    regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)), src_val)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_LOAD)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), mem_val)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_XOR_LOAD)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), mem_val)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_XOR_ADD)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), xor_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_XOR_SWAP)))))),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), swap_regs)), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_XOR_RANK)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), popcount)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CALL)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Const ((Bit regIdxSz), (ConstBit
    (regIdxSz, sP_IDX)))), (Var ((SyntaxKind (Bit wordSz)), sp_inc)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_RET)))))), (UpdateVector (regIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Const
    ((Bit regIdxSz), (ConstBit (regIdxSz, sP_IDX)))), (Var ((SyntaxKind (Bit
    wordSz)), sp_dec)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_PDISCOVER)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    pt_probe_size)))), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    regs_v)))))))))))))))))))))))))))), (fun new_regs -> Let_ ((SyntaxKind
    (Vector ((Bit wordSz), memAddrSz))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v)), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_STORE)))))), (UpdateVector (memAddrSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v)),
    (Var ((SyntaxKind (Bit memAddrSz)), mem_addr_a)), (Var ((SyntaxKind (Bit
    wordSz)), src_val)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CALL)))))),
    (UpdateVector (memAddrSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), mem_v)), (Var ((SyntaxKind (Bit memAddrSz)),
    sp_addr)), (Var ((SyntaxKind (Bit wordSz)), pc_plus_1)))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v)))))))),
    (fun new_mem -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (Var ((SyntaxKind
    Bool), bianchi_violation)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_HALT)))))))), (fun new_halted -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), logic_rsp_fire)), (Var ((SyntaxKind
    Bool), logic_resp_error_v)))), (fun logic_resp_fail -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool),
    chsh_bits_bad)))), (Var ((SyntaxKind Bool), logic_resp_fail)))),
    (fun new_err -> Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), bianchi_violation)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_BIANCHI_VAL)))), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), logic_resp_fail)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_LOGIC_VAL)))), (ITE ((SyntaxKind (Bit
    wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool), chsh_bits_bad)))), (Const
    ((Bit wordSz), (ConstBit (wordSz, eRR_CHSH_VAL)))), (Var ((SyntaxKind
    (Bit wordSz)), error_code_v)))))))), (fun new_error_code -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind (Bit wordSz)),
    mu_v)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    logic_rsp_pending)), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (ITE
    ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_ORACLE_HALTS)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz
      (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 (D0 Nil)))))))))))))))),
    (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool),
    chsh_x1)))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), new_mu)), (Const ((Bit wordSz), (ConstBit
    (wordSz, cHSH_X1_SURCHARGE)))))), (Var ((SyntaxKind (Bit wordSz)),
    new_mu)))))))))), (fun final_mu -> Let_ ((SyntaxKind (Bit pTableIdxSz)),
    (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pt_next_id_v)))), (fun pt_slot -> Let_
    ((SyntaxKind (Bit wordSz)), (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz, (ZeroExtendTrunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun pnew_region_size -> Let_ ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (UpdateVector (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), pt_sizes_v)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pt_slot)), (Var ((SyntaxKind (Bit
    wordSz)), pnew_region_size)))), (fun pt_after_pnew -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), pt_next_id_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (fun next_after_pnew -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)))), (fun psplit_id -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), psplit_id)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun psplit_orig_sz ->
    Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var
    ((SyntaxKind (Bit wordSz)), psplit_orig_sz)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))),
    (fun psplit_left_sz -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Sub wordSz), (Var ((SyntaxKind (Bit wordSz)),
    psplit_orig_sz)), (Var ((SyntaxKind (Bit wordSz)), psplit_left_sz)))),
    (fun psplit_right_sz -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pt_next_id_v)))), (fun psplit_slot1 -> Let_
    ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    pt_next_id_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))))), (fun psplit_slot2 -> Let_
    ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (UpdateVector
    (pTableIdxSz, (Bit wordSz), (UpdateVector (pTableIdxSz, (Bit wordSz),
    (UpdateVector (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), pTableIdxSz))), pt_sizes_v)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), psplit_id)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit pTableIdxSz)),
    psplit_slot1)), (Var ((SyntaxKind (Bit wordSz)), psplit_left_sz)))), (Var
    ((SyntaxKind (Bit pTableIdxSz)), psplit_slot2)), (Var ((SyntaxKind (Bit
    wordSz)), psplit_right_sz)))), (fun pt_after_psplit -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), pt_next_id_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))),
    (fun next_after_psplit -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)))), (fun pmerge_m1 -> Let_
    ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun pmerge_m2 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pmerge_m1)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun pmerge_m1_sz -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pmerge_m2)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun pmerge_m2_sz -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pmerge_m1_sz)), (Var
    ((SyntaxKind (Bit wordSz)), pmerge_m2_sz)))), (fun pmerge_merged_sz ->
    Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pt_next_id_v)))), (fun pmerge_slot -> Let_
    ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (UpdateVector
    (pTableIdxSz, (Bit wordSz), (UpdateVector (pTableIdxSz, (Bit wordSz),
    (UpdateVector (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), pTableIdxSz))), pt_sizes_v)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), pmerge_m1)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit pTableIdxSz)),
    pmerge_m2)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit pTableIdxSz)),
    pmerge_slot)), (Var ((SyntaxKind (Bit wordSz)), pmerge_merged_sz)))),
    (fun pt_after_pmerge -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    pt_next_id_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun next_after_pmerge ->
    Let_ ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (Var ((SyntaxKind
    Bool), bianchi_violation)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), pt_sizes_v)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PNEW)))))),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), pt_after_pnew)),
    (ITE ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_PSPLIT)))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), pt_after_psplit)), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_PMERGE)))))), (Var ((SyntaxKind (Vector ((Bit
    wordSz), pTableIdxSz))), pt_after_pmerge)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))))))))), (fun new_pt_sizes ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind (Bit wordSz)),
    pt_next_id_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_PNEW)))))), (Var ((SyntaxKind (Bit wordSz)),
    next_after_pnew)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_PSPLIT)))))), (Var ((SyntaxKind (Bit wordSz)),
    next_after_psplit)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_PMERGE)))))), (Var ((SyntaxKind (Bit
    wordSz)), next_after_pmerge)), (Var ((SyntaxKind (Bit wordSz)),
    pt_next_id_v)))))))))), (fun new_pt_next_id -> Let_ ((SyntaxKind Bool),
    (BinBool (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_PNEW)))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PSPLIT)))))))),
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PMERGE)))))))),
    (fun is_partition_op -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_partition_op)), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), partition_ops_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), partition_ops_v)))),
    (fun new_partition_ops -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MDLACC)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), mdl_ops_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), mdl_ops_v)))), (fun new_mdl_ops -> Let_
    ((SyntaxKind (Bit wordSz)), (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz, (ZeroExtendTrunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun op_b_32 -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_PDISCOVER)))))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_EMIT)))))))), (fun is_info_gain_op -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (Var ((SyntaxKind Bool), is_info_gain_op)), (UniBool (NegB, (Var
    ((SyntaxKind Bool), bianchi_violation)))))), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), info_gain_v)),
    (Var ((SyntaxKind (Bit wordSz)), op_b_32)))), (Var ((SyntaxKind (Bit
    wordSz)), info_gain_v)))), (fun new_info_gain -> Let_ ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), muTensorIdxSz))), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_REVEAL)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (UpdateVector (muTensorIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)), (Var
    ((SyntaxKind (Bit muTensorIdxSz)), tensor_idx)), (Var ((SyntaxKind (Bit
    wordSz)), tensor_new_val)))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun new_mu_tensor -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind (Bit wordSz)),
    logic_acc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    logic_rsp_fire)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), logic_acc_v)), (Var ((SyntaxKind (Bit
    wordSz)), logic_resp_value_v)))), (ITE ((SyntaxKind (Bit wordSz)), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_ORACLE_HALTS)))))), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    logic_acc_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit
    wordSz)), logic_acc_v)))))))), (fun new_logic_acc -> Let_ ((SyntaxKind
    Bool), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool), logic_req_valid_v)), (ITE
    ((SyntaxKind Bool), (Var ((SyntaxKind Bool), logic_rsp_fire)), (Const
    (Bool, (ConstBool false))), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind
    Bool), logic_issue)), (Const (Bool, (ConstBool true))), (Var ((SyntaxKind
    Bool), logic_req_valid_v)))))))), (fun new_logic_req_valid -> Let_
    ((SyntaxKind (Bit opcodeSz)), (ITE ((SyntaxKind (Bit opcodeSz)), (Var
    ((SyntaxKind Bool), logic_issue)), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Var ((SyntaxKind (Bit opcodeSz)), logic_req_opcode_v)))),
    (fun new_logic_req_opcode -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool), logic_issue)), (Var
    ((SyntaxKind (Bit wordSz)), lpayload32)), (Var ((SyntaxKind (Bit
    wordSz)), logic_req_payload_v)))), (fun new_logic_req_payload -> Let_
    ((SyntaxKind Bool), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool), logic_resp_valid_v)), (ITE
    ((SyntaxKind Bool), (Var ((SyntaxKind Bool), logic_rsp_fire)), (Const
    (Bool, (ConstBool false))), (Var ((SyntaxKind Bool),
    logic_resp_valid_v)))))), (fun new_logic_resp_valid -> WriteReg
    (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit
    wordSz)), new_pc)), (WriteReg (('m'::('u'::[])), (SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind (Bit wordSz)), final_mu)), (WriteReg
    (('r'::('e'::('g'::('s'::[])))), (SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    new_regs)), (WriteReg (('m'::('e'::('m'::[]))), (SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), new_mem)), (WriteReg
    (('h'::('a'::('l'::('t'::('e'::('d'::[])))))), (SyntaxKind Bool), (Var
    ((SyntaxKind Bool), new_halted)), (WriteReg (('e'::('r'::('r'::[]))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), new_err)), (WriteReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_error_code)), (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_logic_acc)), (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), new_logic_req_valid)),
    (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('o'::('p'::('c'::('o'::('d'::('e'::[])))))))))))))))),
    (SyntaxKind (Bit opcodeSz)), (Var ((SyntaxKind (Bit opcodeSz)),
    new_logic_req_opcode)), (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('p'::('a'::('y'::('l'::('o'::('a'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_logic_req_payload)), (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))))))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), new_logic_resp_valid)),
    (WriteReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_partition_ops)), (WriteReg
    (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind (Bit wordSz)), new_mdl_ops)), (WriteReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_info_gain)), (WriteReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), new_mu_tensor)), (WriteReg
    (('p'::('t'::('_'::('s'::('i'::('z'::('e'::('s'::[])))))))), (SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), (Var ((SyntaxKind (Vector ((Bit
    wordSz), pTableIdxSz))), new_pt_sizes)), (WriteReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_pt_next_id)), (Return (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('l'::('o'::('a'::('d'::('I'::('n'::('s'::('t'::('r'::[])))))))));
    attrType = (ExistT ({ arg = (Struct ((Stdlib.Int.succ (Stdlib.Int.succ
    0)), loadInstrPort)); ret = void }, (fun _ arg0 -> ReadReg
    (('i'::('m'::('e'::('m'::[])))), (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), (fun imem_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), loadInstrPort,
    (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
      (Stdlib.Int.succ 0) loadInstrPort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), loadInstrPort))), arg0)))),
    (fun addr_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), loadInstrPort,
    (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
      (Stdlib.Int.succ 0) loadInstrPort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), loadInstrPort))), arg0)))),
    (fun data_v -> WriteReg (('i'::('m'::('e'::('m'::[])))), (SyntaxKind
    (Vector ((Bit instrSz), memAddrSz))), (UpdateVector (memAddrSz, (Bit
    instrSz), (Var ((SyntaxKind (Vector ((Bit instrSz), memAddrSz))),
    imem_v)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), addr_v)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), data_v)))), (Return (Const
    (void, (getDefaultConst void)))))))))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('P'::('C'::[]))))); attrType = (ExistT
    ({ arg = void; ret = (Bit wordSz) }, (fun _ _ -> ReadReg
    (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (fun v -> Return (Var
    ((SyntaxKind (Bit wordSz)), v))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('M'::('u'::[]))))); attrType = (ExistT
    ({ arg = void; ret = (Bit wordSz) }, (fun _ _ -> ReadReg
    (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun v -> Return (Var
    ((SyntaxKind (Bit wordSz)), v))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('E'::('r'::('r'::[])))))); attrType =
    (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('e'::('r'::('r'::[]))), (SyntaxKind Bool), (fun v -> Return (Var
    ((SyntaxKind Bool), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('H'::('a'::('l'::('t'::('e'::('d'::[])))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('h'::('a'::('l'::('t'::('e'::('d'::[])))))), (SyntaxKind Bool),
    (fun v -> Return (Var ((SyntaxKind Bool), v))))))) }), (ConsInModule
    ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('O'::('p'::('s'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('d'::('l'::('O'::('p'::('s'::[])))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind
    (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit wordSz)),
    v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('I'::('n'::('f'::('o'::('G'::('a'::('i'::('n'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('E'::('r'::('r'::('o'::('r'::('C'::('o'::('d'::('e'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('A'::('c'::('c'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('R'::('e'::('q'::('V'::('a'::('l'::('i'::('d'::[]))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('v'::('a'::('l'::('i'::('d'::[]))))))))))))))),
    (SyntaxKind Bool), (fun v -> Return (Var ((SyntaxKind Bool), v))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('R'::('e'::('q'::('O'::('p'::('c'::('o'::('d'::('e'::[])))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit opcodeSz) }, (fun _ _ ->
    ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('o'::('p'::('c'::('o'::('d'::('e'::[])))))))))))))))),
    (SyntaxKind (Bit opcodeSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    opcodeSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('R'::('e'::('q'::('P'::('a'::('y'::('l'::('o'::('a'::('d'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('q'::('_'::('p'::('a'::('y'::('l'::('o'::('a'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('s'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('R'::('e'::('s'::('p'::[]))))))))))));
    attrType = (ExistT ({ arg = (Struct ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), logicRespPort)); ret = void }, (fun _ arg0 -> Let_
    ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('i'::('d'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (ReadField
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), logicRespPort,
    (vector_find (fieldAccessor ('v'::('a'::('l'::('i'::('d'::[]))))))
      (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort), (Var ((SyntaxKind
    (Struct ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    logicRespPort))), arg0)))), (fun valid_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('e'::('r'::('r'::('o'::('r'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (ReadField
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), logicRespPort,
    (vector_find (fieldAccessor ('e'::('r'::('r'::('o'::('r'::[]))))))
      (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort), (Var ((SyntaxKind
    (Struct ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    logicRespPort))), arg0)))), (fun error_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('u'::('e'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (ReadField
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), logicRespPort,
    (vector_find (fieldAccessor ('v'::('a'::('l'::('u'::('e'::[]))))))
      (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort), (Var ((SyntaxKind
    (Struct ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    logicRespPort))), arg0)))), (fun value_v -> WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('i'::('d'::[])))))))))))))))),
    (SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('i'::('d'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (Var
    ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('i'::('d'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), valid_v)),
    (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('e'::('r'::('r'::('o'::('r'::[])))))))))))))))),
    (SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('e'::('r'::('r'::('o'::('r'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (Var
    ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('e'::('r'::('r'::('o'::('r'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), error_v)),
    (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('r'::('e'::('s'::('p'::('_'::('v'::('a'::('l'::('u'::('e'::[])))))))))))))))),
    (SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('u'::('e'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), (Var
    ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      logicRespPort
      (vector_find (fieldAccessor ('v'::('a'::('l'::('u'::('e'::[]))))))
        (Stdlib.Int.succ (Stdlib.Int.succ 0)) logicRespPort))), value_v)),
    (Return (Const (void, (getDefaultConst void)))))))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('0'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('1'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('2'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('3'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('B'::('i'::('a'::('n'::('c'::('h'::('i'::('A'::('l'::('a'::('r'::('m'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> ReadReg
    (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun m -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (fun total -> Return
    (BinBitBool (wordSz, wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit
    wordSz)), m)), (Var ((SyntaxKind (Bit wordSz)), total))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('t'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('t'::('S'::('i'::('z'::('e'::[])))))))));
    attrType = (ExistT ({ arg = (Bit pTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('p'::('t'::('_'::('s'::('i'::('z'::('e'::('s'::[])))))))), (SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), (fun t1 -> Return (ReadIndex
    (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit pTableIdxSz)), idx)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), t1))))))))) }),
    NilInModule))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val thieleCoreS : modulesS **)

let thieleCoreS =
  getModuleS thieleCore

(** val thieleCoreB : bModule list option **)

let thieleCoreB =
  modulesSToBModules thieleCoreS
