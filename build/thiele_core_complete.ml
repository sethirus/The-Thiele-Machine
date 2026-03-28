
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

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

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val tail_add : int -> int -> int **)

let rec tail_add n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n1 -> tail_add n1 (Stdlib.Int.succ m))
    n0

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n0 m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n1 -> tail_addmul (tail_add m r) n1 m)
    n0

(** val tail_mul : int -> int -> int **)

let tail_mul n0 m =
  tail_addmul 0 n0 m

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
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) (Stdlib.Int.succ n0) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n0

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x :: xs -> if in_dec decA x xs then nodup decA xs else x :: (nodup decA xs)

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n0

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val shiftl : int -> int -> int **)

  let shiftl p n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> p)
      (fun n1 -> iter (fun x -> (fun p->2*p) x) p n1)
      n0

  (** val testbit : int -> int -> bool **)

  let rec testbit p n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n0)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val pred : int -> int **)

  let pred = fun n -> Stdlib.Int.max 0 (n-1)

  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val div2 : int -> int **)

  let div2 n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p -> p)
        (fun p -> p)
        (fun _ -> 0)
        p0)
      n0

  (** val coq_lor : int -> int -> int **)

  let coq_lor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> (Pos.coq_lor p q))
        m)
      n0

  (** val coq_land : int -> int -> int **)

  let coq_land n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Pos.coq_land p q)
        m)
      n0

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.coq_lxor p q)
        m)
      n0

  (** val shiftl : int -> int -> int **)

  let shiftl a n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun a0 -> (Pos.shiftl a0 n0))
      a

  (** val shiftr : int -> int -> int **)

  let shiftr a n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> a)
      (fun p -> Pos.iter div2 a p)
      n0

  (** val testbit : int -> int -> bool **)

  let testbit a n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> false)
      (fun p -> Pos.testbit p n0)
      a

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0

  (** val ones : int -> int **)

  let ones n0 =
    pred (shiftl 1 n0)
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one)
        p)
      n0
  in loop (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n0 =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n0

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

module Z =
 struct
  (** val opp : int -> int **)

  let opp = (~-)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val gtb : int -> int -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val abs_nat : int -> int **)

  let abs_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun p -> Pos.to_nat p)
      z0

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n1 -> (Pos.of_succ_nat n1))
      n0
 end

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val length0 : char list -> int **)

let rec length0 = function
| [] -> 0
| _::s' -> Stdlib.Int.succ (length0 s')

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s0 -> ch :: (list_ascii_of_string s0)

module CertCheck =
 struct
  (** val string_to_list : char list -> char list **)

  let rec string_to_list = function
  | [] -> []
  | c::s' -> c :: (string_to_list s')

  (** val list_to_string : char list -> char list **)

  let rec list_to_string = function
  | [] -> []
  | c :: l' -> c::(list_to_string l')

  (** val ascii_nat : char -> int **)

  let ascii_nat =
    nat_of_ascii

  (** val is_space : char -> bool **)

  let is_space c =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> false)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> false)
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> false)
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> false)
                (fun n5 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> false)
                  (fun n6 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> false)
                    (fun n7 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> false)
                      (fun n8 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> true)
                        (fun n9 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> true)
                          (fun n10 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> false)
                            (fun n11 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> false)
                              (fun n12 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> true)
                                (fun n13 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> false)
                                  (fun n14 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> false)
                                    (fun n15 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> false)
                                      (fun n16 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> false)
                                        (fun n17 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> false)
                                          (fun n18 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> false)
                                            (fun n19 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> false)
                                              (fun n20 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> false)
                                                (fun n21 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> false)
                                                  (fun n22 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ ->
                                                    false)
                                                    (fun n23 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      false)
                                                      (fun n24 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        false)
                                                        (fun n25 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          false)
                                                          (fun n26 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ ->
                                                            false)
                                                            (fun n27 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              false)
                                                              (fun n28 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                false)
                                                                (fun n29 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  false)
                                                                  (fun n30 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun n31 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    true)
                                                                    (fun _ ->
                                                                    false)
                                                                    n31)
                                                                    n30)
                                                                  n29)
                                                                n28)
                                                              n27)
                                                            n26)
                                                          n25)
                                                        n24)
                                                      n23)
                                                    n22)
                                                  n21)
                                                n20)
                                              n19)
                                            n18)
                                          n17)
                                        n16)
                                      n15)
                                    n14)
                                  n13)
                                n12)
                              n11)
                            n10)
                          n9)
                        n8)
                      n7)
                    n6)
                  n5)
                n4)
              n3)
            n2)
          n1)
        n0)
      (ascii_nat c)

  (** val trim_left_list : char list -> char list **)

  let rec trim_left_list l = match l with
  | [] -> []
  | c :: l' -> if is_space c then trim_left_list l' else l

  (** val trim_left : char list -> char list **)

  let trim_left s =
    list_to_string (trim_left_list (string_to_list s))

  (** val split_lines_aux : char list -> char list -> char list list **)

  let rec split_lines_aux l cur =
    match l with
    | [] -> (rev cur) :: []
    | c :: l' ->
      if (=) (ascii_nat c) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ 0))))))))))
      then (rev cur) :: (split_lines_aux l' [])
      else split_lines_aux l' (c :: cur)

  (** val split_lines : char list -> char list list **)

  let split_lines s =
    map list_to_string (split_lines_aux (string_to_list s) [])

  (** val split_ws_aux : char list -> char list -> char list list **)

  let rec split_ws_aux l cur =
    match l with
    | [] -> (match rev cur with
             | [] -> []
             | a :: l0 -> (a :: l0) :: [])
    | c :: l' ->
      if is_space c
      then (match rev cur with
            | [] -> split_ws_aux l' []
            | a :: l0 -> (a :: l0) :: (split_ws_aux l' []))
      else split_ws_aux l' (c :: cur)

  (** val split_ws : char list -> char list list **)

  let split_ws s =
    map list_to_string (split_ws_aux (string_to_list s) [])

  (** val starts_with_char : char -> char list -> bool **)

  let starts_with_char ch s =
    match trim_left s with
    | [] -> false
    | c::_ -> (=) c ch

  (** val is_digit : char -> bool **)

  let is_digit c =
    let n0 = ascii_nat c in
    (&&)
      ((<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))))))))))))))))))) n0)
      ((<=) n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val parse_nat_digits : char list -> int -> int option **)

  let rec parse_nat_digits l acc =
    match l with
    | [] -> Some acc
    | c :: l' ->
      if is_digit c
      then parse_nat_digits l'
             (Nat.add
               (Nat.mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0)))))))))) acc)
               (Nat.sub (ascii_nat c) (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ
                 0))))))))))))))))))))))))))))))))))))))))))))))))))
      else None

  (** val parse_int : char list -> int option **)

  let parse_int s =
    let l = string_to_list (trim_left s) in
    (match l with
     | [] -> None
     | c :: rest ->
       if (=) c
            (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              0))))))))))))))))))))))))))))))))))))))))))))))
       then (match parse_nat_digits rest 0 with
             | Some n0 -> Some (Z.opp (Z.of_nat n0))
             | None -> None)
       else if (=) c
                 (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ (Stdlib.Int.succ
                   0))))))))))))))))))))))))))))))))))))))))))))
            then (match parse_nat_digits rest 0 with
                  | Some n0 -> Some (Z.of_nat n0)
                  | None -> None)
            else (match parse_nat_digits l 0 with
                  | Some n0 -> Some (Z.of_nat n0)
                  | None -> None))

  (** val parse_nat : char list -> int option **)

  let parse_nat s =
    match parse_int s with
    | Some z0 -> if Z.ltb z0 0 then None else Some (Z.abs_nat z0)
    | None -> None

  type dimacs_cnf = { cnf_num_vars : int; cnf_clauses : int list list }

  (** val cnf_num_vars : dimacs_cnf -> int **)

  let cnf_num_vars d =
    d.cnf_num_vars

  (** val cnf_clauses : dimacs_cnf -> int list list **)

  let cnf_clauses d =
    d.cnf_clauses

  (** val take_until_zero : int list -> int list **)

  let take_until_zero zs =
    let rec go l acc =
      match l with
      | [] -> rev acc
      | z0 :: l' -> if Z.eqb z0 0 then rev acc else go l' (z0 :: acc)
    in go zs []

  (** val parse_clause_tokens : char list list -> int list option **)

  let parse_clause_tokens toks =
    let ints =
      let rec go ts acc =
        match ts with
        | [] -> Some (rev acc)
        | t :: ts' ->
          (match parse_int t with
           | Some z0 -> go ts' (z0 :: acc)
           | None -> None)
      in go toks []
    in
    (match ints with
     | Some zs -> Some (take_until_zero zs)
     | None -> None)

  (** val parse_dimacs : char list -> dimacs_cnf option **)

  let parse_dimacs text =
    let lines = split_lines text in
    let rec go ls num_vars clauses =
      match ls with
      | [] ->
        (match num_vars with
         | Some nv -> Some { cnf_num_vars = nv; cnf_clauses = (rev clauses) }
         | None -> None)
      | line :: ls' ->
        let line' = trim_left line in
        (match line' with
         | [] -> go ls' num_vars clauses
         | c::_ ->
           if (=) c
                (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ
                  0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           then go ls' num_vars clauses
           else if (=) c
                     (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ
                       0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                then let toks = split_ws line' in
                     (match toks with
                      | [] -> None
                      | _ :: l ->
                        (match l with
                         | [] -> None
                         | _ :: l0 ->
                           (match l0 with
                            | [] -> None
                            | nv :: l1 ->
                              (match l1 with
                               | [] -> None
                               | _ :: _ ->
                                 (match parse_nat nv with
                                  | Some nv' -> go ls' (Some nv') clauses
                                  | None -> None)))))
                else (match parse_clause_tokens (split_ws line') with
                      | Some cl -> go ls' num_vars (cl :: clauses)
                      | None -> None))
    in go lines None []

  (** val lookup_bool : int -> (int * bool) list -> bool option **)

  let rec lookup_bool x = function
  | [] -> None
  | p :: m' -> let (k, v) = p in if (=) k x then Some v else lookup_bool x m'

  (** val insert_bool :
      int -> bool -> (int * bool) list -> (int * bool) list **)

  let insert_bool x v m =
    (x, v) :: m

  (** val remove_prefix_v : char list -> char list **)

  let remove_prefix_v s = match s with
  | [] -> s
  | c::rest ->
    if (||)
         ((=) c
           (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ
             0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ((=) c
           (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ (Stdlib.Int.succ
             0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    then rest
    else s

  (** val split_on_eq_aux :
      char list -> char list -> (char list * char list) option **)

  let rec split_on_eq_aux l acc =
    match l with
    | [] -> None
    | c :: l' ->
      if (=) (ascii_nat c) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
           (Stdlib.Int.succ
           0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      then Some ((rev acc), l')
      else split_on_eq_aux l' (c :: acc)

  (** val split_on_eq : char list -> (char list * char list) option **)

  let split_on_eq s =
    match split_on_eq_aux (string_to_list s) [] with
    | Some p ->
      let (l1, l2) = p in Some ((list_to_string l1), (list_to_string l2))
    | None -> None

  (** val value_is_false : char list -> bool **)

  let value_is_false s =
    let t = trim_left s in
    (||) (eqb0 t ('0'::[]))
      ((||) (eqb0 t ('f'::('a'::('l'::('s'::('e'::[])))))) (eqb0 t ('f'::[])))

  (** val parse_assignment_token : char list -> (int * bool) option **)

  let parse_assignment_token tok =
    if eqb0 tok ('0'::[])
    then None
    else (match split_on_eq tok with
          | Some p ->
            let (lhs, rhs) = p in
            (match parse_nat (remove_prefix_v lhs) with
             | Some var -> Some (var, (negb (value_is_false rhs)))
             | None -> None)
          | None ->
            (match parse_int tok with
             | Some lit ->
               if Z.eqb lit 0
               then None
               else Some ((Z.abs_nat lit), (Z.gtb lit 0))
             | None -> None))

  (** val parse_assignment : char list -> (int * bool) list option **)

  let parse_assignment text =
    let toks = split_ws text in
    let rec go ts acc =
      match ts with
      | [] -> Some acc
      | t :: ts' ->
        (match parse_assignment_token t with
         | Some p -> let (var, v) = p in go ts' (insert_bool var v acc)
         | None -> go ts' acc)
    in go toks []

  (** val clause_satisfied : (int * bool) list -> int list -> bool **)

  let rec clause_satisfied asgn = function
  | [] -> false
  | lit :: lits' ->
    let var = Z.abs_nat lit in
    (match lookup_bool var asgn with
     | Some b ->
       if eqb b (Z.gtb lit 0) then true else clause_satisfied asgn lits'
     | None -> false)

  (** val check_model : char list -> char list -> bool **)

  let check_model cnf_text assignment_text =
    match parse_dimacs cnf_text with
    | Some cnf ->
      (match parse_assignment assignment_text with
       | Some asgn ->
         if Nat.ltb (length asgn) cnf.cnf_num_vars
         then false
         else forallb (clause_satisfied asgn) cnf.cnf_clauses
       | None -> false)
    | None -> false

  (** val assoc_remove :
      int -> (int * int list) list -> (int * int list) list **)

  let assoc_remove k db =
    filter (fun kv -> negb ((=) (fst kv) k)) db

  (** val db_clauses : (int * int list) list -> int list list **)

  let db_clauses db =
    map snd db

  (** val eval_clause : (int * bool) list -> int list -> bool * int list **)

  let eval_clause asgn cl =
    let rec go lits undec =
      match lits with
      | [] -> (false, (rev undec))
      | lit :: lits' ->
        let var = Z.abs_nat lit in
        (match lookup_bool var asgn with
         | Some b ->
           if eqb b (Z.gtb lit 0) then (true, []) else go lits' undec
         | None -> go lits' (lit :: undec))
    in go cl []

  (** val unit_conflict_fuel :
      int -> int -> int list list -> (int * bool) list -> int list -> bool **)

  let rec unit_conflict_fuel fuel num_vars clauses asgn queue =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun fuel' ->
      match queue with
      | [] -> false
      | lit :: queue' ->
        let var = Z.abs_nat lit in
        let value = Z.gtb lit 0 in
        (match lookup_bool var asgn with
         | Some b ->
           if eqb b value
           then unit_conflict_fuel fuel' num_vars clauses asgn queue'
           else true
         | None ->
           let asgn' = insert_bool var value asgn in
           let scan =
             let rec scan cls q =
               match cls with
               | [] -> Some q
               | cl :: cls' ->
                 let (sat, undec) = eval_clause asgn' cl in
                 if sat
                 then scan cls' q
                 else (match undec with
                       | [] -> None
                       | u :: l ->
                         (match l with
                          | [] -> scan cls' (u :: q)
                          | _ :: _ -> scan cls' q))
             in scan
           in
           (match scan clauses queue' with
            | Some q' -> unit_conflict_fuel fuel' num_vars clauses asgn' q'
            | None -> true)))
      fuel

  (** val unit_conflict : int -> int list list -> int list -> bool **)

  let unit_conflict num_vars clauses assumptions =
    let unit_lits =
      fold_right (fun cl acc ->
        match cl with
        | [] -> acc
        | u :: l -> (match l with
                     | [] -> u :: acc
                     | _ :: _ -> acc)) [] clauses
    in
    let queue = app assumptions unit_lits in
    let fuel =
      add (add num_vars (length queue)) (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0))))))))))
    in
    unit_conflict_fuel fuel num_vars clauses [] queue

  (** val verify_rup_clause :
      int -> (int * int list) list -> int list -> bool **)

  let verify_rup_clause num_vars db clause =
    unit_conflict num_vars (db_clauses db) (map Z.opp clause)

  type lrat_step = { lrat_id : int; lrat_clause : int list;
                     lrat_deletions : int list; lrat_is_delete : bool }

  (** val lrat_id : lrat_step -> int **)

  let lrat_id l =
    l.lrat_id

  (** val lrat_clause : lrat_step -> int list **)

  let lrat_clause l =
    l.lrat_clause

  (** val lrat_deletions : lrat_step -> int list **)

  let lrat_deletions l =
    l.lrat_deletions

  (** val lrat_is_delete : lrat_step -> bool **)

  let lrat_is_delete l =
    l.lrat_is_delete

  (** val parse_nat_list : char list list -> int list option **)

  let parse_nat_list toks =
    let rec go ts acc =
      match ts with
      | [] -> Some (rev acc)
      | t :: ts' ->
        (match parse_nat t with
         | Some n0 -> if (=) n0 0 then Some (rev acc) else go ts' (n0 :: acc)
         | None -> None)
    in go toks []

  (** val parse_z_list : char list list -> int list option **)

  let parse_z_list toks =
    let rec go ts acc =
      match ts with
      | [] -> Some (rev acc)
      | t :: ts' ->
        (match parse_int t with
         | Some z0 ->
           if Z.eqb z0 0 then Some (rev acc) else go ts' (z0 :: acc)
         | None -> None)
    in go toks []

  (** val drop_until_zero : char list list -> char list list **)

  let rec drop_until_zero = function
  | [] -> []
  | t :: ts' -> if eqb0 t ('0'::[]) then ts' else drop_until_zero ts'

  (** val parse_lrat_line : char list -> lrat_step option **)

  let parse_lrat_line line =
    let t = trim_left line in
    if eqb0 t []
    then None
    else if starts_with_char
              (ascii_of_nat (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ
                0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              t
         then None
         else let toks = split_ws t in
              (match toks with
               | [] -> None
               | first :: rest ->
                 if eqb0 first ('d'::[])
                 then (match parse_nat_list rest with
                       | Some dels ->
                         Some { lrat_id = 0; lrat_clause = [];
                           lrat_deletions = dels; lrat_is_delete = true }
                       | None -> None)
                 else (match parse_nat first with
                       | Some cid ->
                         (match parse_z_list rest with
                          | Some clause ->
                            let after_clause = drop_until_zero rest in
                            let after_hints = drop_until_zero after_clause in
                            (match parse_nat_list after_hints with
                             | Some dels ->
                               Some { lrat_id = cid; lrat_clause = clause;
                                 lrat_deletions = dels; lrat_is_delete =
                                 false }
                             | None -> None)
                          | None -> None)
                       | None -> None))

  (** val build_initial_db : int list list -> int -> (int * int list) list **)

  let rec build_initial_db clauses idx =
    match clauses with
    | [] -> []
    | cl :: cls -> (idx, cl) :: (build_initial_db cls (Stdlib.Int.succ idx))

  (** val apply_deletions :
      (int * int list) list -> int list -> (int * int list) list **)

  let rec apply_deletions db = function
  | [] -> db
  | d :: ds -> apply_deletions (assoc_remove d db) ds

  (** val check_lrat_lines :
      int -> char list list -> (int * int list) list -> bool -> bool **)

  let rec check_lrat_lines num_vars lines db derived_empty =
    match lines with
    | [] -> derived_empty
    | line :: lines' ->
      (match parse_lrat_line line with
       | Some st ->
         if st.lrat_is_delete
         then check_lrat_lines num_vars lines'
                (apply_deletions db st.lrat_deletions) derived_empty
         else if verify_rup_clause num_vars db st.lrat_clause
              then let db' = (st.lrat_id,
                     st.lrat_clause) :: (apply_deletions db st.lrat_deletions)
                   in
                   let derived_empty' =
                     (||) derived_empty ((=) (length st.lrat_clause) 0)
                   in
                   check_lrat_lines num_vars lines' db' derived_empty'
              else false
       | None -> check_lrat_lines num_vars lines' db derived_empty)

  (** val check_lrat : char list -> char list -> bool **)

  let check_lrat cnf_text proof_text =
    match parse_dimacs cnf_text with
    | Some cnf ->
      let db = build_initial_db cnf.cnf_clauses (Stdlib.Int.succ 0) in
      check_lrat_lines cnf.cnf_num_vars (split_lines proof_text) db false
    | None -> false
 end

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

(** val nat_list_mem : int -> int list -> bool **)

let rec nat_list_mem x = function
| [] -> false
| y :: ys -> if (=) x y then true else nat_list_mem x ys

(** val normalize_region : int list -> int list **)

let normalize_region region =
  nodup (=) region

(** val nat_list_subset : int list -> int list -> bool **)

let nat_list_subset xs ys =
  forallb (fun x -> nat_list_mem x ys) xs

(** val nat_list_disjoint : int list -> int list -> bool **)

let nat_list_disjoint xs ys =
  forallb (fun x -> negb (nat_list_mem x ys)) xs

(** val nat_list_union : int list -> int list -> int list **)

let nat_list_union xs ys =
  normalize_region (app xs ys)

(** val nat_list_eq : int list -> int list -> bool **)

let nat_list_eq xs ys =
  (&&) (nat_list_subset xs ys) (nat_list_subset ys xs)

type moduleState = { module_region : int list; module_axioms : axiomSet;
                     module_mu_tensor : int list }

(** val module_mu_tensor_default : int list **)

let module_mu_tensor_default =
  repeat 0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))

(** val mk_module_state : int list -> axiomSet -> moduleState **)

let mk_module_state region axioms =
  { module_region = region; module_axioms = axioms; module_mu_tensor =
    module_mu_tensor_default }

(** val list_update_at : int list -> int -> int -> int list **)

let rec list_update_at l k v =
  match l with
  | [] -> []
  | h :: t ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> v :: t)
       (fun i -> h :: (list_update_at t i v))
       k)

(** val normalize_module : moduleState -> moduleState **)

let normalize_module m =
  { module_region = (normalize_region m.module_region); module_axioms =
    m.module_axioms; module_mu_tensor = m.module_mu_tensor }

type morphismID = int

type couplingData = { coupling_pairs : (int * int) list;
                      coupling_label : char list }

type morphismState = { morph_source : moduleID; morph_target : moduleID;
                       morph_coupling : couplingData; morph_is_identity : 
                       bool }

(** val nat_pair_eq_dec : (int * int) -> (int * int) -> bool **)

let nat_pair_eq_dec p1 p2 =
  let (a, b) = p1 in let (n0, n1) = p2 in if (=) a n0 then (=) b n1 else false

(** val normalize_coupling : couplingData -> couplingData **)

let normalize_coupling c =
  { coupling_pairs = (nodup nat_pair_eq_dec c.coupling_pairs);
    coupling_label = c.coupling_label }

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID * moduleState) list;
                        pg_next_morph_id : morphismID;
                        pg_morphisms : (morphismID * morphismState) list }

(** val graph_lookup_modules :
    (moduleID * moduleState) list -> moduleID -> moduleState option **)

let rec graph_lookup_modules modules mid =
  match modules with
  | [] -> None
  | p :: rest ->
    let (id, m) = p in
    if (=) id mid then Some m else graph_lookup_modules rest mid

(** val graph_lookup : partitionGraph -> moduleID -> moduleState option **)

let graph_lookup g mid =
  graph_lookup_modules g.pg_modules mid

(** val graph_insert_modules :
    (moduleID * moduleState) list -> moduleID -> moduleState ->
    (moduleID * moduleState) list **)

let rec graph_insert_modules modules mid m =
  match modules with
  | [] -> (mid, m) :: []
  | p :: rest ->
    let (id, existing) = p in
    if (=) id mid
    then (mid, m) :: rest
    else (id, existing) :: (graph_insert_modules rest mid m)

(** val graph_update :
    partitionGraph -> moduleID -> moduleState -> partitionGraph **)

let graph_update g mid m =
  { pg_next_id = g.pg_next_id; pg_modules =
    (graph_insert_modules g.pg_modules mid (normalize_module m));
    pg_next_morph_id = g.pg_next_morph_id; pg_morphisms = g.pg_morphisms }

(** val graph_remove_modules :
    (moduleID * moduleState) list -> moduleID -> ((moduleID * moduleState)
    list * moduleState) option **)

let rec graph_remove_modules modules mid =
  match modules with
  | [] -> None
  | p :: rest ->
    let (id, m) = p in
    if (=) id mid
    then Some (rest, m)
    else (match graph_remove_modules rest mid with
          | Some p0 ->
            let (rest', removed) = p0 in Some (((id, m) :: rest'), removed)
          | None -> None)

(** val graph_remove :
    partitionGraph -> moduleID -> (partitionGraph * moduleState) option **)

let graph_remove g mid =
  match graph_remove_modules g.pg_modules mid with
  | Some p ->
    let (modules', removed) = p in
    Some ({ pg_next_id = g.pg_next_id; pg_modules = modules';
    pg_next_morph_id = g.pg_next_morph_id; pg_morphisms = g.pg_morphisms },
    removed)
  | None -> None

(** val graph_add_module :
    partitionGraph -> int list -> axiomSet -> partitionGraph * moduleID **)

let graph_add_module g region axioms =
  let module0 = normalize_module (mk_module_state region axioms) in
  let mid = g.pg_next_id in
  ({ pg_next_id = (Stdlib.Int.succ mid); pg_modules = ((mid,
  module0) :: g.pg_modules); pg_next_morph_id = g.pg_next_morph_id;
  pg_morphisms = g.pg_morphisms }, mid)

(** val graph_find_region_modules :
    (moduleID * moduleState) list -> int list -> moduleID option **)

let rec graph_find_region_modules modules region =
  match modules with
  | [] -> None
  | p :: rest ->
    let (id, m) = p in
    if nat_list_eq m.module_region region
    then Some id
    else graph_find_region_modules rest region

(** val graph_find_region : partitionGraph -> int list -> moduleID option **)

let graph_find_region g region =
  graph_find_region_modules g.pg_modules (normalize_region region)

(** val graph_add_axiom :
    partitionGraph -> moduleID -> vMAxiom -> partitionGraph **)

let graph_add_axiom g mid ax =
  match graph_lookup g mid with
  | Some m ->
    let updated = { module_region = m.module_region; module_axioms =
      (app m.module_axioms (ax :: [])); module_mu_tensor =
      m.module_mu_tensor }
    in
    graph_update g mid updated
  | None -> g

(** val graph_add_axioms :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_add_axioms g mid axs =
  fold_left (fun acc ax -> graph_add_axiom acc mid ax) axs g

(** val graph_update_module_tensor :
    partitionGraph -> moduleID -> int -> int -> partitionGraph **)

let graph_update_module_tensor g mid k value =
  match graph_lookup g mid with
  | Some m ->
    let updated = { module_region = m.module_region; module_axioms =
      m.module_axioms; module_mu_tensor =
      (list_update_at m.module_mu_tensor k value) }
    in
    graph_update g mid updated
  | None -> g

(** val graph_record_discovery :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_record_discovery =
  graph_add_axioms

(** val relational_compose :
    (int * int) list -> (int * int) list -> (int * int) list **)

let relational_compose r1 r2 =
  flat_map (fun pat ->
    let (a, b) = pat in
    map (fun pat0 -> let (_, c) = pat0 in (a, c))
      (filter (fun pat0 -> let (b', _) = pat0 in (=) b b') r2)) r1

(** val graph_lookup_morphism_list :
    (morphismID * morphismState) list -> morphismID -> morphismState option **)

let rec graph_lookup_morphism_list morphisms morph_id =
  match morphisms with
  | [] -> None
  | p :: rest ->
    let (id, ms) = p in
    if (=) id morph_id
    then Some ms
    else graph_lookup_morphism_list rest morph_id

(** val graph_lookup_morphism :
    partitionGraph -> morphismID -> morphismState option **)

let graph_lookup_morphism g morph_id =
  graph_lookup_morphism_list g.pg_morphisms morph_id

(** val graph_add_morphism :
    partitionGraph -> moduleID -> moduleID -> couplingData -> bool ->
    partitionGraph * morphismID **)

let graph_add_morphism g src dst c is_id =
  let new_id = g.pg_next_morph_id in
  let ms = { morph_source = src; morph_target = dst; morph_coupling =
    (normalize_coupling c); morph_is_identity = is_id }
  in
  ({ pg_next_id = g.pg_next_id; pg_modules = g.pg_modules; pg_next_morph_id =
  (Stdlib.Int.succ new_id); pg_morphisms = ((new_id,
  ms) :: g.pg_morphisms) }, new_id)

(** val graph_add_identity :
    partitionGraph -> moduleID -> (partitionGraph * morphismID) option **)

let graph_add_identity g mid =
  match graph_lookup g mid with
  | Some m ->
    let diag = map (fun x -> (x, x)) m.module_region in
    let c = { coupling_pairs = diag; coupling_label = ('i'::('d'::[])) } in
    Some (graph_add_morphism g mid mid c true)
  | None -> None

(** val graph_delete_morphism :
    partitionGraph -> morphismID -> partitionGraph option **)

let graph_delete_morphism g morph_id =
  if existsb (fun pat -> let (id, _) = pat in (=) id morph_id) g.pg_morphisms
  then Some { pg_next_id = g.pg_next_id; pg_modules = g.pg_modules;
         pg_next_morph_id = g.pg_next_morph_id; pg_morphisms =
         (filter (fun pat -> let (id, _) = pat in negb ((=) id morph_id))
           g.pg_morphisms) }
  else None

(** val graph_compose_morphisms :
    partitionGraph -> morphismID -> morphismID ->
    (partitionGraph * morphismID) option **)

let graph_compose_morphisms g m1 m2 =
  match graph_lookup_morphism g m1 with
  | Some f ->
    (match graph_lookup_morphism g m2 with
     | Some h ->
       if (=) f.morph_target h.morph_source
       then let composed_pairs =
              relational_compose f.morph_coupling.coupling_pairs
                h.morph_coupling.coupling_pairs
            in
            let c = { coupling_pairs = composed_pairs; coupling_label =
              (append f.morph_coupling.coupling_label
                (append (';'::[]) h.morph_coupling.coupling_label)) }
            in
            Some (graph_add_morphism g f.morph_source h.morph_target c false)
       else None
     | None -> None)
  | None -> None

(** val graph_tensor_morphisms :
    partitionGraph -> morphismID -> morphismID ->
    (partitionGraph * morphismID) option **)

let graph_tensor_morphisms g f_id g_id =
  match graph_lookup_morphism g f_id with
  | Some f ->
    (match graph_lookup_morphism g g_id with
     | Some h ->
       (match graph_lookup g f.morph_source with
        | Some a_mod ->
          (match graph_lookup g f.morph_target with
           | Some b_mod ->
             (match graph_lookup g h.morph_source with
              | Some c_mod ->
                (match graph_lookup g h.morph_target with
                 | Some d_mod ->
                   if (&&)
                        (nat_list_disjoint a_mod.module_region
                          c_mod.module_region)
                        (nat_list_disjoint b_mod.module_region
                          d_mod.module_region)
                   then let ac_region =
                          nat_list_union a_mod.module_region
                            c_mod.module_region
                        in
                        let bd_region =
                          nat_list_union b_mod.module_region
                            d_mod.module_region
                        in
                        (match graph_find_region g ac_region with
                         | Some ac_id ->
                           (match graph_find_region g bd_region with
                            | Some bd_id ->
                              let tensor_pairs =
                                app f.morph_coupling.coupling_pairs
                                  h.morph_coupling.coupling_pairs
                              in
                              let c = { coupling_pairs = tensor_pairs;
                                coupling_label =
                                (append f.morph_coupling.coupling_label
                                  (append ('\226'::('\138'::('\151'::[])))
                                    h.morph_coupling.coupling_label)) }
                              in
                              Some (graph_add_morphism g ac_id bd_id c false)
                            | None -> None)
                         | None -> None)
                   else None
                 | None -> None)
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  | None -> None

type cSRState = { csr_cert_addr : int; csr_status : int; csr_err : int;
                  csr_heap_base : int }

(** val csr_set_status : cSRState -> int -> cSRState **)

let csr_set_status csrs status =
  { csr_cert_addr = csrs.csr_cert_addr; csr_status = status; csr_err =
    csrs.csr_err; csr_heap_base = csrs.csr_heap_base }

(** val csr_set_err : cSRState -> int -> cSRState **)

let csr_set_err csrs err =
  { csr_cert_addr = csrs.csr_cert_addr; csr_status = csrs.csr_status;
    csr_err = err; csr_heap_base = csrs.csr_heap_base }

(** val csr_set_cert_addr : cSRState -> int -> cSRState **)

let csr_set_cert_addr csrs addr =
  { csr_cert_addr = addr; csr_status = csrs.csr_status; csr_err =
    csrs.csr_err; csr_heap_base = csrs.csr_heap_base }

type witnessCounts = { wc_same_00 : int; wc_diff_00 : int; wc_same_01 : 
                       int; wc_diff_01 : int; wc_same_10 : int;
                       wc_diff_10 : int; wc_same_11 : int; wc_diff_11 : 
                       int }

type vMState = { vm_graph : partitionGraph; vm_csrs : cSRState;
                 vm_regs : int list; vm_mem : int list; vm_pc : int;
                 vm_mu : int; vm_mu_tensor : int list; vm_err : bool;
                 vm_logic_acc : int; vm_mstatus : int;
                 vm_witness : witnessCounts; vm_certified : bool }

(** val word64_mask : int **)

let word64_mask =
  N.ones ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1))))))

(** val word64 : int -> int **)

let word64 x =
  N.to_nat (N.coq_land (N.of_nat x) word64_mask)

(** val word64_xor : int -> int -> int **)

let word64_xor a b =
  word64 (N.to_nat (N.coq_lxor (N.of_nat a) (N.of_nat b)))

(** val word64_add : int -> int -> int **)

let word64_add a b =
  word64 (add a b)

(** val word64_sub : int -> int -> int **)

let word64_sub a b =
  N.to_nat
    (N.coq_land
      (N.add (N.of_nat (word64 a))
        (N.add (N.coq_lxor (N.of_nat (word64 b)) word64_mask) 1)) word64_mask)

(** val popcount_upto : int -> int -> int **)

let rec popcount_upto bits x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun bits' ->
    add (if N.testbit x (N.of_nat bits') then Stdlib.Int.succ 0 else 0)
      (popcount_upto bits' x))
    bits

(** val word64_popcount : int -> int **)

let word64_popcount x =
  popcount_upto (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (N.coq_land (N.of_nat x) word64_mask)

(** val word64_and : int -> int -> int **)

let word64_and a b =
  N.to_nat (N.coq_land (N.coq_land (N.of_nat a) (N.of_nat b)) word64_mask)

(** val word64_or : int -> int -> int **)

let word64_or a b =
  N.to_nat
    (N.coq_lor (N.coq_land (N.of_nat a) word64_mask)
      (N.coq_land (N.of_nat b) word64_mask))

(** val word64_shl : int -> int -> int **)

let word64_shl a b =
  word64
    (N.to_nat
      (N.shiftl (N.of_nat a)
        (N.of_nat
          (Nat.modulo b (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val word64_shr : int -> int -> int **)

let word64_shr a b =
  N.to_nat
    (N.shiftr (N.coq_land (N.of_nat a) word64_mask)
      (N.of_nat
        (Nat.modulo b (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val word64_mul : int -> int -> int **)

let word64_mul a b =
  word64 (mul a b)

(** val rEG_COUNT : int **)

let rEG_COUNT =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))

(** val mEM_SIZE : int **)

let mEM_SIZE =
  of_num_uint (UIntDecimal (D6 (D5 (D5 (D3 (D6 Nil))))))

(** val reg_index : int -> int **)

let reg_index r =
  Nat.modulo r rEG_COUNT

(** val mem_index : int -> int **)

let mem_index a =
  Nat.modulo a mEM_SIZE

(** val read_reg : vMState -> int -> int **)

let read_reg s r =
  nth (reg_index r) s.vm_regs 0

(** val write_reg : vMState -> int -> int -> int list **)

let write_reg s r v =
  let idx = reg_index r in
  app (firstn idx s.vm_regs)
    (app ((word64 v) :: []) (skipn (Stdlib.Int.succ idx) s.vm_regs))

(** val read_mem : vMState -> int -> int **)

let read_mem s a =
  nth (mem_index a) s.vm_mem 0

(** val write_mem : vMState -> int -> int -> int list **)

let write_mem s a v =
  let idx = mem_index a in
  app (firstn idx s.vm_mem)
    (app ((word64 v) :: []) (skipn (Stdlib.Int.succ idx) s.vm_mem))

(** val swap_regs : int list -> int -> int -> int list **)

let swap_regs regs a b =
  let a_idx = Nat.modulo a rEG_COUNT in
  let b_idx = Nat.modulo b rEG_COUNT in
  let va = nth a_idx regs 0 in
  let vb = nth b_idx regs 0 in
  let regs' =
    app (firstn a_idx regs)
      (app (vb :: []) (skipn (Stdlib.Int.succ a_idx) regs))
  in
  app (firstn b_idx regs')
    (app (va :: []) (skipn (Stdlib.Int.succ b_idx) regs'))

(** val ascii_checksum : char list -> int **)

let ascii_checksum s =
  fold_right (fun ch acc -> add (nat_of_ascii ch) acc) 0
    (list_ascii_of_string s)

(** val module_tensor_entry : vMState -> moduleID -> int -> int -> int **)

let module_tensor_entry s m i j =
  match graph_lookup s.vm_graph m with
  | Some ms ->
    nth
      (add
        (mul i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0))))) j) ms.module_mu_tensor 0
  | None -> 0

(** val graph_pnew :
    partitionGraph -> int list -> partitionGraph * moduleID **)

let graph_pnew g region =
  let normalized = normalize_region region in
  (match graph_find_region g normalized with
   | Some existing -> (g, existing)
   | None -> graph_add_module g normalized [])

(** val partition_valid : int list -> int list -> int list -> bool **)

let partition_valid original left right =
  (&&)
    ((&&)
      ((&&) (nat_list_subset left original) (nat_list_subset right original))
      (nat_list_disjoint left right))
    (nat_list_subset original (nat_list_union left right))

(** val graph_psplit :
    partitionGraph -> moduleID -> int list -> int list ->
    ((partitionGraph * moduleID) * moduleID) option **)

let graph_psplit g mid left right =
  match graph_lookup g mid with
  | Some m ->
    let axioms = m.module_axioms in
    let original = m.module_region in
    let left_norm = normalize_region left in
    let right_norm = normalize_region right in
    if (||) ((=) (length left_norm) 0) ((=) (length right_norm) 0)
    then let (g', empty_id) = graph_add_module g [] [] in
         Some ((g', mid), empty_id)
    else if partition_valid original left_norm right_norm
         then (match graph_remove g mid with
               | Some p ->
                 let (g_removed, _) = p in
                 let (g_left, left_id) =
                   graph_add_module g_removed left_norm axioms
                 in
                 let (g_right, right_id) =
                   graph_add_module g_left right_norm axioms
                 in
                 Some ((g_right, left_id), right_id)
               | None -> None)
         else None
  | None -> None

(** val graph_pmerge :
    partitionGraph -> moduleID -> moduleID -> (partitionGraph * moduleID)
    option **)

let graph_pmerge g m1 m2 =
  if (=) m1 m2
  then None
  else (match graph_remove g m1 with
        | Some p ->
          let (g1, mod1) = p in
          (match graph_remove g1 m2 with
           | Some p0 ->
             let (g2, mod2) = p0 in
             if negb (nat_list_disjoint mod1.module_region mod2.module_region)
             then None
             else let union =
                    nat_list_union mod1.module_region mod2.module_region
                  in
                  let combined_axioms =
                    app mod1.module_axioms mod2.module_axioms
                  in
                  (match graph_find_region g2 union with
                   | Some existing ->
                     (match graph_lookup g2 existing with
                      | Some existing_mod ->
                        let updated = { module_region =
                          existing_mod.module_region; module_axioms =
                          (app existing_mod.module_axioms combined_axioms);
                          module_mu_tensor = existing_mod.module_mu_tensor }
                        in
                        Some ((graph_update g2 existing updated), existing)
                      | None -> None)
                   | None -> Some (graph_add_module g2 union combined_axioms))
           | None -> None)
        | None -> None)

type lassert_certificate =
| Lassert_cert_unsat of char list
| Lassert_cert_sat of char list

type vm_instruction =
| Instr_pnew of int list * int
| Instr_psplit of moduleID * int list * int list * int
| Instr_pmerge of moduleID * moduleID * int
| Instr_lassert of moduleID * char list * lassert_certificate * int
| Instr_ljoin of char list * char list * int
| Instr_mdlacc of moduleID * int
| Instr_pdiscover of moduleID * vMAxiom list * int
| Instr_xfer of int * int * int
| Instr_load_imm of int * int * int
| Instr_load of int * int * int
| Instr_store of int * int * int
| Instr_add of int * int * int * int
| Instr_sub of int * int * int * int
| Instr_jump of int * int
| Instr_jnez of int * int * int
| Instr_call of int * int
| Instr_ret of int
| Instr_chsh_trial of int * int * int * int * int
| Instr_xor_load of int * int * int
| Instr_xor_add of int * int * int
| Instr_xor_swap of int * int * int
| Instr_xor_rank of int * int * int
| Instr_emit of moduleID * char list * int
| Instr_reveal of moduleID * int * char list * int
| Instr_oracle_halts of char list * int
| Instr_halt of int
| Instr_checkpoint of char list * int
| Instr_read_port of int * int * int * int * int
| Instr_write_port of int * int * int
| Instr_heap_load of int * int * int
| Instr_heap_store of int * int * int
| Instr_certify of int
| Instr_and of int * int * int * int
| Instr_or of int * int * int * int
| Instr_shl of int * int * int * int
| Instr_shr of int * int * int * int
| Instr_mul of int * int * int * int
| Instr_lui of int * int * int
| Instr_tensor_set of moduleID * int * int * int * int
| Instr_tensor_get of int * moduleID * int * int * int
| Instr_morph of int * moduleID * moduleID * int * int
| Instr_compose of int * morphismID * morphismID * int
| Instr_morph_id of int * moduleID * int
| Instr_morph_delete of morphismID * int
| Instr_morph_assert of morphismID * char list * char list * int
| Instr_morph_tensor of int * morphismID * morphismID * int
| Instr_morph_get of int * morphismID * int * int

(** val instruction_cost : vm_instruction -> int **)

let instruction_cost = function
| Instr_pnew (_, cost) -> cost
| Instr_psplit (_, _, _, cost) -> cost
| Instr_pmerge (_, _, cost) -> cost
| Instr_lassert (_, formula, _, cost) ->
  add
    (mul (length0 formula) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ cost)
| Instr_ljoin (_, _, cost) -> Stdlib.Int.succ cost
| Instr_mdlacc (_, cost) -> cost
| Instr_pdiscover (_, _, cost) -> cost
| Instr_xfer (_, _, cost) -> cost
| Instr_load_imm (_, _, cost) -> cost
| Instr_load (_, _, cost) -> cost
| Instr_store (_, _, cost) -> cost
| Instr_add (_, _, _, cost) -> cost
| Instr_sub (_, _, _, cost) -> cost
| Instr_jump (_, cost) -> cost
| Instr_jnez (_, _, cost) -> cost
| Instr_call (_, cost) -> cost
| Instr_ret cost -> cost
| Instr_chsh_trial (_, _, _, _, cost) -> cost
| Instr_xor_load (_, _, cost) -> cost
| Instr_xor_add (_, _, cost) -> cost
| Instr_xor_swap (_, _, cost) -> cost
| Instr_xor_rank (_, _, cost) -> cost
| Instr_emit (_, _, cost) -> Stdlib.Int.succ cost
| Instr_reveal (_, _, _, cost) -> Stdlib.Int.succ cost
| Instr_oracle_halts (_, cost) -> cost
| Instr_halt cost -> cost
| Instr_checkpoint (_, cost) -> cost
| Instr_read_port (_, _, _, _, cost) -> Stdlib.Int.succ cost
| Instr_write_port (_, _, cost) -> cost
| Instr_heap_load (_, _, cost) -> cost
| Instr_heap_store (_, _, cost) -> cost
| Instr_certify cost -> Stdlib.Int.succ cost
| Instr_and (_, _, _, cost) -> cost
| Instr_or (_, _, _, cost) -> cost
| Instr_shl (_, _, _, cost) -> cost
| Instr_shr (_, _, _, cost) -> cost
| Instr_mul (_, _, _, cost) -> cost
| Instr_lui (_, _, cost) -> cost
| Instr_tensor_set (_, _, _, _, cost) -> cost
| Instr_tensor_get (_, _, _, _, cost) -> cost
| Instr_morph (_, _, _, _, cost) -> cost
| Instr_compose (_, _, _, cost) -> cost
| Instr_morph_id (_, _, cost) -> cost
| Instr_morph_delete (_, cost) -> cost
| Instr_morph_assert (_, _, _, cost) -> Stdlib.Int.succ cost
| Instr_morph_tensor (_, _, _, cost) -> cost
| Instr_morph_get (_, _, _, cost) -> cost

(** val is_cert_setterb : vm_instruction -> bool **)

let is_cert_setterb = function
| Instr_lassert (_, _, _, _) -> true
| Instr_ljoin (_, _, _) -> true
| Instr_emit (_, _, _) -> true
| Instr_reveal (_, _, _, _) -> true
| Instr_read_port (_, _, _, _, _) -> true
| Instr_certify _ -> true
| Instr_morph_assert (_, _, _, _) -> true
| _ -> false

(** val is_bit : int -> bool **)

let is_bit n0 =
  (||) ((=) n0 0) ((=) n0 (Stdlib.Int.succ 0))

(** val chsh_bits_ok : int -> int -> int -> int -> bool **)

let chsh_bits_ok x y a b =
  (&&) ((&&) (is_bit x) (is_bit y)) ((&&) (is_bit a) (is_bit b))

(** val apply_cost : vMState -> vm_instruction -> int **)

let apply_cost s instr =
  add s.vm_mu (instruction_cost instr)

(** val latch_err : vMState -> bool -> bool **)

let latch_err s flag =
  (||) flag s.vm_err

(** val vm_mu_tensor_add_at : vMState -> int -> int -> int list **)

let vm_mu_tensor_add_at s k delta =
  let old = nth k s.vm_mu_tensor 0 in
  list_update_at s.vm_mu_tensor k (add old delta)

(** val record_trial :
    witnessCounts -> int -> int -> int -> int -> witnessCounts **)

let record_trial wc x y a b =
  let same = (=) a b in
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ ->
       if same
       then { wc_same_00 = (Stdlib.Int.succ wc.wc_same_00); wc_diff_00 =
              wc.wc_diff_00; wc_same_01 = wc.wc_same_01; wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = (Stdlib.Int.succ
              wc.wc_diff_00); wc_same_01 = wc.wc_same_01; wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = (Stdlib.Int.succ wc.wc_same_01); wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = (Stdlib.Int.succ
              wc.wc_diff_01); wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       y)
     (fun _ ->
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = (Stdlib.Int.succ wc.wc_same_10); wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = (Stdlib.Int.succ
              wc.wc_diff_10); wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = wc.wc_diff_10;
              wc_same_11 = (Stdlib.Int.succ wc.wc_same_11); wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = wc.wc_diff_10;
              wc_same_11 = wc.wc_same_11; wc_diff_11 = (Stdlib.Int.succ
              wc.wc_diff_11) })
       y)
     x)

(** val advance_state :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> bool -> vMState **)

let advance_state s instr graph csrs err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = s.vm_regs; vm_mem = s.vm_mem;
    vm_pc = (Stdlib.Int.succ s.vm_pc); vm_mu = (apply_cost s instr);
    vm_mu_tensor = s.vm_mu_tensor; vm_err = err_flag; vm_logic_acc =
    s.vm_logic_acc; vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness;
    vm_certified = s.vm_certified }

(** val advance_state_reveal :
    vMState -> vm_instruction -> int -> int -> partitionGraph -> cSRState ->
    bool -> vMState **)

let advance_state_reveal s instr flat_idx delta graph csrs err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = s.vm_regs; vm_mem = s.vm_mem;
    vm_pc = (Stdlib.Int.succ s.vm_pc); vm_mu = (apply_cost s instr);
    vm_mu_tensor = (vm_mu_tensor_add_at s flat_idx delta); vm_err = err_flag;
    vm_logic_acc = s.vm_logic_acc; vm_mstatus = s.vm_mstatus; vm_witness =
    s.vm_witness; vm_certified = s.vm_certified }

(** val advance_state_rm :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> int list ->
    int list -> bool -> vMState **)

let advance_state_rm s instr graph csrs regs mem err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = regs; vm_mem = mem; vm_pc =
    (Stdlib.Int.succ s.vm_pc); vm_mu = (apply_cost s instr); vm_mu_tensor =
    s.vm_mu_tensor; vm_err = err_flag; vm_logic_acc = s.vm_logic_acc;
    vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness; vm_certified =
    s.vm_certified }

(** val jump_state : vMState -> vm_instruction -> int -> vMState **)

let jump_state s instr target =
  { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = s.vm_regs; vm_mem =
    s.vm_mem; vm_pc = target; vm_mu = (apply_cost s instr); vm_mu_tensor =
    s.vm_mu_tensor; vm_err = s.vm_err; vm_logic_acc = s.vm_logic_acc;
    vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness; vm_certified =
    s.vm_certified }

(** val jump_state_rm :
    vMState -> vm_instruction -> int -> int list -> int list -> vMState **)

let jump_state_rm s instr target regs mem =
  { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = regs; vm_mem = mem;
    vm_pc = target; vm_mu = (apply_cost s instr); vm_mu_tensor =
    s.vm_mu_tensor; vm_err = s.vm_err; vm_logic_acc = s.vm_logic_acc;
    vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness; vm_certified =
    s.vm_certified }

(** val vm_apply : vMState -> vm_instruction -> vMState **)

let vm_apply s = function
| Instr_pnew (region, cost) ->
  let (graph', _) = graph_pnew s.vm_graph region in
  advance_state s (Instr_pnew (region, cost)) graph' s.vm_csrs s.vm_err
| Instr_psplit (module0, left_region, right_region, cost) ->
  (match graph_psplit s.vm_graph module0 left_region right_region with
   | Some p ->
     let (p0, _) = p in
     let (graph', _) = p0 in
     advance_state s (Instr_psplit (module0, left_region, right_region,
       cost)) graph' s.vm_csrs s.vm_err
   | None ->
     advance_state s (Instr_psplit (module0, left_region, right_region,
       cost)) s.vm_graph (csr_set_err s.vm_csrs (Stdlib.Int.succ 0))
       (latch_err s true))
| Instr_pmerge (m1, m2, cost) ->
  (match graph_pmerge s.vm_graph m1 m2 with
   | Some p ->
     let (graph', _) = p in
     advance_state s (Instr_pmerge (m1, m2, cost)) graph' s.vm_csrs s.vm_err
   | None ->
     advance_state s (Instr_pmerge (m1, m2, cost)) s.vm_graph
       (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_lassert (module0, formula, cert, cost) ->
  (match cert with
   | Lassert_cert_unsat proof ->
     if CertCheck.check_lrat formula proof
     then let csrs' =
            csr_set_err (csr_set_status s.vm_csrs (Stdlib.Int.succ 0)) 0
          in
          advance_state s (Instr_lassert (module0, formula,
            (Lassert_cert_unsat proof), cost)) s.vm_graph
            (csr_set_cert_addr csrs' (ascii_checksum formula)) s.vm_err
     else advance_state s (Instr_lassert (module0, formula,
            (Lassert_cert_unsat proof), cost)) s.vm_graph
            (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true)
   | Lassert_cert_sat model ->
     if CertCheck.check_model formula model
     then let graph' = graph_add_axiom s.vm_graph module0 formula in
          let csrs' =
            csr_set_err (csr_set_status s.vm_csrs (Stdlib.Int.succ 0)) 0
          in
          advance_state s (Instr_lassert (module0, formula, (Lassert_cert_sat
            model), cost)) graph'
            (csr_set_cert_addr csrs' (ascii_checksum formula)) s.vm_err
     else advance_state s (Instr_lassert (module0, formula, (Lassert_cert_sat
            model), cost)) s.vm_graph
            (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_ljoin (cert1, cert2, cost) ->
  if eqb0 cert1 cert2
  then let csrs' = csr_set_err s.vm_csrs 0 in
       advance_state s (Instr_ljoin (cert1, cert2, cost)) s.vm_graph
         (csr_set_cert_addr csrs' (ascii_checksum (append cert1 cert2)))
         s.vm_err
  else let csrs' = csr_set_err s.vm_csrs (Stdlib.Int.succ 0) in
       advance_state s (Instr_ljoin (cert1, cert2, cost)) s.vm_graph
         (csr_set_cert_addr csrs' (ascii_checksum (append cert1 cert2)))
         (latch_err s true)
| Instr_pdiscover (module0, evidence, cost) ->
  let graph' = graph_record_discovery s.vm_graph module0 evidence in
  advance_state s (Instr_pdiscover (module0, evidence, cost)) graph'
    s.vm_csrs s.vm_err
| Instr_xfer (dst, src, cost) ->
  advance_state_rm s (Instr_xfer (dst, src, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (read_reg s src)) s.vm_mem s.vm_err
| Instr_load_imm (dst, imm, cost) ->
  advance_state_rm s (Instr_load_imm (dst, imm, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64 imm)) s.vm_mem s.vm_err
| Instr_load (dst, rs_addr, cost) ->
  advance_state_rm s (Instr_load (dst, rs_addr, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (read_mem s (read_reg s rs_addr))) s.vm_mem s.vm_err
| Instr_store (rs_addr, src, cost) ->
  advance_state_rm s (Instr_store (rs_addr, src, cost)) s.vm_graph s.vm_csrs
    s.vm_regs (write_mem s (read_reg s rs_addr) (read_reg s src)) s.vm_err
| Instr_add (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_add (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_add (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_sub (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_sub (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_sub (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_jump (target, cost) -> jump_state s (Instr_jump (target, cost)) target
| Instr_jnez (rs, target, cost) ->
  if (=) (read_reg s rs) 0
  then advance_state s (Instr_jnez (rs, target, cost)) s.vm_graph s.vm_csrs
         s.vm_err
  else jump_state s (Instr_jnez (rs, target, cost)) target
| Instr_call (target, cost) ->
  let sp =
    read_reg s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))))))))))))))))))))))))))
  in
  jump_state_rm s (Instr_call (target, cost)) target
    (write_reg s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))) (word64_add sp (Stdlib.Int.succ 0)))
    (write_mem s sp (Stdlib.Int.succ s.vm_pc))
| Instr_ret cost ->
  let sp =
    word64_sub
      (read_reg s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))))))))))))))))))))))))))))))) (Stdlib.Int.succ 0)
  in
  jump_state_rm s (Instr_ret cost) (read_mem s sp)
    (write_reg s (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))) sp) s.vm_mem
| Instr_chsh_trial (x, y, a, b, cost) ->
  if chsh_bits_ok x y a b
  then { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = s.vm_regs;
         vm_mem = s.vm_mem; vm_pc = (Stdlib.Int.succ s.vm_pc); vm_mu =
         (apply_cost s (Instr_chsh_trial (x, y, a, b, cost))); vm_mu_tensor =
         s.vm_mu_tensor; vm_err = s.vm_err; vm_logic_acc = s.vm_logic_acc;
         vm_mstatus = s.vm_mstatus; vm_witness =
         (record_trial s.vm_witness x y a b); vm_certified = s.vm_certified }
  else advance_state s (Instr_chsh_trial (x, y, a, b, cost)) s.vm_graph
         (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true)
| Instr_xor_load (dst, addr, cost) ->
  advance_state_rm s (Instr_xor_load (dst, addr, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (read_mem s addr)) s.vm_mem s.vm_err
| Instr_xor_add (dst, src, cost) ->
  advance_state_rm s (Instr_xor_add (dst, src, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_xor (read_reg s dst) (read_reg s src))) s.vm_mem
    s.vm_err
| Instr_xor_swap (a, b, cost) ->
  advance_state_rm s (Instr_xor_swap (a, b, cost)) s.vm_graph s.vm_csrs
    (swap_regs s.vm_regs a b) s.vm_mem s.vm_err
| Instr_xor_rank (dst, src, cost) ->
  advance_state_rm s (Instr_xor_rank (dst, src, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_popcount (read_reg s src))) s.vm_mem s.vm_err
| Instr_emit (module0, payload, cost) ->
  let csrs' = csr_set_cert_addr s.vm_csrs (ascii_checksum payload) in
  advance_state s (Instr_emit (module0, payload, cost)) s.vm_graph csrs'
    s.vm_err
| Instr_reveal (module0, bits, cert, cost) ->
  let csrs' = csr_set_cert_addr s.vm_csrs (ascii_checksum cert) in
  advance_state_reveal s (Instr_reveal (module0, bits, cert, cost)) module0
    bits s.vm_graph csrs' s.vm_err
| Instr_read_port (dst, channel_idx, value, bits, cost) ->
  advance_state_rm s (Instr_read_port (dst, channel_idx, value, bits, cost))
    s.vm_graph s.vm_csrs (write_reg s dst value) s.vm_mem s.vm_err
| Instr_heap_load (dst, rs_addr, cost) ->
  advance_state_rm s (Instr_heap_load (dst, rs_addr, cost)) s.vm_graph
    s.vm_csrs
    (write_reg s dst
      (read_mem s (add s.vm_csrs.csr_heap_base (read_reg s rs_addr))))
    s.vm_mem s.vm_err
| Instr_heap_store (rs_addr, src, cost) ->
  advance_state_rm s (Instr_heap_store (rs_addr, src, cost)) s.vm_graph
    s.vm_csrs s.vm_regs
    (write_mem s (add s.vm_csrs.csr_heap_base (read_reg s rs_addr))
      (read_reg s src)) s.vm_err
| Instr_certify delta_mu ->
  { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = s.vm_regs; vm_mem =
    s.vm_mem; vm_pc = (Stdlib.Int.succ s.vm_pc); vm_mu =
    (add s.vm_mu (Stdlib.Int.succ delta_mu)); vm_mu_tensor = s.vm_mu_tensor;
    vm_err = s.vm_err; vm_logic_acc = s.vm_logic_acc; vm_mstatus =
    s.vm_mstatus; vm_witness = s.vm_witness; vm_certified = true }
| Instr_and (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_and (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_and (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_or (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_or (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_or (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_shl (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_shl (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_shl (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_shr (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_shr (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_shr (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_mul (dst, rs1, rs2, cost) ->
  advance_state_rm s (Instr_mul (dst, rs1, rs2, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst (word64_mul (read_reg s rs1) (read_reg s rs2))) s.vm_mem
    s.vm_err
| Instr_lui (dst, imm, cost) ->
  advance_state_rm s (Instr_lui (dst, imm, cost)) s.vm_graph s.vm_csrs
    (write_reg s dst
      (word64_shl imm (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))) s.vm_mem s.vm_err
| Instr_tensor_set (mid, i, j, value, cost) ->
  if (&&)
       (Nat.ltb i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))
       (Nat.ltb j (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))
  then advance_state s (Instr_tensor_set (mid, i, j, value, cost))
         (graph_update_module_tensor s.vm_graph mid
           (add
             (mul i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
               (Stdlib.Int.succ 0))))) j) value) s.vm_csrs s.vm_err
  else advance_state s (Instr_tensor_set (mid, i, j, value, cost)) s.vm_graph
         (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true)
| Instr_tensor_get (dst, mid, i, j, cost) ->
  if (&&)
       (Nat.ltb i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))
       (Nat.ltb j (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))
  then advance_state_rm s (Instr_tensor_get (dst, mid, i, j, cost))
         s.vm_graph s.vm_csrs
         (write_reg s dst (module_tensor_entry s mid i j)) s.vm_mem s.vm_err
  else advance_state s (Instr_tensor_get (dst, mid, i, j, cost)) s.vm_graph
         (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true)
| Instr_morph (dst, src_mod, dst_mod, coupling_idx, cost) ->
  (match graph_lookup s.vm_graph src_mod with
   | Some _ ->
     (match graph_lookup s.vm_graph dst_mod with
      | Some _ ->
        let c = { coupling_pairs = []; coupling_label = [] } in
        let (graph', morph_id) =
          graph_add_morphism s.vm_graph src_mod dst_mod c false
        in
        advance_state_rm s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
          cost)) graph' s.vm_csrs (write_reg s dst morph_id) s.vm_mem s.vm_err
      | None ->
        advance_state s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
          cost)) s.vm_graph (csr_set_err s.vm_csrs (Stdlib.Int.succ 0))
          (latch_err s true))
   | None ->
     advance_state s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
       cost)) s.vm_graph (csr_set_err s.vm_csrs (Stdlib.Int.succ 0))
       (latch_err s true))
| Instr_compose (dst, m1_id, m2_id, cost) ->
  (match graph_compose_morphisms s.vm_graph m1_id m2_id with
   | Some p ->
     let (graph', new_id) = p in
     advance_state_rm s (Instr_compose (dst, m1_id, m2_id, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_compose (dst, m1_id, m2_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_morph_id (dst, module0, cost) ->
  (match graph_add_identity s.vm_graph module0 with
   | Some p ->
     let (graph', new_id) = p in
     advance_state_rm s (Instr_morph_id (dst, module0, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_morph_id (dst, module0, cost)) s.vm_graph
       (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_morph_delete (morph_id, cost) ->
  (match graph_delete_morphism s.vm_graph morph_id with
   | Some graph' ->
     advance_state s (Instr_morph_delete (morph_id, cost)) graph' s.vm_csrs
       s.vm_err
   | None ->
     advance_state s (Instr_morph_delete (morph_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_morph_assert (morph_id, property, cert, cost) ->
  (match graph_lookup_morphism s.vm_graph morph_id with
   | Some _ ->
     let csrs' = csr_set_err (csr_set_status s.vm_csrs (Stdlib.Int.succ 0)) 0
     in
     advance_state s (Instr_morph_assert (morph_id, property, cert, cost))
       s.vm_graph (csr_set_cert_addr csrs' (ascii_checksum property)) s.vm_err
   | None ->
     advance_state s (Instr_morph_assert (morph_id, property, cert, cost))
       s.vm_graph (csr_set_err s.vm_csrs (Stdlib.Int.succ 0))
       (latch_err s true))
| Instr_morph_tensor (dst, f_id, g_id, cost) ->
  (match graph_tensor_morphisms s.vm_graph f_id g_id with
   | Some p ->
     let (graph', new_id) = p in
     advance_state_rm s (Instr_morph_tensor (dst, f_id, g_id, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_morph_tensor (dst, f_id, g_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs (Stdlib.Int.succ 0)) (latch_err s true))
| Instr_morph_get (dst, morph_id, selector, cost) ->
  (match graph_lookup_morphism s.vm_graph morph_id with
   | Some ms ->
     let value =
       (fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> ms.morph_source)
         (fun n0 ->
         (fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> ms.morph_target)
           (fun n1 ->
           (fun fO fS n -> if n=0 then fO () else fS (n-1))
             (fun _ -> length ms.morph_coupling.coupling_pairs)
             (fun n2 ->
             (fun fO fS n -> if n=0 then fO () else fS (n-1))
               (fun _ ->
               if ms.morph_is_identity then Stdlib.Int.succ 0 else 0)
               (fun _ -> 0)
               n2)
             n1)
           n0)
         selector
     in
     advance_state_rm s (Instr_morph_get (dst, morph_id, selector, cost))
       s.vm_graph s.vm_csrs (write_reg s dst value) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_morph_get (dst, morph_id, selector, cost))
       s.vm_graph (csr_set_err s.vm_csrs (Stdlib.Int.succ 0))
       (latch_err s true))
| x -> advance_state s x s.vm_graph s.vm_csrs s.vm_err

(** val nofi_step_cost_okb : vm_instruction -> bool **)

let nofi_step_cost_okb instr =
  if is_cert_setterb instr
  then (<=) (Stdlib.Int.succ 0) (instruction_cost instr)
  else true

(** val nofi_trace_cost_okb : vm_instruction list -> bool **)

let nofi_trace_cost_okb trace =
  forallb nofi_step_cost_okb trace

(** val vm_apply_nofi : vMState -> vm_instruction -> vMState **)

let vm_apply_nofi =
  vm_apply

(** val vm_apply_runtime : vMState -> vm_instruction -> vMState **)

let vm_apply_runtime =
  vm_apply

type kamiSnapshot = { snap_pc : int; snap_mu : int; snap_err : bool;
                      snap_halted : bool; snap_regs : (int -> int);
                      snap_mem : (int -> int); snap_partition_ops : int;
                      snap_mdl_ops : int; snap_info_gain : int;
                      snap_error_code : int; snap_mu_tensor : (int -> int);
                      snap_pt_sizes : (int -> int); snap_pt_next_id : 
                      int; snap_certified : bool; snap_wc_same_00 : int;
                      snap_wc_diff_00 : int; snap_wc_same_01 : int;
                      snap_wc_diff_01 : int; snap_wc_same_10 : int;
                      snap_wc_diff_10 : int; snap_wc_same_11 : int;
                      snap_wc_diff_11 : int }

type busReg =
| BusRegPc
| BusRegMu
| BusRegErr
| BusRegHalted
| BusRegPartitionOps
| BusRegMdlOps
| BusRegInfoGain
| BusRegErrorCode
| BusRegMstatus
| BusRegMcycleLo
| BusRegMcycleHi
| BusRegMinstretLo
| BusRegMinstretHi
| BusRegLogicAcc
| BusRegLogicReqValid
| BusRegLogicReqOpcode
| BusRegLogicReqPayload
| BusRegMuTensor0
| BusRegMuTensor1
| BusRegMuTensor2
| BusRegMuTensor3
| BusRegBianchiAlarm
| BusRegPtNextId
| BusRegPtSize
| BusRegLoadInstrAddr
| BusRegLoadInstrData
| BusRegLoadInstrKick
| BusRegSetLogicRespValid
| BusRegSetLogicRespError
| BusRegSetLogicRespValue
| BusRegSetActiveModule
| BusRegSetTrapVector

(** val decodeBusReg : int -> busReg option **)

let decodeBusReg addr =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some BusRegPc)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Some BusRegMu)
            (fun n4 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                    (fun _ -> Some BusRegErr)
                    (fun n8 ->
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                            (fun _ -> Some BusRegHalted)
                            (fun n12 ->
                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                    (fun _ -> Some
                                    BusRegPartitionOps)
                                    (fun n16 ->
                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                            (fun _ -> Some
                                            BusRegMdlOps)
                                            (fun n20 ->
                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                    (fun _ -> Some
                                                    BusRegInfoGain)
                                                    (fun n24 ->
                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                            (fun _ -> Some
                                                            BusRegErrorCode)
                                                            (fun n28 ->
                                                            (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMstatus)
                                                                    (fun n32 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMcycleLo)
                                                                    (fun n36 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMcycleHi)
                                                                    (fun n40 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMinstretLo)
                                                                    (fun n44 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMinstretHi)
                                                                    (fun n48 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLogicAcc)
                                                                    (fun n52 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLogicReqValid)
                                                                    (fun n56 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLogicReqOpcode)
                                                                    (fun n60 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLogicReqPayload)
                                                                    (fun n64 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor0)
                                                                    (fun n68 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor1)
                                                                    (fun n72 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor2)
                                                                    (fun n76 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor3)
                                                                    (fun n80 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegBianchiAlarm)
                                                                    (fun n84 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegPtNextId)
                                                                    (fun n88 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegPtSize)
                                                                    (fun n92 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n116 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n117 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n124 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n125 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrAddr)
                                                                    (fun n128 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrData)
                                                                    (fun n132 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrKick)
                                                                    (fun n136 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetLogicRespValid)
                                                                    (fun n140 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetLogicRespError)
                                                                    (fun n144 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetLogicRespValue)
                                                                    (fun n148 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n149 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetActiveModule)
                                                                    (fun n152 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetTrapVector)
                                                                    (fun _ ->
                                                                    None)
                                                                    n155)
                                                                    n154)
                                                                    n153)
                                                                    n152)
                                                                    n151)
                                                                    n150)
                                                                    n149)
                                                                    n148)
                                                                    n147)
                                                                    n146)
                                                                    n145)
                                                                    n144)
                                                                    n143)
                                                                    n142)
                                                                    n141)
                                                                    n140)
                                                                    n139)
                                                                    n138)
                                                                    n137)
                                                                    n136)
                                                                    n135)
                                                                    n134)
                                                                    n133)
                                                                    n132)
                                                                    n131)
                                                                    n130)
                                                                    n129)
                                                                    n128)
                                                                    n127)
                                                                    n126)
                                                                    n125)
                                                                    n124)
                                                                    n123)
                                                                    n122)
                                                                    n121)
                                                                    n120)
                                                                    n119)
                                                                    n118)
                                                                    n117)
                                                                    n116)
                                                                    n115)
                                                                    n114)
                                                                    n113)
                                                                    n112)
                                                                    n111)
                                                                    n110)
                                                                    n109)
                                                                    n108)
                                                                    n107)
                                                                    n106)
                                                                    n105)
                                                                    n104)
                                                                    n103)
                                                                    n102)
                                                                    n101)
                                                                    n100)
                                                                    n99)
                                                                    n98)
                                                                    n97)
                                                                    n96)
                                                                    n95)
                                                                    n94)
                                                                    n93)
                                                                    n92)
                                                                    n91)
                                                                    n90)
                                                                    n89)
                                                                    n88)
                                                                    n87)
                                                                    n86)
                                                                    n85)
                                                                    n84)
                                                                    n83)
                                                                    n82)
                                                                    n81)
                                                                    n80)
                                                                    n79)
                                                                    n78)
                                                                    n77)
                                                                    n76)
                                                                    n75)
                                                                    n74)
                                                                    n73)
                                                                    n72)
                                                                    n71)
                                                                    n70)
                                                                    n69)
                                                                    n68)
                                                                    n67)
                                                                    n66)
                                                                    n65)
                                                                    n64)
                                                                    n63)
                                                                    n62)
                                                                    n61)
                                                                    n60)
                                                                    n59)
                                                                    n58)
                                                                    n57)
                                                                    n56)
                                                                    n55)
                                                                    n54)
                                                                    n53)
                                                                    n52)
                                                                    n51)
                                                                    n50)
                                                                    n49)
                                                                    n48)
                                                                    n47)
                                                                    n46)
                                                                    n45)
                                                                    n44)
                                                                    n43)
                                                                    n42)
                                                                    n41)
                                                                    n40)
                                                                    n39)
                                                                    n38)
                                                                    n37)
                                                                    n36)
                                                                    n35)
                                                                    n34)
                                                                    n33)
                                                                    n32)
                                                                    n31)
                                                                  n30)
                                                                n29)
                                                              n28)
                                                            n27)
                                                          n26)
                                                        n25)
                                                      n24)
                                                    n23)
                                                  n22)
                                                n21)
                                              n20)
                                            n19)
                                          n18)
                                        n17)
                                      n16)
                                    n15)
                                  n14)
                                n13)
                              n12)
                            n11)
                          n10)
                        n9)
                      n8)
                    n7)
                  n6)
                n5)
              n4)
            n3)
          n2)
        n1)
      n0)
    addr

(** val busRegReadable : busReg -> bool **)

let busRegReadable = function
| BusRegLoadInstrAddr -> false
| BusRegLoadInstrData -> false
| BusRegLoadInstrKick -> false
| BusRegSetLogicRespValid -> false
| BusRegSetLogicRespError -> false
| BusRegSetLogicRespValue -> false
| BusRegSetActiveModule -> false
| BusRegSetTrapVector -> false
| _ -> true

(** val busRegWritable : busReg -> bool **)

let busRegWritable r =
  negb (busRegReadable r)

type busCoreView = { view_pc : int; view_mu : int; view_err : bool;
                     view_halted : bool; view_partition_ops : int;
                     view_mdl_ops : int; view_info_gain : int;
                     view_error_code : int; view_mstatus : int;
                     view_mcycle_lo : int; view_mcycle_hi : int;
                     view_minstret_lo : int; view_minstret_hi : int;
                     view_logic_acc : int; view_logic_req_valid : bool;
                     view_logic_req_opcode : int;
                     view_logic_req_payload : int; view_mu_tensor0 : 
                     int; view_mu_tensor1 : int; view_mu_tensor2 : int;
                     view_mu_tensor3 : int; view_bianchi_alarm : bool;
                     view_pt_next_id : int; view_pt_size : (int -> int) }

(** val bool_to_nat : bool -> int **)

let bool_to_nat = function
| true -> Stdlib.Int.succ 0
| false -> 0

(** val busRegReadValue : busCoreView -> busReg -> int option **)

let busRegReadValue v = function
| BusRegPc -> Some v.view_pc
| BusRegMu -> Some v.view_mu
| BusRegErr -> Some (bool_to_nat v.view_err)
| BusRegHalted -> Some (bool_to_nat v.view_halted)
| BusRegPartitionOps -> Some v.view_partition_ops
| BusRegMdlOps -> Some v.view_mdl_ops
| BusRegInfoGain -> Some v.view_info_gain
| BusRegErrorCode -> Some v.view_error_code
| BusRegMstatus -> Some v.view_mstatus
| BusRegMcycleLo -> Some v.view_mcycle_lo
| BusRegMcycleHi -> Some v.view_mcycle_hi
| BusRegMinstretLo -> Some v.view_minstret_lo
| BusRegMinstretHi -> Some v.view_minstret_hi
| BusRegLogicAcc -> Some v.view_logic_acc
| BusRegLogicReqValid -> Some (bool_to_nat v.view_logic_req_valid)
| BusRegLogicReqOpcode -> Some v.view_logic_req_opcode
| BusRegLogicReqPayload -> Some v.view_logic_req_payload
| BusRegMuTensor0 -> Some v.view_mu_tensor0
| BusRegMuTensor1 -> Some v.view_mu_tensor1
| BusRegMuTensor2 -> Some v.view_mu_tensor2
| BusRegMuTensor3 -> Some v.view_mu_tensor3
| BusRegBianchiAlarm -> Some (bool_to_nat v.view_bianchi_alarm)
| BusRegPtNextId -> Some v.view_pt_next_id
| BusRegPtSize -> Some (v.view_pt_size 0)
| _ -> None

(** val busRead : busCoreView -> int -> int option **)

let busRead v addr =
  match decodeBusReg addr with
  | Some r -> if busRegReadable r then busRegReadValue v r else None
  | None -> None

type busShadowRegs = { sh_load_instr_addr : int; sh_load_instr_data : 
                       int; sh_load_instr_kick : bool;
                       sh_logic_resp_valid : bool;
                       sh_logic_resp_error : bool; sh_logic_resp_value : 
                       int; sh_active_module : int; sh_trap_vector : 
                       int }

type busWrapperState = { bw_core : kamiSnapshot; bw_shadow : busShadowRegs }

(** val busWriteShadow : busShadowRegs -> busReg -> int -> busShadowRegs **)

let busWriteShadow s r data =
  match r with
  | BusRegLoadInstrAddr ->
    { sh_load_instr_addr = data; sh_load_instr_data = s.sh_load_instr_data;
      sh_load_instr_kick = s.sh_load_instr_kick; sh_logic_resp_valid =
      s.sh_logic_resp_valid; sh_logic_resp_error = s.sh_logic_resp_error;
      sh_logic_resp_value = s.sh_logic_resp_value; sh_active_module =
      s.sh_active_module; sh_trap_vector = s.sh_trap_vector }
  | BusRegLoadInstrData ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data = data;
      sh_load_instr_kick = s.sh_load_instr_kick; sh_logic_resp_valid =
      s.sh_logic_resp_valid; sh_logic_resp_error = s.sh_logic_resp_error;
      sh_logic_resp_value = s.sh_logic_resp_value; sh_active_module =
      s.sh_active_module; sh_trap_vector = s.sh_trap_vector }
  | BusRegLoadInstrKick ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = (negb ((=) data 0));
      sh_logic_resp_valid = s.sh_logic_resp_valid; sh_logic_resp_error =
      s.sh_logic_resp_error; sh_logic_resp_value = s.sh_logic_resp_value;
      sh_active_module = s.sh_active_module; sh_trap_vector =
      s.sh_trap_vector }
  | BusRegSetLogicRespValid ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_logic_resp_valid = (negb ((=) data 0)); sh_logic_resp_error =
      s.sh_logic_resp_error; sh_logic_resp_value = s.sh_logic_resp_value;
      sh_active_module = s.sh_active_module; sh_trap_vector =
      s.sh_trap_vector }
  | BusRegSetLogicRespError ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_logic_resp_valid = s.sh_logic_resp_valid; sh_logic_resp_error =
      (negb ((=) data 0)); sh_logic_resp_value = s.sh_logic_resp_value;
      sh_active_module = s.sh_active_module; sh_trap_vector =
      s.sh_trap_vector }
  | BusRegSetLogicRespValue ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_logic_resp_valid = s.sh_logic_resp_valid; sh_logic_resp_error =
      s.sh_logic_resp_error; sh_logic_resp_value = data; sh_active_module =
      s.sh_active_module; sh_trap_vector = s.sh_trap_vector }
  | BusRegSetActiveModule ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_logic_resp_valid = s.sh_logic_resp_valid; sh_logic_resp_error =
      s.sh_logic_resp_error; sh_logic_resp_value = s.sh_logic_resp_value;
      sh_active_module = data; sh_trap_vector = s.sh_trap_vector }
  | BusRegSetTrapVector ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_logic_resp_valid = s.sh_logic_resp_valid; sh_logic_resp_error =
      s.sh_logic_resp_error; sh_logic_resp_value = s.sh_logic_resp_value;
      sh_active_module = s.sh_active_module; sh_trap_vector = data }
  | _ -> s

(** val busWrite : busWrapperState -> int -> int -> busWrapperState **)

let busWrite st addr data =
  match decodeBusReg addr with
  | Some r ->
    if busRegWritable r
    then { bw_core = st.bw_core; bw_shadow =
           (busWriteShadow st.bw_shadow r data) }
    else st
  | None -> st

(** val coreViewOfSnapshot : kamiSnapshot -> busCoreView **)

let coreViewOfSnapshot s =
  { view_pc = s.snap_pc; view_mu = s.snap_mu; view_err = s.snap_err;
    view_halted = s.snap_halted; view_partition_ops = s.snap_partition_ops;
    view_mdl_ops = s.snap_mdl_ops; view_info_gain = s.snap_info_gain;
    view_error_code = s.snap_error_code; view_mstatus = 0; view_mcycle_lo =
    0; view_mcycle_hi = 0; view_minstret_lo = 0; view_minstret_hi = 0;
    view_logic_acc = 0; view_logic_req_valid = false; view_logic_req_opcode =
    0; view_logic_req_payload = 0; view_mu_tensor0 = (s.snap_mu_tensor 0);
    view_mu_tensor1 = (s.snap_mu_tensor (Stdlib.Int.succ 0));
    view_mu_tensor2 =
    (s.snap_mu_tensor (Stdlib.Int.succ (Stdlib.Int.succ 0)));
    view_mu_tensor3 =
    (s.snap_mu_tensor (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))));
    view_bianchi_alarm = false; view_pt_next_id = s.snap_pt_next_id;
    view_pt_size = s.snap_pt_sizes }

type busOp =
| BusOpRead of int
| BusOpWrite of int * int

(** val bus_step : busWrapperState -> busOp -> busWrapperState **)

let bus_step st = function
| BusOpRead _ -> st
| BusOpWrite (addr, data) -> busWrite st addr data

(** val pnew_chain : int -> vMState -> int list -> int -> vMState **)

let rec pnew_chain n0 s region cost =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> s)
    (fun k ->
    pnew_chain k (vm_apply s (Instr_pnew (region, cost))) region cost)
    n0
