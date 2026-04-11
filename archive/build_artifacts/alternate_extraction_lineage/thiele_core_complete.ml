
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val length : 'a1 list -> int **)

let length x =
  let rec length0 = function
  | [] -> 0
  | _::l' -> (fun x -> x + 1) (length0 l')
  in length0 x

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let app x =
  let rec app0 l m =
    match l with
    | [] -> m
    | a::l1 -> a::(app0 l1 m)
  in app0 x

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
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> m)
    (fun n1 -> tail_add n1 ((fun x -> x + 1) m))
    n0

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n0 m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
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
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      (tail_mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub = fun n m -> max 0 (n-m)

  (** val eqb : int -> int -> bool **)

  let rec eqb = (=)

  (** val ltb : int -> int -> bool **)

  let ltb = (<)

  (** val min : int -> int -> int **)

  let rec min n0 m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> 0)
        (fun m' -> (fun x -> x + 1) (min n' m'))
        m)
      n0

  (** val divmod : int -> int -> int -> int -> int*int **)

  let rec divmod x y q u =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> q,u)
      (fun x' ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> divmod x' y ((fun x -> x + 1) q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = fun x y -> if y = 0 then 0 else x / y

  (** val modulo : int -> int -> int **)

  let modulo = fun x y -> if y = 0 then 0 else x mod y
 end

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let in_dec h a l =
  let rec f = function
  | [] -> false
  | y::l1 -> let s = h y a in if s then true else if f l1 then true else false
  in f l

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let nth n0 =
  let rec nth0 n1 l default =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> match l with
                | [] -> default
                | x::_ -> x)
      (fun m -> match l with
                | [] -> default
                | _::t -> nth0 m t default)
      n1
  in nth0 n0

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let map f =
  let rec map0 = function
  | [] -> []
  | a::t -> (f a)::(map0 t)
  in map0

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let flat_map f =
  let rec flat_map0 = function
  | [] -> []
  | x::t -> app (f x) (flat_map0 t)
  in flat_map0

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let fold_left f =
  let rec fold_left0 l a0 =
    match l with
    | [] -> a0
    | b::t -> fold_left0 t (f a0 b)
  in fold_left0

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let fold_right f a0 =
  let rec fold_right0 = function
  | [] -> a0
  | b::t -> f b (fold_right0 t)
  in fold_right0

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let existsb f =
  let rec existsb0 = function
  | [] -> false
  | a::l0 -> (||) (f a) (existsb0 l0)
  in existsb0

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let forallb f =
  let rec forallb0 = function
  | [] -> true
  | a::l0 -> (&&) (f a) (forallb0 l0)
  in forallb0

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let filter f =
  let rec filter0 = function
  | [] -> []
  | x::l0 -> if f x then x::(filter0 l0) else filter0 l0
  in filter0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let firstn n0 =
  let rec firstn0 n1 l =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> [])
      (fun n2 -> match l with
                 | [] -> []
                 | a::l0 -> a::(firstn0 n2 l0))
      n1
  in firstn0 n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let skipn n0 =
  let rec skipn0 n1 l =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> l)
      (fun n2 -> match l with
                 | [] -> []
                 | _::l0 -> skipn0 n2 l0)
      n1
  in skipn0 n0

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let nodup decA =
  let rec nodup0 = function
  | [] -> []
  | x::xs -> if in_dec decA x xs then nodup0 xs else x::(nodup0 xs)
  in nodup0

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> [])
    (fun len0 -> start::(seq ((fun x -> x + 1) start) len0))
    len

(** val repeat : 'a1 -> int -> 'a1 list **)

let repeat x =
  let rec repeat0 x0 n0 =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> [])
      (fun k -> x0::(repeat0 x0 k))
      n0
  in repeat0 x

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

  let iter f =
    let rec iter_fix x n0 =
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun n' -> f (iter_fix (iter_fix x n') n'))
        (fun n' -> iter_fix (iter_fix x n') n')
        (fun _ -> f x)
        n0
    in iter_fix

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

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

  let iter_op op =
    let rec iter0 p a =
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p0 -> op a (iter0 p0 (op a a)))
        (fun p0 -> iter0 p0 (op a a))
        (fun _ -> a)
        p
    in iter0

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x ((fun x -> x + 1) 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
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
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0

  (** val ones : int -> int **)

  let ones n0 =
    pred
      ((fun f0 fp n -> if n=0 then f0 () else fp n)
         (fun _ -> 0)
         (fun a -> (Pos.shiftl a n0))
         1)
 end

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b::l' ->
  N.add (if b then 1 else 0) (N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Eq -> false
    | Lt -> true
    | Gt -> false

  (** val gtb : int -> int -> bool **)

  let gtb x y =
    match compare x y with
    | Eq -> false
    | Lt -> false
    | Gt -> true

  (** val abs : int -> int **)

  let abs = Stdlib.Int.abs

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun n1 -> (Pos.of_succ_nat n1))
      n0
 end

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val string_of_list_ascii : char list -> char list **)

let rec string_of_list_ascii = function
| [] -> []
| ch::s0 -> ch::(string_of_list_ascii s0)

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s0 -> ch::(list_ascii_of_string s0)

module CertCheck =
 struct
  (** val word32_to_signed : int -> int **)

  let word32_to_signed w =
    let w' = Z.of_nat w in
    if Z.ltb w' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
         1)))))))))))))))))))))))))))))))
    then w'
    else Z.sub w' ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           1))))))))))))))))))))))))))))))))

  (** val check_model_binary_fn : int list -> (int -> int) -> bool **)

  let check_model_binary_fn formula_words get_cert =
    match formula_words with
    | [] -> false
    | _::l ->
      (match l with
       | [] -> false
       | _::l0 ->
         (match l0 with
          | [] -> false
          | nclauses_w::lit_words ->
            let lookup_asgn = fun var -> negb (Nat.eqb (get_cert var) 0) in
            let rec scan words ndone clause_sat =
              if Nat.eqb ndone nclauses_w
              then true
              else (match words with
                    | [] -> false
                    | w::ws ->
                      if Nat.eqb w 0
                      then if clause_sat
                           then scan ws ((fun x -> x + 1) ndone) false
                           else false
                      else let lit = word32_to_signed w in
                           let var = Z.to_nat (Z.abs lit) in
                           let lsat =
                             if Z.gtb lit 0
                             then lookup_asgn var
                             else negb (lookup_asgn var)
                           in
                           scan ws ndone ((||) clause_sat lsat))
            in scan lit_words 0 false))
 end

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

(** val nat_list_mem : int -> int list -> bool **)

let rec nat_list_mem x = function
| [] -> false
| y::ys -> if Nat.eqb x y then true else nat_list_mem x ys

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
  repeat 0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) 0))))))))))))))))

(** val mk_module_state : int list -> axiomSet -> moduleState **)

let mk_module_state region axioms =
  { module_region = region; module_axioms = axioms; module_mu_tensor =
    module_mu_tensor_default }

(** val list_update_at : int list -> int -> int -> int list **)

let rec list_update_at l k v =
  match l with
  | [] -> []
  | h::t ->
    ((fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ -> v::t)
       (fun i -> h::(list_update_at t i v))
       k)

(** val normalize_module : moduleState -> moduleState **)

let normalize_module m =
  { module_region = (normalize_region m.module_region); module_axioms =
    m.module_axioms; module_mu_tensor = m.module_mu_tensor }

type morphismID = int

type couplingData = { coupling_pairs : (int*int) list;
                      coupling_label : char list }

type morphismState = { morph_source : moduleID; morph_target : moduleID;
                       morph_coupling : couplingData; morph_is_identity : 
                       bool }

(** val nat_pair_eq_dec : (int*int) -> (int*int) -> bool **)

let nat_pair_eq_dec p1 p2 =
  (let a,b = p1 in
   (fun x ->
   let n0,n1 = x in
   if (=) a n0 then if (=) b n1 then true else false else false)) p2

(** val normalize_coupling : couplingData -> couplingData **)

let normalize_coupling c =
  { coupling_pairs = (nodup nat_pair_eq_dec c.coupling_pairs);
    coupling_label = c.coupling_label }

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID*moduleState) list;
                        pg_next_morph_id : morphismID;
                        pg_morphisms : (morphismID*morphismState) list }

(** val graph_lookup_modules :
    (moduleID*moduleState) list -> moduleID -> moduleState option **)

let rec graph_lookup_modules modules mid =
  match modules with
  | [] -> None
  | p::rest ->
    let id,m = p in
    if Nat.eqb id mid then Some m else graph_lookup_modules rest mid

(** val graph_lookup : partitionGraph -> moduleID -> moduleState option **)

let graph_lookup g mid =
  graph_lookup_modules g.pg_modules mid

(** val graph_insert_modules :
    (moduleID*moduleState) list -> moduleID -> moduleState ->
    (moduleID*moduleState) list **)

let rec graph_insert_modules modules mid m =
  match modules with
  | [] -> (mid,m)::[]
  | p::rest ->
    let id,existing = p in
    if Nat.eqb id mid
    then (mid,m)::rest
    else (id,existing)::(graph_insert_modules rest mid m)

(** val graph_update :
    partitionGraph -> moduleID -> moduleState -> partitionGraph **)

let graph_update g mid m =
  { pg_next_id = g.pg_next_id; pg_modules =
    (graph_insert_modules g.pg_modules mid (normalize_module m));
    pg_next_morph_id = g.pg_next_morph_id; pg_morphisms = g.pg_morphisms }

(** val graph_remove_modules :
    (moduleID*moduleState) list -> moduleID -> ((moduleID*moduleState)
    list*moduleState) option **)

let rec graph_remove_modules modules mid =
  match modules with
  | [] -> None
  | p::rest ->
    let id,m = p in
    if Nat.eqb id mid
    then Some (rest,m)
    else (match graph_remove_modules rest mid with
          | Some p0 ->
            let rest',removed = p0 in Some (((id,m)::rest'),removed)
          | None -> None)

(** val graph_remove :
    partitionGraph -> moduleID -> (partitionGraph*moduleState) option **)

let graph_remove g mid =
  match graph_remove_modules g.pg_modules mid with
  | Some p ->
    let modules',removed = p in
    Some ({ pg_next_id = g.pg_next_id; pg_modules = modules';
    pg_next_morph_id = g.pg_next_morph_id; pg_morphisms =
    g.pg_morphisms },removed)
  | None -> None

(** val graph_add_module :
    partitionGraph -> int list -> axiomSet -> partitionGraph*moduleID **)

let graph_add_module g region axioms =
  let module0 = normalize_module (mk_module_state region axioms) in
  let mid = g.pg_next_id in
  { pg_next_id = ((fun x -> x + 1) mid); pg_modules =
  ((mid,module0)::g.pg_modules); pg_next_morph_id = g.pg_next_morph_id;
  pg_morphisms = g.pg_morphisms },mid

(** val graph_find_region_modules :
    (moduleID*moduleState) list -> int list -> moduleID option **)

let rec graph_find_region_modules modules region =
  match modules with
  | [] -> None
  | p::rest ->
    let id,m = p in
    if nat_list_eq m.module_region region
    then Some id
    else graph_find_region_modules rest region

(** val graph_find_region : partitionGraph -> int list -> moduleID option **)

let graph_find_region g region =
  graph_find_region_modules g.pg_modules (normalize_region region)

(** val graph_add_axioms :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_add_axioms g mid axs =
  fold_left (fun acc ax ->
    match graph_lookup acc mid with
    | Some m ->
      let updated = { module_region = m.module_region; module_axioms =
        (app m.module_axioms (ax::[])); module_mu_tensor =
        m.module_mu_tensor }
      in
      graph_update acc mid updated
    | None -> acc) axs g

(** val graph_record_discovery :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_record_discovery =
  graph_add_axioms

(** val relational_compose :
    (int*int) list -> (int*int) list -> (int*int) list **)

let relational_compose r1 r2 =
  flat_map (fun pat ->
    let a,b = pat in
    map (fun pat0 -> let _,c = pat0 in a,c)
      (filter (fun pat0 -> let b',_ = pat0 in Nat.eqb b b') r2)) r1

(** val graph_lookup_morphism_list :
    (morphismID*morphismState) list -> morphismID -> morphismState option **)

let rec graph_lookup_morphism_list morphisms morph_id =
  match morphisms with
  | [] -> None
  | p::rest ->
    let id,ms = p in
    if Nat.eqb id morph_id
    then Some ms
    else graph_lookup_morphism_list rest morph_id

(** val graph_lookup_morphism :
    partitionGraph -> morphismID -> morphismState option **)

let graph_lookup_morphism g morph_id =
  graph_lookup_morphism_list g.pg_morphisms morph_id

(** val graph_add_morphism :
    partitionGraph -> moduleID -> moduleID -> couplingData -> bool ->
    partitionGraph*morphismID **)

let graph_add_morphism g src dst c is_id =
  let new_id = g.pg_next_morph_id in
  let ms = { morph_source = src; morph_target = dst; morph_coupling =
    (normalize_coupling c); morph_is_identity = is_id }
  in
  { pg_next_id = g.pg_next_id; pg_modules = g.pg_modules; pg_next_morph_id =
  ((fun x -> x + 1) new_id); pg_morphisms =
  ((new_id,ms)::g.pg_morphisms) },new_id

(** val graph_add_identity :
    partitionGraph -> moduleID -> (partitionGraph*morphismID) option **)

let graph_add_identity g mid =
  match graph_lookup g mid with
  | Some m ->
    let diag = map (fun x -> x,x) m.module_region in
    let c = { coupling_pairs = diag; coupling_label = ('i'::('d'::[])) } in
    Some (graph_add_morphism g mid mid c true)
  | None -> None

(** val graph_delete_morphism :
    partitionGraph -> morphismID -> partitionGraph option **)

let graph_delete_morphism g morph_id =
  if existsb (fun pat -> let id,_ = pat in Nat.eqb id morph_id) g.pg_morphisms
  then Some { pg_next_id = g.pg_next_id; pg_modules = g.pg_modules;
         pg_next_morph_id = g.pg_next_morph_id; pg_morphisms =
         (filter (fun pat -> let id,_ = pat in negb (Nat.eqb id morph_id))
           g.pg_morphisms) }
  else None

(** val graph_compose_morphisms :
    partitionGraph -> morphismID -> morphismID -> (partitionGraph*morphismID)
    option **)

let graph_compose_morphisms g m1 m2 =
  match graph_lookup_morphism g m1 with
  | Some f ->
    (match graph_lookup_morphism g m2 with
     | Some h ->
       if Nat.eqb f.morph_target h.morph_source
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
    partitionGraph -> morphismID -> morphismID -> (partitionGraph*morphismID)
    option **)

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

(** val word64 : int -> int **)

let word64 = (fun x -> x)

(** val word64_xor : int -> int -> int **)

let word64_xor = (fun a b -> Int64.to_int (Int64.logxor (Int64.of_int a) (Int64.of_int b)))

(** val word64_add : int -> int -> int **)

let word64_add = (fun a b -> Int64.to_int (Int64.add (Int64.of_int a) (Int64.of_int b)))

(** val word64_sub : int -> int -> int **)

let word64_sub = (fun a b -> Int64.to_int (Int64.sub (Int64.of_int a) (Int64.of_int b)))

(** val word64_popcount : int -> int **)

let word64_popcount = (fun x -> let v = ref (Int64.of_int x) in let c = ref 0 in while !v <> 0L do v := Int64.logand !v (Int64.sub !v 1L); incr c done; !c)

(** val word64_and : int -> int -> int **)

let word64_and = (fun a b -> Int64.to_int (Int64.logand (Int64.of_int a) (Int64.of_int b)))

(** val word64_or : int -> int -> int **)

let word64_or = (fun a b -> Int64.to_int (Int64.logor (Int64.of_int a) (Int64.of_int b)))

(** val word64_shl : int -> int -> int **)

let word64_shl = (fun a b -> Int64.to_int (Int64.shift_left (Int64.of_int a) (b mod 64)))

(** val word64_shr : int -> int -> int **)

let word64_shr = (fun a b -> Int64.to_int (Int64.shift_right_logical (Int64.of_int a) (b mod 64)))

(** val word64_mul : int -> int -> int **)

let word64_mul = (fun a b -> Int64.to_int (Int64.mul (Int64.of_int a) (Int64.of_int b)))

(** val rEG_COUNT : int **)

let rEG_COUNT =
  (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
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
    (app ((word64 v)::[]) (skipn ((fun x -> x + 1) idx) s.vm_regs))

(** val read_mem : vMState -> int -> int **)

let read_mem s a =
  nth (mem_index a) s.vm_mem 0

(** val write_mem : vMState -> int -> int -> int list **)

let write_mem s a v =
  let idx = mem_index a in
  app (firstn idx s.vm_mem)
    (app ((word64 v)::[]) (skipn ((fun x -> x + 1) idx) s.vm_mem))

(** val bytes_to_word_4 : int -> int -> int -> int -> int **)

let bytes_to_word_4 = (fun b0 b1 b2 b3 -> b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24))

(** val word_to_bytes_4 : int -> char list **)

let word_to_bytes_4 = (fun w -> [Char.chr (w land 0xff); Char.chr ((w lsr 8) land 0xff); Char.chr ((w lsr 16) land 0xff); Char.chr ((w lsr 24) land 0xff)])

(** val bytes_to_words : char list -> int list **)

let rec bytes_to_words = function
| [] -> []
| a::l ->
  (match l with
   | [] -> (bytes_to_word_4 (nat_of_ascii a) 0 0 0)::[]
   | b::l0 ->
     (match l0 with
      | [] -> (bytes_to_word_4 (nat_of_ascii a) (nat_of_ascii b) 0 0)::[]
      | c::l1 ->
        (match l1 with
         | [] ->
           (bytes_to_word_4 (nat_of_ascii a) (nat_of_ascii b)
             (nat_of_ascii c) 0)::[]
         | d::rest ->
           (bytes_to_word_4 (nat_of_ascii a) (nat_of_ascii b)
             (nat_of_ascii c) (nat_of_ascii d))::(bytes_to_words rest))))

(** val words_to_bytes : int list -> int -> char list **)

let words_to_bytes ws n_bytes =
  firstn n_bytes (flat_map word_to_bytes_4 ws)

(** val list_read_at : int list -> int -> int **)

let list_read_at mem addr =
  nth addr mem 0

(** val mem_to_string : int list -> int -> char list **)

let mem_to_string mem base =
  let len = list_read_at mem base in
  let n_words =
    Nat.div
      (add len ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0))))
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0))))
  in
  let words =
    map (fun i -> list_read_at mem (add ((fun x -> x + 1) base) i))
      (seq 0 n_words)
  in
  string_of_list_ascii (words_to_bytes words len)

(** val write_words_at : int list -> int -> int list -> int list **)

let rec write_words_at mem addr = function
| [] -> mem
| w::rest ->
  write_words_at (list_update_at mem addr w) ((fun x -> x + 1) addr) rest

(** val write_string_to_mem : int list -> int -> char list -> int list **)

let write_string_to_mem mem base str =
  let chars = list_ascii_of_string str in
  let len = length chars in
  let words = bytes_to_words chars in
  let mem1 = list_update_at mem base len in
  write_words_at mem1 ((fun x -> x + 1) base) words

(** val memory_word_at : int list -> int -> int **)

let memory_word_at mem addr =
  list_read_at mem (mem_index addr)

(** val serialized_coupling_pair_count : int list -> int -> int **)

let serialized_coupling_pair_count mem base =
  Nat.min (memory_word_at mem base)
    (Nat.div mEM_SIZE ((fun x -> x + 1) ((fun x -> x + 1) 0)))

(** val load_coupling_pairs_from_mem :
    int list -> int -> int -> (int*int) list **)

let rec load_coupling_pairs_from_mem mem addr remaining =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> [])
    (fun remaining' ->
    ((memory_word_at mem addr),(memory_word_at mem ((fun x -> x + 1) addr)))::
    (load_coupling_pairs_from_mem mem
      (add addr ((fun x -> x + 1) ((fun x -> x + 1) 0))) remaining'))
    remaining

(** val pair_respects_regions : int list -> int list -> (int*int) -> bool **)

let pair_respects_regions src_region dst_region p =
  (&&) (nat_list_mem (fst p) src_region) (nat_list_mem (snd p) dst_region)

(** val restrict_coupling_to_regions :
    int list -> int list -> couplingData -> couplingData **)

let restrict_coupling_to_regions src_region dst_region c =
  { coupling_pairs =
    (filter (pair_respects_regions src_region dst_region) c.coupling_pairs);
    coupling_label = c.coupling_label }

(** val load_coupling_from_mem :
    vMState -> int list -> int list -> int -> couplingData **)

let load_coupling_from_mem s src_region dst_region base =
  let pair_count = serialized_coupling_pair_count s.vm_mem base in
  let label_base =
    add ((fun x -> x + 1) base)
      (mul ((fun x -> x + 1) ((fun x -> x + 1) 0)) pair_count)
  in
  let raw = { coupling_pairs =
    (load_coupling_pairs_from_mem s.vm_mem ((fun x -> x + 1) base) pair_count);
    coupling_label = (mem_to_string s.vm_mem (mem_index label_base)) }
  in
  restrict_coupling_to_regions src_region dst_region raw

(** val swap_regs : int list -> int -> int -> int list **)

let swap_regs regs a b =
  let a_idx = Nat.modulo a rEG_COUNT in
  let b_idx = Nat.modulo b rEG_COUNT in
  let va = nth a_idx regs 0 in
  let vb = nth b_idx regs 0 in
  let regs' =
    app (firstn a_idx regs)
      (app (vb::[]) (skipn ((fun x -> x + 1) a_idx) regs))
  in
  app (firstn b_idx regs')
    (app (va::[]) (skipn ((fun x -> x + 1) b_idx) regs'))

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
        (mul i ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
          ((fun x -> x + 1) 0))))) j) ms.module_mu_tensor 0
  | None -> 0

(** val graph_pnew : partitionGraph -> int list -> partitionGraph*moduleID **)

let graph_pnew g region =
  let normalized = normalize_region region in
  (match graph_find_region g normalized with
   | Some existing -> g,existing
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
    ((partitionGraph*moduleID)*moduleID) option **)

let graph_psplit g mid left right =
  match graph_lookup g mid with
  | Some m ->
    let axioms = m.module_axioms in
    let original = m.module_region in
    let left_norm = normalize_region left in
    let right_norm = normalize_region right in
    if (||) (Nat.eqb (length left_norm) 0) (Nat.eqb (length right_norm) 0)
    then let g',empty_id = graph_add_module g [] [] in
         Some ((g',mid),empty_id)
    else if partition_valid original left_norm right_norm
         then (match graph_remove g mid with
               | Some p ->
                 let g_removed,_ = p in
                 let g_left,left_id =
                   graph_add_module g_removed left_norm axioms
                 in
                 let g_right,right_id =
                   graph_add_module g_left right_norm axioms
                 in
                 Some ((g_right,left_id),right_id)
               | None -> None)
         else None
  | None -> None

(** val graph_pmerge :
    partitionGraph -> moduleID -> moduleID -> (partitionGraph*moduleID) option **)

let graph_pmerge g m1 m2 =
  if Nat.eqb m1 m2
  then None
  else (match graph_remove g m1 with
        | Some p ->
          let g1,mod1 = p in
          (match graph_remove g1 m2 with
           | Some p0 ->
             let g2,mod2 = p0 in
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
                        Some ((graph_update g2 existing updated),existing)
                      | None -> None)
                   | None ->
                     let g',merged_id =
                       graph_add_module g2 union combined_axioms
                     in
                     Some (g',merged_id))
           | None -> None)
        | None -> None)

type vm_instruction =
| Instr_pnew of int list * int
| Instr_psplit of moduleID * int list * int list * int
| Instr_pmerge of moduleID * moduleID * int
| Instr_lassert of int * int * bool * int * int
| Instr_ljoin of int * int * int
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
| Instr_lassert (_, _, _, flen, cost) ->
  add
    (mul flen ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) 0))))))))) ((fun x -> x + 1) cost)
| Instr_ljoin (_, _, cost) -> (fun x -> x + 1) cost
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
| Instr_emit (_, _, cost) -> (fun x -> x + 1) cost
| Instr_reveal (_, _, _, cost) -> (fun x -> x + 1) cost
| Instr_oracle_halts (_, _) ->
  of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 (D0 Nil))))))))
| Instr_halt cost -> cost
| Instr_checkpoint (_, cost) -> cost
| Instr_read_port (_, _, _, _, cost) -> (fun x -> x + 1) cost
| Instr_write_port (_, _, cost) -> cost
| Instr_heap_load (_, _, cost) -> cost
| Instr_heap_store (_, _, cost) -> cost
| Instr_certify cost -> (fun x -> x + 1) cost
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
| Instr_morph_assert (_, _, _, cost) -> (fun x -> x + 1) cost
| Instr_morph_tensor (_, _, _, cost) -> cost
| Instr_morph_get (_, _, _, cost) -> cost

(** val is_cert_setterb : vm_instruction -> bool **)

let is_cert_setterb = function
| Instr_pnew (_, _) -> false
| Instr_psplit (_, _, _, _) -> false
| Instr_pmerge (_, _, _) -> false
| Instr_lassert (_, _, _, _, _) -> true
| Instr_ljoin (_, _, _) -> true
| Instr_mdlacc (_, _) -> false
| Instr_pdiscover (_, _, _) -> false
| Instr_xfer (_, _, _) -> false
| Instr_load_imm (_, _, _) -> false
| Instr_load (_, _, _) -> false
| Instr_store (_, _, _) -> false
| Instr_add (_, _, _, _) -> false
| Instr_sub (_, _, _, _) -> false
| Instr_jump (_, _) -> false
| Instr_jnez (_, _, _) -> false
| Instr_call (_, _) -> false
| Instr_ret _ -> false
| Instr_chsh_trial (_, _, _, _, _) -> false
| Instr_xor_load (_, _, _) -> false
| Instr_xor_add (_, _, _) -> false
| Instr_xor_swap (_, _, _) -> false
| Instr_xor_rank (_, _, _) -> false
| Instr_emit (_, _, _) -> true
| Instr_reveal (_, _, _, _) -> true
| Instr_oracle_halts (_, _) -> false
| Instr_halt _ -> false
| Instr_checkpoint (_, _) -> false
| Instr_read_port (_, _, _, _, _) -> true
| Instr_write_port (_, _, _) -> false
| Instr_heap_load (_, _, _) -> false
| Instr_heap_store (_, _, _) -> false
| Instr_certify _ -> true
| Instr_and (_, _, _, _) -> false
| Instr_or (_, _, _, _) -> false
| Instr_shl (_, _, _, _) -> false
| Instr_shr (_, _, _, _) -> false
| Instr_mul (_, _, _, _) -> false
| Instr_lui (_, _, _) -> false
| Instr_tensor_set (_, _, _, _, _) -> false
| Instr_tensor_get (_, _, _, _, _) -> false
| Instr_morph (_, _, _, _, _) -> false
| Instr_compose (_, _, _, _) -> false
| Instr_morph_id (_, _, _) -> false
| Instr_morph_delete (_, _) -> false
| Instr_morph_assert (_, _, _, _) -> true
| Instr_morph_tensor (_, _, _, _) -> false
| Instr_morph_get (_, _, _, _) -> false

(** val is_bit : int -> bool **)

let is_bit n0 =
  (||) (Nat.eqb n0 0) (Nat.eqb n0 ((fun x -> x + 1) 0))

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
  let same = Nat.eqb a b in
  ((fun zero succ n -> if n=0 then zero () else succ (n-1))
     (fun _ ->
     (fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ ->
       if same
       then { wc_same_00 = ((fun x -> x + 1) wc.wc_same_00); wc_diff_00 =
              wc.wc_diff_00; wc_same_01 = wc.wc_same_01; wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = ((fun x -> x + 1)
              wc.wc_diff_00); wc_same_01 = wc.wc_same_01; wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = ((fun x -> x + 1) wc.wc_same_01); wc_diff_01 =
              wc.wc_diff_01; wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = ((fun x -> x + 1)
              wc.wc_diff_01); wc_same_10 = wc.wc_same_10; wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       y)
     (fun _ ->
     (fun zero succ n -> if n=0 then zero () else succ (n-1))
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = ((fun x -> x + 1) wc.wc_same_10); wc_diff_10 =
              wc.wc_diff_10; wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = ((fun x -> x + 1)
              wc.wc_diff_10); wc_same_11 = wc.wc_same_11; wc_diff_11 =
              wc.wc_diff_11 })
       (fun _ ->
       if same
       then { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = wc.wc_diff_10;
              wc_same_11 = ((fun x -> x + 1) wc.wc_same_11); wc_diff_11 =
              wc.wc_diff_11 }
       else { wc_same_00 = wc.wc_same_00; wc_diff_00 = wc.wc_diff_00;
              wc_same_01 = wc.wc_same_01; wc_diff_01 = wc.wc_diff_01;
              wc_same_10 = wc.wc_same_10; wc_diff_10 = wc.wc_diff_10;
              wc_same_11 = wc.wc_same_11; wc_diff_11 = ((fun x -> x + 1)
              wc.wc_diff_11) })
       y)
     x)

(** val lASSERT_TRAP_PC : int **)

let lASSERT_TRAP_PC =
  (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val lassert_check_ok : vMState -> int -> int -> bool -> bool **)

let lassert_check_ok s freg creg kind =
  let fbase = read_reg s freg in
  let cbase = read_reg s creg in
  let hw_flen = read_mem s fbase in
  let formula_words =
    map (fun i -> read_mem s (add fbase i))
      (seq 0
        (add ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0)))
          hw_flen))
  in
  let get_cert = fun var -> read_mem s (add cbase var) in
  if kind
  then CertCheck.check_model_binary_fn formula_words get_cert
  else false

(** val advance_state :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> bool -> vMState **)

let advance_state s instr graph csrs err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = s.vm_regs; vm_mem = s.vm_mem;
    vm_pc = ((fun x -> x + 1) s.vm_pc); vm_mu = (apply_cost s instr);
    vm_mu_tensor = s.vm_mu_tensor; vm_err = err_flag; vm_logic_acc =
    s.vm_logic_acc; vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness;
    vm_certified = s.vm_certified }

(** val advance_state_reveal :
    vMState -> vm_instruction -> int -> int -> partitionGraph -> cSRState ->
    bool -> vMState **)

let advance_state_reveal s instr flat_idx delta graph csrs err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = s.vm_regs; vm_mem = s.vm_mem;
    vm_pc = ((fun x -> x + 1) s.vm_pc); vm_mu = (apply_cost s instr);
    vm_mu_tensor = (vm_mu_tensor_add_at s flat_idx delta); vm_err = err_flag;
    vm_logic_acc = s.vm_logic_acc; vm_mstatus = s.vm_mstatus; vm_witness =
    s.vm_witness; vm_certified = s.vm_certified }

(** val advance_state_rm :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> int list ->
    int list -> bool -> vMState **)

let advance_state_rm s instr graph csrs regs mem err_flag =
  { vm_graph = graph; vm_csrs = csrs; vm_regs = regs; vm_mem = mem; vm_pc =
    ((fun x -> x + 1) s.vm_pc); vm_mu = (apply_cost s instr); vm_mu_tensor =
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
  let graph',_ = graph_pnew s.vm_graph region in
  advance_state s (Instr_pnew (region, cost)) graph' s.vm_csrs s.vm_err
| Instr_psplit (module0, left_region, right_region, cost) ->
  (match graph_psplit s.vm_graph module0 left_region right_region with
   | Some p ->
     let p0,_ = p in
     let graph',_ = p0 in
     advance_state s (Instr_psplit (module0, left_region, right_region,
       cost)) graph' s.vm_csrs s.vm_err
   | None ->
     advance_state s (Instr_psplit (module0, left_region, right_region,
       cost)) s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
       (latch_err s true))
| Instr_pmerge (m1, m2, cost) ->
  (match graph_pmerge s.vm_graph m1 m2 with
   | Some p ->
     let graph',_ = p in
     advance_state s (Instr_pmerge (m1, m2, cost)) graph' s.vm_csrs s.vm_err
   | None ->
     advance_state s (Instr_pmerge (m1, m2, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true))
| Instr_lassert (freg, creg, kind, flen, cost) ->
  let check_ok = lassert_check_ok s freg creg kind in
  let new_pc = if check_ok then (fun x -> x + 1) s.vm_pc else lASSERT_TRAP_PC
  in
  let new_err = if check_ok then s.vm_err else true in
  { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = s.vm_regs; vm_mem =
  s.vm_mem; vm_pc = new_pc; vm_mu =
  (apply_cost s (Instr_lassert (freg, creg, kind, flen, cost)));
  vm_mu_tensor = s.vm_mu_tensor; vm_err = new_err; vm_logic_acc =
  s.vm_logic_acc; vm_mstatus = s.vm_mstatus; vm_witness = s.vm_witness;
  vm_certified = s.vm_certified }
| Instr_ljoin (c1reg, c2reg, cost) ->
  advance_state s (Instr_ljoin (c1reg, c2reg, cost)) s.vm_graph s.vm_csrs
    s.vm_err
| Instr_mdlacc (module0, cost) ->
  advance_state s (Instr_mdlacc (module0, cost)) s.vm_graph s.vm_csrs s.vm_err
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
  if Nat.eqb (read_reg s rs) 0
  then advance_state s (Instr_jnez (rs, target, cost)) s.vm_graph s.vm_csrs
         s.vm_err
  else jump_state s (Instr_jnez (rs, target, cost)) target
| Instr_call (target, cost) ->
  let sp =
    read_reg s ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))))))))))))))))))))))))))))))
  in
  jump_state_rm s (Instr_call (target, cost)) target
    (write_reg s ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0))))))))))))))))))))))))))))))) (word64_add sp ((fun x -> x + 1) 0)))
    (write_mem s sp ((fun x -> x + 1) s.vm_pc))
| Instr_ret cost ->
  let sp =
    word64_sub
      (read_reg s ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))) ((fun x -> x + 1)
      0)
  in
  jump_state_rm s (Instr_ret cost) (read_mem s sp)
    (write_reg s ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0))))))))))))))))))))))))))))))) sp) s.vm_mem
| Instr_chsh_trial (x, y, a, b, cost) ->
  if chsh_bits_ok x y a b
  then { vm_graph = s.vm_graph; vm_csrs = s.vm_csrs; vm_regs = s.vm_regs;
         vm_mem = s.vm_mem; vm_pc = ((fun x -> x + 1) s.vm_pc); vm_mu =
         (apply_cost s (Instr_chsh_trial (x, y, a, b, cost))); vm_mu_tensor =
         s.vm_mu_tensor; vm_err = s.vm_err; vm_logic_acc = s.vm_logic_acc;
         vm_mstatus = s.vm_mstatus; vm_witness =
         (record_trial s.vm_witness x y a b); vm_certified = s.vm_certified }
  else advance_state s (Instr_chsh_trial (x, y, a, b, cost)) s.vm_graph
         (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true)
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
| Instr_oracle_halts (payload, cost) ->
  advance_state s (Instr_oracle_halts (payload, cost)) s.vm_graph s.vm_csrs
    s.vm_err
| Instr_halt cost ->
  advance_state s (Instr_halt cost) s.vm_graph s.vm_csrs s.vm_err
| Instr_checkpoint (label, cost) ->
  advance_state s (Instr_checkpoint (label, cost)) s.vm_graph s.vm_csrs
    s.vm_err
| Instr_read_port (dst, channel_idx, value, bits, cost) ->
  advance_state_rm s (Instr_read_port (dst, channel_idx, value, bits, cost))
    s.vm_graph s.vm_csrs (write_reg s dst value) s.vm_mem s.vm_err
| Instr_write_port (channel_idx, src, cost) ->
  advance_state s (Instr_write_port (channel_idx, src, cost)) s.vm_graph
    s.vm_csrs s.vm_err
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
    s.vm_mem; vm_pc = ((fun x -> x + 1) s.vm_pc); vm_mu =
    (add s.vm_mu ((fun x -> x + 1) delta_mu)); vm_mu_tensor = s.vm_mu_tensor;
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
      (word64_shl imm ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) 0)))))))))) s.vm_mem s.vm_err
| Instr_tensor_set (mid, i, j, value, cost) ->
  if (&&)
       (Nat.ltb i ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) 0)))))
       (Nat.ltb j ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) 0)))))
  then advance_state s (Instr_tensor_set (mid, i, j, value, cost))
         (let g = s.vm_graph in
          match graph_lookup g mid with
          | Some m ->
            let updated = { module_region = m.module_region; module_axioms =
              m.module_axioms; module_mu_tensor =
              (list_update_at m.module_mu_tensor
                (add
                  (mul i ((fun x -> x + 1) ((fun x -> x + 1)
                    ((fun x -> x + 1) ((fun x -> x + 1) 0))))) j) value) }
            in
            graph_update g mid updated
          | None -> g) s.vm_csrs s.vm_err
  else advance_state s (Instr_tensor_set (mid, i, j, value, cost)) s.vm_graph
         (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true)
| Instr_tensor_get (dst, mid, i, j, cost) ->
  if (&&)
       (Nat.ltb i ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) 0)))))
       (Nat.ltb j ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) 0)))))
  then advance_state_rm s (Instr_tensor_get (dst, mid, i, j, cost))
         s.vm_graph s.vm_csrs
         (write_reg s dst (module_tensor_entry s mid i j)) s.vm_mem s.vm_err
  else advance_state s (Instr_tensor_get (dst, mid, i, j, cost)) s.vm_graph
         (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true)
| Instr_morph (dst, src_mod, dst_mod, coupling_idx, cost) ->
  (match graph_lookup s.vm_graph src_mod with
   | Some src_state ->
     (match graph_lookup s.vm_graph dst_mod with
      | Some dst_state ->
        let c =
          load_coupling_from_mem s src_state.module_region
            dst_state.module_region coupling_idx
        in
        let graph',morph_id =
          graph_add_morphism s.vm_graph src_mod dst_mod c false
        in
        advance_state_rm s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
          cost)) graph' s.vm_csrs (write_reg s dst morph_id) s.vm_mem s.vm_err
      | None ->
        advance_state s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
          cost)) s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
          (latch_err s true))
   | None ->
     advance_state s (Instr_morph (dst, src_mod, dst_mod, coupling_idx,
       cost)) s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
       (latch_err s true))
| Instr_compose (dst, m1_id, m2_id, cost) ->
  (match graph_compose_morphisms s.vm_graph m1_id m2_id with
   | Some p ->
     let graph',new_id = p in
     advance_state_rm s (Instr_compose (dst, m1_id, m2_id, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_compose (dst, m1_id, m2_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true))
| Instr_morph_id (dst, module0, cost) ->
  (match graph_add_identity s.vm_graph module0 with
   | Some p ->
     let graph',new_id = p in
     advance_state_rm s (Instr_morph_id (dst, module0, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_morph_id (dst, module0, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true))
| Instr_morph_delete (morph_id, cost) ->
  (match graph_delete_morphism s.vm_graph morph_id with
   | Some graph' ->
     advance_state s (Instr_morph_delete (morph_id, cost)) graph' s.vm_csrs
       s.vm_err
   | None ->
     advance_state s (Instr_morph_delete (morph_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true))
| Instr_morph_assert (morph_id, property, cert, cost) ->
  (match graph_lookup_morphism s.vm_graph morph_id with
   | Some _ ->
     let csrs' = csr_set_err (csr_set_status s.vm_csrs ((fun x -> x + 1) 0)) 0
     in
     advance_state s (Instr_morph_assert (morph_id, property, cert, cost))
       s.vm_graph (csr_set_cert_addr csrs' (ascii_checksum property)) s.vm_err
   | None ->
     advance_state s (Instr_morph_assert (morph_id, property, cert, cost))
       s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
       (latch_err s true))
| Instr_morph_tensor (dst, f_id, g_id, cost) ->
  (match graph_tensor_morphisms s.vm_graph f_id g_id with
   | Some p ->
     let graph',new_id = p in
     advance_state_rm s (Instr_morph_tensor (dst, f_id, g_id, cost)) graph'
       s.vm_csrs (write_reg s dst new_id) s.vm_mem s.vm_err
   | None ->
     advance_state s (Instr_morph_tensor (dst, f_id, g_id, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (latch_err s true))
| Instr_morph_get (dst, morph_id, selector, cost) ->
  (match graph_lookup_morphism s.vm_graph morph_id with
   | Some ms ->
     let value =
       (fun zero succ n -> if n=0 then zero () else succ (n-1))
         (fun _ -> ms.morph_source)
         (fun n0 ->
         (fun zero succ n -> if n=0 then zero () else succ (n-1))
           (fun _ -> ms.morph_target)
           (fun n1 ->
           (fun zero succ n -> if n=0 then zero () else succ (n-1))
             (fun _ -> length ms.morph_coupling.coupling_pairs)
             (fun n2 ->
             (fun zero succ n -> if n=0 then zero () else succ (n-1))
               (fun _ ->
               if ms.morph_is_identity then (fun x -> x + 1) 0 else 0)
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
       s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
       (latch_err s true))

(** val nofi_step_cost_okb : vm_instruction -> bool **)

let nofi_step_cost_okb instr =
  if is_cert_setterb instr
  then (<=) ((fun x -> x + 1) 0) (instruction_cost instr)
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
| BusRegSetActiveModule
| BusRegSetTrapVector

(** val decodeBusReg : int -> busReg option **)

let decodeBusReg addr =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> Some BusRegPc)
    (fun n0 ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> None)
      (fun n1 ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> None)
        (fun n2 ->
        (fun zero succ n -> if n=0 then zero () else succ (n-1))
          (fun _ -> None)
          (fun n3 ->
          (fun zero succ n -> if n=0 then zero () else succ (n-1))
            (fun _ -> Some BusRegMu)
            (fun n4 ->
            (fun zero succ n -> if n=0 then zero () else succ (n-1))
              (fun _ -> None)
              (fun n5 ->
              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                (fun _ -> None)
                (fun n6 ->
                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                  (fun _ -> None)
                  (fun n7 ->
                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                    (fun _ -> Some BusRegErr)
                    (fun n8 ->
                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                      (fun _ -> None)
                      (fun n9 ->
                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                        (fun _ -> None)
                        (fun n10 ->
                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                          (fun _ -> None)
                          (fun n11 ->
                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                            (fun _ -> Some BusRegHalted)
                            (fun n12 ->
                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                              (fun _ -> None)
                              (fun n13 ->
                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                (fun _ -> None)
                                (fun n14 ->
                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                  (fun _ -> None)
                                  (fun n15 ->
                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                    (fun _ -> Some
                                    BusRegPartitionOps)
                                    (fun n16 ->
                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                      (fun _ -> None)
                                      (fun n17 ->
                                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                        (fun _ -> None)
                                        (fun n18 ->
                                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                          (fun _ -> None)
                                          (fun n19 ->
                                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                            (fun _ -> Some
                                            BusRegMdlOps)
                                            (fun n20 ->
                                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                              (fun _ -> None)
                                              (fun n21 ->
                                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                (fun _ -> None)
                                                (fun n22 ->
                                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                  (fun _ -> None)
                                                  (fun n23 ->
                                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                    (fun _ -> Some
                                                    BusRegInfoGain)
                                                    (fun n24 ->
                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                      (fun _ ->
                                                      None)
                                                      (fun n25 ->
                                                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                        (fun _ ->
                                                        None)
                                                        (fun n26 ->
                                                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                          (fun _ ->
                                                          None)
                                                          (fun n27 ->
                                                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                            (fun _ -> Some
                                                            BusRegErrorCode)
                                                            (fun n28 ->
                                                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                              (fun _ ->
                                                              None)
                                                              (fun n29 ->
                                                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                (fun _ ->
                                                                None)
                                                                (fun n30 ->
                                                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                  (fun _ ->
                                                                  None)
                                                                  (fun n31 ->
                                                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMstatus)
                                                                    (fun n32 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n33 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n34 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n35 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMcycleLo)
                                                                    (fun n36 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n37 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n38 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n39 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMcycleHi)
                                                                    (fun n40 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n41 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n42 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n43 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMinstretLo)
                                                                    (fun n44 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n45 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n46 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n47 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMinstretHi)
                                                                    (fun n48 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n49 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n50 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n51 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLogicAcc)
                                                                    (fun n52 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n53 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n54 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n55 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n56 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n57 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n58 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n59 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n60 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n61 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n62 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n63 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n64 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n65 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n66 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n67 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor0)
                                                                    (fun n68 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n69 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n70 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n71 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor1)
                                                                    (fun n72 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n73 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n74 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n75 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor2)
                                                                    (fun n76 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n77 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n78 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n79 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegMuTensor3)
                                                                    (fun n80 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n81 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n82 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n83 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegBianchiAlarm)
                                                                    (fun n84 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n85 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n86 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n87 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegPtNextId)
                                                                    (fun n88 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n89 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n90 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n91 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegPtSize)
                                                                    (fun n92 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n93 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n94 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n95 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n96 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n97 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n98 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n99 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n100 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n101 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n102 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n103 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n104 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n105 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n106 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n107 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n108 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n109 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n110 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n111 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n112 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n113 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n114 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n115 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n116 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n117 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n118 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n119 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n120 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n121 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n122 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n123 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n124 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n125 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n126 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n127 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrAddr)
                                                                    (fun n128 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n129 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n130 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n131 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrData)
                                                                    (fun n132 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n133 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n134 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n135 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegLoadInstrKick)
                                                                    (fun n136 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n137 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n138 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n139 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n140 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n141 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n142 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n143 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n144 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n145 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n146 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n147 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n148 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n149 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n150 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n151 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    Some
                                                                    BusRegSetActiveModule)
                                                                    (fun n152 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n153 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n154 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    None)
                                                                    (fun n155 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
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
| BusRegPc -> true
| BusRegMu -> true
| BusRegErr -> true
| BusRegHalted -> true
| BusRegPartitionOps -> true
| BusRegMdlOps -> true
| BusRegInfoGain -> true
| BusRegErrorCode -> true
| BusRegMstatus -> true
| BusRegMcycleLo -> true
| BusRegMcycleHi -> true
| BusRegMinstretLo -> true
| BusRegMinstretHi -> true
| BusRegLogicAcc -> true
| BusRegMuTensor0 -> true
| BusRegMuTensor1 -> true
| BusRegMuTensor2 -> true
| BusRegMuTensor3 -> true
| BusRegBianchiAlarm -> true
| BusRegPtNextId -> true
| BusRegPtSize -> true
| BusRegLoadInstrAddr -> false
| BusRegLoadInstrData -> false
| BusRegLoadInstrKick -> false
| BusRegSetActiveModule -> false
| BusRegSetTrapVector -> false

(** val busRegWritable : busReg -> bool **)

let busRegWritable r =
  negb (busRegReadable r)

type busCoreView = { view_pc : int; view_mu : int; view_err : bool;
                     view_halted : bool; view_partition_ops : int;
                     view_mdl_ops : int; view_info_gain : int;
                     view_error_code : int; view_mstatus : int;
                     view_mcycle_lo : int; view_mcycle_hi : int;
                     view_minstret_lo : int; view_minstret_hi : int;
                     view_logic_acc : int; view_mu_tensor0 : int;
                     view_mu_tensor1 : int; view_mu_tensor2 : int;
                     view_mu_tensor3 : int; view_bianchi_alarm : bool;
                     view_pt_next_id : int; view_pt_size : (int -> int) }

(** val bool_to_nat : bool -> int **)

let bool_to_nat = function
| true -> (fun x -> x + 1) 0
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
| BusRegMuTensor0 -> Some v.view_mu_tensor0
| BusRegMuTensor1 -> Some v.view_mu_tensor1
| BusRegMuTensor2 -> Some v.view_mu_tensor2
| BusRegMuTensor3 -> Some v.view_mu_tensor3
| BusRegBianchiAlarm -> Some (bool_to_nat v.view_bianchi_alarm)
| BusRegPtNextId -> Some v.view_pt_next_id
| BusRegPtSize -> Some (v.view_pt_size 0)
| BusRegLoadInstrAddr -> None
| BusRegLoadInstrData -> None
| BusRegLoadInstrKick -> None
| BusRegSetActiveModule -> None
| BusRegSetTrapVector -> None

(** val busRead : busCoreView -> int -> int option **)

let busRead v addr =
  match decodeBusReg addr with
  | Some r -> if busRegReadable r then busRegReadValue v r else None
  | None -> None

type busShadowRegs = { sh_load_instr_addr : int; sh_load_instr_data : 
                       int; sh_load_instr_kick : bool;
                       sh_active_module : int; sh_trap_vector : int }

type busWrapperState = { bw_core : kamiSnapshot; bw_shadow : busShadowRegs }

(** val busWriteShadow : busShadowRegs -> busReg -> int -> busShadowRegs **)

let busWriteShadow s r data =
  match r with
  | BusRegPc -> s
  | BusRegMu -> s
  | BusRegErr -> s
  | BusRegHalted -> s
  | BusRegPartitionOps -> s
  | BusRegMdlOps -> s
  | BusRegInfoGain -> s
  | BusRegErrorCode -> s
  | BusRegMstatus -> s
  | BusRegMcycleLo -> s
  | BusRegMcycleHi -> s
  | BusRegMinstretLo -> s
  | BusRegMinstretHi -> s
  | BusRegLogicAcc -> s
  | BusRegMuTensor0 -> s
  | BusRegMuTensor1 -> s
  | BusRegMuTensor2 -> s
  | BusRegMuTensor3 -> s
  | BusRegBianchiAlarm -> s
  | BusRegPtNextId -> s
  | BusRegPtSize -> s
  | BusRegLoadInstrAddr ->
    { sh_load_instr_addr = data; sh_load_instr_data = s.sh_load_instr_data;
      sh_load_instr_kick = s.sh_load_instr_kick; sh_active_module =
      s.sh_active_module; sh_trap_vector = s.sh_trap_vector }
  | BusRegLoadInstrData ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data = data;
      sh_load_instr_kick = s.sh_load_instr_kick; sh_active_module =
      s.sh_active_module; sh_trap_vector = s.sh_trap_vector }
  | BusRegLoadInstrKick ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = (negb (Nat.eqb data 0));
      sh_active_module = s.sh_active_module; sh_trap_vector =
      s.sh_trap_vector }
  | BusRegSetActiveModule ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_active_module = data; sh_trap_vector = s.sh_trap_vector }
  | BusRegSetTrapVector ->
    { sh_load_instr_addr = s.sh_load_instr_addr; sh_load_instr_data =
      s.sh_load_instr_data; sh_load_instr_kick = s.sh_load_instr_kick;
      sh_active_module = s.sh_active_module; sh_trap_vector = data }

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
    view_logic_acc = 0; view_mu_tensor0 = (s.snap_mu_tensor 0);
    view_mu_tensor1 = (s.snap_mu_tensor ((fun x -> x + 1) 0));
    view_mu_tensor2 =
    (s.snap_mu_tensor ((fun x -> x + 1) ((fun x -> x + 1) 0)));
    view_mu_tensor3 =
    (s.snap_mu_tensor ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
      0)))); view_bianchi_alarm = false; view_pt_next_id = s.snap_pt_next_id;
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
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> s)
    (fun k ->
    pnew_chain k (vm_apply s (Instr_pnew (region, cost))) region cost)
    n0
