
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

let rec length = function
| [] -> 0
| _::l' -> (fun x -> x + 1) (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> m)
      (fun p -> (fun x -> x + 1) (add p m))
      n0

  (** val mul : int -> int -> int **)

  let rec mul n0 m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) ((fun x -> x + 1) n0) m

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

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

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
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> zero)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one)
        p)
      n0
  in loop ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
       ((fun x -> x + 1) ((fun x -> x + 1) 0))))))))

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

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> match l with
              | [] -> default
              | x::_ -> x)
    (fun m -> match l with
              | [] -> default
              | _::t -> nth m t default)
    n0

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t -> (f a)::(map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t -> f b (fold_right f a0 t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a::l0 -> a::(firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _::l0 -> skipn n1 l0)
    n0

(** val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec nodup decA = function
| [] -> []
| x::xs -> if in_dec decA x xs then nodup decA xs else x::(nodup decA xs)

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

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s0 -> ch::(list_ascii_of_string s0)

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

(** val nat_list_mem : int -> int list -> bool **)

let rec nat_list_mem x = function
| [] -> false
| y::ys -> if (=) x y then true else nat_list_mem x ys

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

type moduleState = { module_region : int list; module_axioms : axiomSet }

(** val normalize_module : moduleState -> moduleState **)

let normalize_module m =
  { module_region = (normalize_region m.module_region); module_axioms =
    m.module_axioms }

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID*moduleState) list }

(** val graph_lookup_modules :
    (moduleID*moduleState) list -> moduleID -> moduleState option **)

let rec graph_lookup_modules modules mid =
  match modules with
  | [] -> None
  | p::rest ->
    let id,m = p in
    if (=) id mid then Some m else graph_lookup_modules rest mid

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
    if (=) id mid
    then (mid,m)::rest
    else (id,existing)::(graph_insert_modules rest mid m)

(** val graph_update :
    partitionGraph -> moduleID -> moduleState -> partitionGraph **)

let graph_update g mid m =
  { pg_next_id = g.pg_next_id; pg_modules =
    (graph_insert_modules g.pg_modules mid (normalize_module m)) }

(** val graph_remove_modules :
    (moduleID*moduleState) list -> moduleID -> ((moduleID*moduleState)
    list*moduleState) option **)

let rec graph_remove_modules modules mid =
  match modules with
  | [] -> None
  | p::rest ->
    let id,m = p in
    if (=) id mid
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
    Some ({ pg_next_id = g.pg_next_id; pg_modules = modules' },removed)
  | None -> None

(** val graph_add_module :
    partitionGraph -> int list -> axiomSet -> partitionGraph*moduleID **)

let graph_add_module g region axioms =
  let module0 =
    normalize_module { module_region = region; module_axioms = axioms }
  in
  let mid = g.pg_next_id in
  { pg_next_id = ((fun x -> x + 1) mid); pg_modules =
  ((mid,module0)::g.pg_modules) },mid

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

(** val graph_add_axiom :
    partitionGraph -> moduleID -> vMAxiom -> partitionGraph **)

let graph_add_axiom g mid ax =
  match graph_lookup g mid with
  | Some m ->
    let updated = { module_region = m.module_region; module_axioms =
      (app m.module_axioms (ax::[])) }
    in
    graph_update g mid updated
  | None -> g

(** val graph_add_axioms :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_add_axioms g mid axs =
  fold_left (fun acc ax -> graph_add_axiom acc mid ax) axs g

(** val graph_record_discovery :
    partitionGraph -> moduleID -> vMAxiom list -> partitionGraph **)

let graph_record_discovery =
  graph_add_axioms

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
    if (||) ((=) (length left_norm) 0) ((=) (length right_norm) 0)
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
  if (=) m1 m2
  then None
  else (match graph_remove g m1 with
        | Some p ->
          let g_without_m1,mod1 = p in
          (match graph_remove g_without_m1 m2 with
           | Some p0 ->
             let g_without_both,mod2 = p0 in
             if negb (nat_list_disjoint mod1.module_region mod2.module_region)
             then None
             else let union =
                    nat_list_union mod1.module_region mod2.module_region
                  in
                  let combined_axioms =
                    app mod1.module_axioms mod2.module_axioms
                  in
                  (match graph_find_region g_without_both union with
                   | Some existing ->
                     (match graph_lookup g_without_both existing with
                      | Some existing_mod ->
                        let updated = { module_region =
                          existing_mod.module_region; module_axioms =
                          (app existing_mod.module_axioms combined_axioms) }
                        in
                        Some
                        ((graph_update g_without_both existing updated),existing)
                      | None -> None)
                   | None ->
                     Some
                       (graph_add_module g_without_both union combined_axioms))
           | None -> None)
        | None -> None)

type cSRState = { csr_cert_addr : int; csr_status : int; csr_err : int }

(** val csr_set_status : cSRState -> int -> cSRState **)

let csr_set_status csrs status =
  { csr_cert_addr = csrs.csr_cert_addr; csr_status = status; csr_err =
    csrs.csr_err }

(** val csr_set_err : cSRState -> int -> cSRState **)

let csr_set_err csrs err =
  { csr_cert_addr = csrs.csr_cert_addr; csr_status = csrs.csr_status;
    csr_err = err }

(** val csr_set_cert_addr : cSRState -> int -> cSRState **)

let csr_set_cert_addr csrs addr =
  { csr_cert_addr = addr; csr_status = csrs.csr_status; csr_err =
    csrs.csr_err }

type vMState = { vm_graph : partitionGraph; vm_csrs : cSRState;
                 vm_regs : int list; vm_mem : int list; vm_pc : int;
                 vm_mu : int; vm_err : bool }

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
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val word32 : int -> int **)

let word32 = (fun x -> x land 0xFFFFFFFF)

(** val word32_xor : int -> int -> int **)

let word32_xor = (fun a b -> (a lxor b) land 0xFFFFFFFF)

(** val word32_popcount : int -> int **)

let word32_popcount = (fun x -> let v = x land 0xFFFFFFFF in let rec pc v acc = if v = 0 then acc else pc (v land (v - 1)) (acc + 1) in pc v 0)

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
    (app ((word32 v)::[]) (skipn ((fun x -> x + 1) idx) s.vm_regs))

(** val read_mem : vMState -> int -> int **)

let read_mem s a =
  nth (mem_index a) s.vm_mem 0

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

module CertCheck =
 struct
  (** val string_to_list : char list -> char list **)

  let rec string_to_list = function
  | [] -> []
  | c::s' -> c::(string_to_list s')

  (** val list_to_string : char list -> char list **)

  let rec list_to_string = function
  | [] -> []
  | c::l' -> c::(list_to_string l')

  (** val ascii_nat : char -> int **)

  let ascii_nat =
    nat_of_ascii

  (** val is_space : char -> bool **)

  let is_space c =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun n0 ->
      (fun zero succ n -> if n=0 then zero () else succ (n-1))
        (fun _ -> false)
        (fun n1 ->
        (fun zero succ n -> if n=0 then zero () else succ (n-1))
          (fun _ -> false)
          (fun n2 ->
          (fun zero succ n -> if n=0 then zero () else succ (n-1))
            (fun _ -> false)
            (fun n3 ->
            (fun zero succ n -> if n=0 then zero () else succ (n-1))
              (fun _ -> false)
              (fun n4 ->
              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                (fun _ -> false)
                (fun n5 ->
                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                  (fun _ -> false)
                  (fun n6 ->
                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                    (fun _ -> false)
                    (fun n7 ->
                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                      (fun _ -> false)
                      (fun n8 ->
                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                        (fun _ -> true)
                        (fun n9 ->
                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                          (fun _ -> true)
                          (fun n10 ->
                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                            (fun _ -> false)
                            (fun n11 ->
                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                              (fun _ -> false)
                              (fun n12 ->
                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                (fun _ -> true)
                                (fun n13 ->
                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                  (fun _ -> false)
                                  (fun n14 ->
                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                    (fun _ -> false)
                                    (fun n15 ->
                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                      (fun _ -> false)
                                      (fun n16 ->
                                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                        (fun _ -> false)
                                        (fun n17 ->
                                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                          (fun _ -> false)
                                          (fun n18 ->
                                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                            (fun _ -> false)
                                            (fun n19 ->
                                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                              (fun _ -> false)
                                              (fun n20 ->
                                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                (fun _ -> false)
                                                (fun n21 ->
                                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                  (fun _ -> false)
                                                  (fun n22 ->
                                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                    (fun _ ->
                                                    false)
                                                    (fun n23 ->
                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                      (fun _ ->
                                                      false)
                                                      (fun n24 ->
                                                      (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                        (fun _ ->
                                                        false)
                                                        (fun n25 ->
                                                        (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                          (fun _ ->
                                                          false)
                                                          (fun n26 ->
                                                          (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                            (fun _ ->
                                                            false)
                                                            (fun n27 ->
                                                            (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                              (fun _ ->
                                                              false)
                                                              (fun n28 ->
                                                              (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                (fun _ ->
                                                                false)
                                                                (fun n29 ->
                                                                (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                  (fun _ ->
                                                                  false)
                                                                  (fun n30 ->
                                                                  (fun zero succ n -> if n=0 then zero () else succ (n-1))
                                                                    (fun _ ->
                                                                    false)
                                                                    (fun n31 ->
                                                                    (fun zero succ n -> if n=0 then zero () else succ (n-1))
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
  | c::l' -> if is_space c then trim_left_list l' else l

  (** val trim_left : char list -> char list **)

  let trim_left s =
    list_to_string (trim_left_list (string_to_list s))

  (** val split_lines_aux : char list -> char list -> char list list **)

  let rec split_lines_aux l cur =
    match l with
    | [] -> (rev cur)::[]
    | c::l' ->
      if (=) (ascii_nat c) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) 0))))))))))
      then (rev cur)::(split_lines_aux l' [])
      else split_lines_aux l' (c::cur)

  (** val split_lines : char list -> char list list **)

  let split_lines s =
    map list_to_string (split_lines_aux (string_to_list s) [])

  (** val split_ws_aux : char list -> char list -> char list list **)

  let rec split_ws_aux l cur =
    match l with
    | [] -> (match rev cur with
             | [] -> []
             | a::l0 -> (a::l0)::[])
    | c::l' ->
      if is_space c
      then (match rev cur with
            | [] -> split_ws_aux l' []
            | a::l0 -> (a::l0)::(split_ws_aux l' []))
      else split_ws_aux l' (c::cur)

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
      ((<=) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        0)))))))))))))))))))))))))))))))))))))))))))))))) n0)
      ((<=) n0 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val parse_nat_digits : char list -> int -> int option **)

  let rec parse_nat_digits l acc =
    match l with
    | [] -> Some acc
    | c::l' ->
      if is_digit c
      then let d =
             Nat.sub (ascii_nat c) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
               ((fun x -> x + 1)
               0))))))))))))))))))))))))))))))))))))))))))))))))
           in
           parse_nat_digits l'
             (Nat.add
               (Nat.mul ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                 ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                 ((fun x -> x + 1) 0)))))))))) acc) d)
      else None

  (** val parse_int : char list -> int option **)

  let parse_int s =
    let l = string_to_list (trim_left s) in
    (match l with
     | [] -> None
     | c::rest ->
       if (=) c
            (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
              ((fun x -> x + 1)
              0))))))))))))))))))))))))))))))))))))))))))))))
       then (match parse_nat_digits rest 0 with
             | Some n0 -> Some (Z.opp (Z.of_nat n0))
             | None -> None)
       else if (=) c
                 (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                   ((fun x -> x + 1) ((fun x -> x + 1)
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
    | Some z0 -> if Z.ltb z0 0 then None else Some (Z.to_nat z0)
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
      | z0::l' -> if Z.eqb z0 0 then rev acc else go l' (z0::acc)
    in go zs []

  (** val parse_clause_tokens : char list list -> int list option **)

  let parse_clause_tokens toks =
    let ints =
      let rec go ts acc =
        match ts with
        | [] -> Some (rev acc)
        | t::ts' ->
          (match parse_int t with
           | Some z0 -> go ts' (z0::acc)
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
      | line::ls' ->
        let line' = trim_left line in
        (match line' with
         | [] -> go ls' num_vars clauses
         | c::_ ->
           if (=) c
                (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1)
                  0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           then go ls' num_vars clauses
           else if (=) c
                     (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                       ((fun x -> x + 1) ((fun x -> x + 1)
                       0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                then let toks = split_ws line' in
                     (match toks with
                      | [] -> None
                      | _::l ->
                        (match l with
                         | [] -> None
                         | _::l0 ->
                           (match l0 with
                            | [] -> None
                            | nv::l1 ->
                              (match l1 with
                               | [] -> None
                               | _::_ ->
                                 (match parse_nat nv with
                                  | Some nv' -> go ls' (Some nv') clauses
                                  | None -> None)))))
                else (match parse_clause_tokens (split_ws line') with
                      | Some cl -> go ls' num_vars (cl::clauses)
                      | None -> None))
    in go lines None []

  (** val lookup_bool : int -> (int*bool) list -> bool option **)

  let rec lookup_bool x = function
  | [] -> None
  | p::m' -> let k,v = p in if (=) k x then Some v else lookup_bool x m'

  (** val insert_bool : int -> bool -> (int*bool) list -> (int*bool) list **)

  let insert_bool x v m =
    (x,v)::m

  (** val remove_prefix_v : char list -> char list **)

  let remove_prefix_v s = match s with
  | [] -> s
  | c::rest ->
    if (||)
         ((=) c
           (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1)
             0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ((=) c
           (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
             0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    then rest
    else s

  (** val split_on_eq_aux :
      char list -> char list -> (char list*char list) option **)

  let rec split_on_eq_aux l acc =
    match l with
    | [] -> None
    | c::l' ->
      if (=) (ascii_nat c) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
           ((fun x -> x + 1) ((fun x -> x + 1)
           0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      then Some ((rev acc),l')
      else split_on_eq_aux l' (c::acc)

  (** val split_on_eq : char list -> (char list*char list) option **)

  let split_on_eq s =
    match split_on_eq_aux (string_to_list s) [] with
    | Some p ->
      let l1,l2 = p in Some ((list_to_string l1),(list_to_string l2))
    | None -> None

  (** val value_is_false : char list -> bool **)

  let value_is_false s =
    let t = trim_left s in
    (||) (eqb0 t ('0'::[]))
      ((||) (eqb0 t ('f'::('a'::('l'::('s'::('e'::[])))))) (eqb0 t ('f'::[])))

  (** val parse_assignment_token : char list -> (int*bool) option **)

  let parse_assignment_token tok =
    if eqb0 tok ('0'::[])
    then None
    else (match split_on_eq tok with
          | Some p ->
            let lhs,rhs = p in
            (match parse_nat (remove_prefix_v lhs) with
             | Some var -> Some (var,(negb (value_is_false rhs)))
             | None -> None)
          | None ->
            (match parse_int tok with
             | Some lit ->
               if Z.eqb lit 0
               then None
               else let var = Z.to_nat (Z.abs lit) in Some (var,(Z.gtb lit 0))
             | None -> None))

  (** val parse_assignment : char list -> (int*bool) list option **)

  let parse_assignment text =
    let toks = split_ws text in
    let rec go ts acc =
      match ts with
      | [] -> Some acc
      | t::ts' ->
        (match parse_assignment_token t with
         | Some p -> let var,v = p in go ts' (insert_bool var v acc)
         | None -> go ts' acc)
    in go toks []

  (** val clause_satisfied : (int*bool) list -> int list -> bool **)

  let rec clause_satisfied asgn = function
  | [] -> false
  | lit::lits' ->
    let var = Z.to_nat (Z.abs lit) in
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

  (** val assoc_remove : int -> (int*int list) list -> (int*int list) list **)

  let assoc_remove k db =
    filter (fun kv -> negb ((=) (fst kv) k)) db

  (** val db_clauses : (int*int list) list -> int list list **)

  let db_clauses db =
    map snd db

  (** val eval_clause : (int*bool) list -> int list -> bool*int list **)

  let eval_clause asgn cl =
    let rec go lits undec =
      match lits with
      | [] -> false,(rev undec)
      | lit::lits' ->
        let var = Z.to_nat (Z.abs lit) in
        (match lookup_bool var asgn with
         | Some b -> if eqb b (Z.gtb lit 0) then true,[] else go lits' undec
         | None -> go lits' (lit::undec))
    in go cl []

  (** val unit_conflict_fuel :
      int -> int -> int list list -> (int*bool) list -> int list -> bool **)

  let rec unit_conflict_fuel fuel num_vars clauses asgn queue =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> false)
      (fun fuel' ->
      match queue with
      | [] -> false
      | lit::queue' ->
        let var = Z.to_nat (Z.abs lit) in
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
               | cl::cls' ->
                 let sat,undec = eval_clause asgn' cl in
                 if sat
                 then scan cls' q
                 else (match undec with
                       | [] -> None
                       | u::l ->
                         (match l with
                          | [] -> scan cls' (u::q)
                          | _::_ -> scan cls' q))
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
        | u::l -> (match l with
                   | [] -> u::acc
                   | _::_ -> acc)) [] clauses
    in
    let queue = app assumptions unit_lits in
    let fuel =
      add (add num_vars (length queue)) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
        ((fun x -> x + 1) ((fun x -> x + 1) 0))))))))))
    in
    unit_conflict_fuel fuel num_vars clauses [] queue

  (** val verify_rup_clause :
      int -> (int*int list) list -> int list -> bool **)

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
      | t::ts' ->
        (match parse_nat t with
         | Some n0 -> if (=) n0 0 then Some (rev acc) else go ts' (n0::acc)
         | None -> None)
    in go toks []

  (** val parse_z_list : char list list -> int list option **)

  let parse_z_list toks =
    let rec go ts acc =
      match ts with
      | [] -> Some (rev acc)
      | t::ts' ->
        (match parse_int t with
         | Some z0 -> if Z.eqb z0 0 then Some (rev acc) else go ts' (z0::acc)
         | None -> None)
    in go toks []

  (** val drop_until_zero : char list list -> char list list **)

  let rec drop_until_zero = function
  | [] -> []
  | t::ts' -> if eqb0 t ('0'::[]) then ts' else drop_until_zero ts'

  (** val parse_lrat_line : char list -> lrat_step option **)

  let parse_lrat_line line =
    let t = trim_left line in
    if eqb0 t []
    then None
    else if starts_with_char
              (ascii_of_nat ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                ((fun x -> x + 1)
                0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              t
         then None
         else let toks = split_ws t in
              (match toks with
               | [] -> None
               | first::rest ->
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

  (** val build_initial_db : int list list -> int -> (int*int list) list **)

  let rec build_initial_db clauses idx =
    match clauses with
    | [] -> []
    | cl::cls -> (idx,cl)::(build_initial_db cls ((fun x -> x + 1) idx))

  (** val apply_deletions :
      (int*int list) list -> int list -> (int*int list) list **)

  let rec apply_deletions db = function
  | [] -> db
  | d::ds -> apply_deletions (assoc_remove d db) ds

  (** val check_lrat_lines :
      int -> char list list -> (int*int list) list -> bool -> bool **)

  let rec check_lrat_lines num_vars lines db derived_empty =
    match lines with
    | [] -> derived_empty
    | line::lines' ->
      (match parse_lrat_line line with
       | Some st ->
         if st.lrat_is_delete
         then check_lrat_lines num_vars lines'
                (apply_deletions db st.lrat_deletions) derived_empty
         else if verify_rup_clause num_vars db st.lrat_clause
              then let db' =
                     (st.lrat_id,st.lrat_clause)::(apply_deletions db
                                                    st.lrat_deletions)
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
      let db = build_initial_db cnf.cnf_clauses ((fun x -> x + 1) 0) in
      check_lrat_lines cnf.cnf_num_vars (split_lines proof_text) db false
    | None -> false
 end

module VMStep =
 struct
  (** val check_lrat : char list -> char list -> bool **)

  let check_lrat =
    CertCheck.check_lrat

  (** val check_model : char list -> char list -> bool **)

  let check_model =
    CertCheck.check_model

  type lassert_certificate =
  | Coq_lassert_cert_unsat of char list
  | Coq_lassert_cert_sat of char list

  type vm_instruction =
  | Coq_instr_pnew of int list * int
  | Coq_instr_psplit of moduleID * int list * int list * int
  | Coq_instr_pmerge of moduleID * moduleID * int
  | Coq_instr_lassert of moduleID * char list * lassert_certificate * int
  | Coq_instr_ljoin of char list * char list * int
  | Coq_instr_mdlacc of moduleID * int
  | Coq_instr_pdiscover of moduleID * vMAxiom list * int
  | Coq_instr_xfer of int * int * int
  | Coq_instr_pyexec of char list * int
  | Coq_instr_chsh_trial of int * int * int * int * int
  | Coq_instr_xor_load of int * int * int
  | Coq_instr_xor_add of int * int * int
  | Coq_instr_xor_swap of int * int * int
  | Coq_instr_xor_rank of int * int * int
  | Coq_instr_emit of moduleID * char list * int
  | Coq_instr_reveal of moduleID * int * char list * int
  | Coq_instr_oracle_halts of char list * int
  | Coq_instr_halt of int

  (** val instruction_cost : vm_instruction -> int **)

  let instruction_cost = function
  | Coq_instr_pnew (_, cost) -> cost
  | Coq_instr_psplit (_, _, _, cost) -> cost
  | Coq_instr_pmerge (_, _, cost) -> cost
  | Coq_instr_lassert (_, _, _, cost) -> cost
  | Coq_instr_ljoin (_, _, cost) -> cost
  | Coq_instr_mdlacc (_, cost) -> cost
  | Coq_instr_pdiscover (_, _, cost) -> cost
  | Coq_instr_xfer (_, _, cost) -> cost
  | Coq_instr_pyexec (_, cost) -> cost
  | Coq_instr_chsh_trial (_, _, _, _, cost) -> cost
  | Coq_instr_xor_load (_, _, cost) -> cost
  | Coq_instr_xor_add (_, _, cost) -> cost
  | Coq_instr_xor_swap (_, _, cost) -> cost
  | Coq_instr_xor_rank (_, _, cost) -> cost
  | Coq_instr_emit (_, _, cost) -> cost
  | Coq_instr_reveal (_, _, _, cost) -> cost
  | Coq_instr_oracle_halts (_, cost) -> cost
  | Coq_instr_halt cost -> cost

  (** val is_bit : int -> bool **)

  let is_bit n0 =
    (||) ((=) n0 0) ((=) n0 ((fun x -> x + 1) 0))

  (** val chsh_bits_ok : int -> int -> int -> int -> bool **)

  let chsh_bits_ok x y a b =
    (&&) ((&&) (is_bit x) (is_bit y)) ((&&) (is_bit a) (is_bit b))

  (** val apply_cost : vMState -> vm_instruction -> int **)

  let apply_cost s instr =
    add s.vm_mu (instruction_cost instr)

  (** val latch_err : vMState -> bool -> bool **)

  let latch_err s flag =
    (||) flag s.vm_err

  (** val advance_state :
      vMState -> vm_instruction -> partitionGraph -> cSRState -> bool ->
      vMState **)

  let advance_state s instr graph csrs err_flag =
    { vm_graph = graph; vm_csrs = csrs; vm_regs = s.vm_regs; vm_mem =
      s.vm_mem; vm_pc = ((fun x -> x + 1) s.vm_pc); vm_mu =
      (apply_cost s instr); vm_err = err_flag }

  (** val advance_state_rm :
      vMState -> vm_instruction -> partitionGraph -> cSRState -> int list ->
      int list -> bool -> vMState **)

  let advance_state_rm s instr graph csrs regs mem err_flag =
    { vm_graph = graph; vm_csrs = csrs; vm_regs = regs; vm_mem = mem; vm_pc =
      ((fun x -> x + 1) s.vm_pc); vm_mu = (apply_cost s instr); vm_err =
      err_flag }
 end

(** val vm_apply : vMState -> VMStep.vm_instruction -> vMState **)

let vm_apply s = function
| VMStep.Coq_instr_pnew (region, cost) ->
  let graph',_ = graph_pnew s.vm_graph region in
  VMStep.advance_state s (VMStep.Coq_instr_pnew (region, cost)) graph'
    s.vm_csrs s.vm_err
| VMStep.Coq_instr_psplit (module0, left_region, right_region, cost) ->
  (match graph_psplit s.vm_graph module0 left_region right_region with
   | Some p ->
     let p0,_ = p in
     let graph',_ = p0 in
     VMStep.advance_state s (VMStep.Coq_instr_psplit (module0, left_region,
       right_region, cost)) graph' s.vm_csrs s.vm_err
   | None ->
     VMStep.advance_state s (VMStep.Coq_instr_psplit (module0, left_region,
       right_region, cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (VMStep.latch_err s true))
| VMStep.Coq_instr_pmerge (m1, m2, cost) ->
  (match graph_pmerge s.vm_graph m1 m2 with
   | Some p ->
     let graph',_ = p in
     VMStep.advance_state s (VMStep.Coq_instr_pmerge (m1, m2, cost)) graph'
       s.vm_csrs s.vm_err
   | None ->
     VMStep.advance_state s (VMStep.Coq_instr_pmerge (m1, m2, cost))
       s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
       (VMStep.latch_err s true))
| VMStep.Coq_instr_lassert (module0, formula, cert, cost) ->
  (match cert with
   | VMStep.Coq_lassert_cert_unsat proof ->
     VMStep.advance_state s (VMStep.Coq_instr_lassert (module0, formula,
       (VMStep.Coq_lassert_cert_unsat proof), cost)) s.vm_graph
       (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (VMStep.latch_err s true)
   | VMStep.Coq_lassert_cert_sat model ->
     if VMStep.check_model formula model
     then let graph' = graph_add_axiom s.vm_graph module0 formula in
          let csrs' =
            csr_set_err (csr_set_status s.vm_csrs ((fun x -> x + 1) 0)) 0
          in
          VMStep.advance_state s (VMStep.Coq_instr_lassert (module0, formula,
            (VMStep.Coq_lassert_cert_sat model), cost)) graph'
            (csr_set_cert_addr csrs' (ascii_checksum formula)) s.vm_err
     else VMStep.advance_state s (VMStep.Coq_instr_lassert (module0, formula,
            (VMStep.Coq_lassert_cert_sat model), cost)) s.vm_graph
            (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
            (VMStep.latch_err s true))
| VMStep.Coq_instr_ljoin (cert1, cert2, cost) ->
  if eqb0 cert1 cert2
  then let csrs' = csr_set_err s.vm_csrs 0 in
       VMStep.advance_state s (VMStep.Coq_instr_ljoin (cert1, cert2, cost))
         s.vm_graph
         (csr_set_cert_addr csrs' (ascii_checksum (append cert1 cert2)))
         s.vm_err
  else let csrs' = csr_set_err s.vm_csrs ((fun x -> x + 1) 0) in
       VMStep.advance_state s (VMStep.Coq_instr_ljoin (cert1, cert2, cost))
         s.vm_graph
         (csr_set_cert_addr csrs' (ascii_checksum (append cert1 cert2)))
         (VMStep.latch_err s true)
| VMStep.Coq_instr_pdiscover (module0, evidence, cost) ->
  let graph' = graph_record_discovery s.vm_graph module0 evidence in
  VMStep.advance_state s (VMStep.Coq_instr_pdiscover (module0, evidence,
    cost)) graph' s.vm_csrs s.vm_err
| VMStep.Coq_instr_xfer (dst, src, cost) ->
  let regs' = write_reg s dst (read_reg s src) in
  VMStep.advance_state_rm s (VMStep.Coq_instr_xfer (dst, src, cost))
    s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err
| VMStep.Coq_instr_pyexec (payload, cost) ->
  VMStep.advance_state s (VMStep.Coq_instr_pyexec (payload, cost)) s.vm_graph
    (csr_set_err s.vm_csrs ((fun x -> x + 1) 0)) (VMStep.latch_err s true)
| VMStep.Coq_instr_chsh_trial (x, y, a, b, cost) ->
  if VMStep.chsh_bits_ok x y a b
  then VMStep.advance_state s (VMStep.Coq_instr_chsh_trial (x, y, a, b,
         cost)) s.vm_graph s.vm_csrs s.vm_err
  else VMStep.advance_state s (VMStep.Coq_instr_chsh_trial (x, y, a, b,
         cost)) s.vm_graph (csr_set_err s.vm_csrs ((fun x -> x + 1) 0))
         (VMStep.latch_err s true)
| VMStep.Coq_instr_xor_load (dst, addr, cost) ->
  let value = read_mem s addr in
  let regs' = write_reg s dst value in
  VMStep.advance_state_rm s (VMStep.Coq_instr_xor_load (dst, addr, cost))
    s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err
| VMStep.Coq_instr_xor_add (dst, src, cost) ->
  let vdst = read_reg s dst in
  let vsrc = read_reg s src in
  let regs' = write_reg s dst (word32_xor vdst vsrc) in
  VMStep.advance_state_rm s (VMStep.Coq_instr_xor_add (dst, src, cost))
    s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err
| VMStep.Coq_instr_xor_swap (a, b, cost) ->
  let regs' = swap_regs s.vm_regs a b in
  VMStep.advance_state_rm s (VMStep.Coq_instr_xor_swap (a, b, cost))
    s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err
| VMStep.Coq_instr_xor_rank (dst, src, cost) ->
  let vsrc = read_reg s src in
  let regs' = write_reg s dst (word32_popcount vsrc) in
  VMStep.advance_state_rm s (VMStep.Coq_instr_xor_rank (dst, src, cost))
    s.vm_graph s.vm_csrs regs' s.vm_mem s.vm_err
| VMStep.Coq_instr_emit (module0, payload, cost) ->
  let csrs' = csr_set_cert_addr s.vm_csrs (ascii_checksum payload) in
  VMStep.advance_state s (VMStep.Coq_instr_emit (module0, payload, cost))
    s.vm_graph csrs' s.vm_err
| VMStep.Coq_instr_reveal (module0, bits, cert, cost) ->
  let csrs' = csr_set_cert_addr s.vm_csrs (ascii_checksum cert) in
  VMStep.advance_state s (VMStep.Coq_instr_reveal (module0, bits, cert,
    cost)) s.vm_graph csrs' s.vm_err
| x -> VMStep.advance_state s x s.vm_graph s.vm_csrs s.vm_err
