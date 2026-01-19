
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m
 end

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

type muCost = nat

type trace =
| Empty
| Discover of muCost * trace
| Verify of muCost * trace
| Compose of trace * trace

(** val mu_total : trace -> muCost **)

let rec mu_total = function
| Empty -> O
| Discover (c, t') -> add c (mu_total t')
| Verify (c, t') -> add c (mu_total t')
| Compose (t1, t2) -> add (mu_total t1) (mu_total t2)

(** val inversions_nat : nat list -> nat **)

let rec inversions_nat = function
| Nil -> O
| Cons (x, xs) ->
  add (length (filter (fun y -> Nat.ltb y x) xs)) (inversions_nat xs)

(** val sorting_mu_cost : nat list -> muCost **)

let sorting_mu_cost =
  inversions_nat
