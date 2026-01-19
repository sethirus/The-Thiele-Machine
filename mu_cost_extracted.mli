
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val add : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type muCost = nat

type trace =
| Empty
| Discover of muCost * trace
| Verify of muCost * trace
| Compose of trace * trace

val mu_total : trace -> muCost

val inversions_nat : nat list -> nat

val sorting_mu_cost : nat list -> muCost
