
type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : int -> int -> int

val sub : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_succ_nat : int -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val gtb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val div2 : z -> z

  val shiftl : z -> z -> z
 end

type q16 = z

val q16_ONE : q16

val q16_MAX : q16

val q16_MIN : q16

val saturate : z -> q16

val q16_add : q16 -> q16 -> q16

val q16_sub : q16 -> q16 -> q16

val q16_mul : q16 -> q16 -> q16

val q16_div : q16 -> q16 -> q16

val log2_lut : q16 list

val lut_lookup : int -> q16 list -> q16

val count_leading_zeros_helper : z -> int -> int -> int

val count_leading_zeros : z -> int

val extract_lut_index : z -> int

val q16_log2 : q16 -> q16

val information_gain : z -> z -> q16

type muAccumulator =
  q16
  (* singleton inductive, whose constructor was Build_MuAccumulator *)

val mu_value : muAccumulator -> q16

val mu_accumulate : muAccumulator -> q16 -> muAccumulator
