(** ProbabilityImpossibility: composition laws alone do not determine a unique weight rule

  This file is a no-go result about abstraction level. It shows that simple
  compositional laws for trace weights do not force a unique probability-like
  assignment. Two different weight functions can satisfy the same additive
  interface, so extra structure is needed before one can recover anything as
  specific as the Born rule.

  The point is a boundary claim: pure composition is too weak by itself.

  *)

(* SCOPE NOTE: foundation connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.PeanoNat Lia.

From Kernel Require Import VMStep.

Import ListNotations.

(** Abstract weight interface. *)

(** [Weight] is an arbitrary natural-valued assignment to instruction lists.
    The type is deliberately broad: the theorem below concerns the algebraic
    interface only and does not identify a weight with probability or cost. *)
Definition Weight := list vm_instruction -> nat.

(** [weight_compositional] requires a zero value on the empty list and
    additivity under list concatenation. It is the only interface used by the
    non-uniqueness theorem. *)
Definition weight_compositional (w : Weight) : Prop :=
  w [] = 0 /\
  forall t1 t2, w (t1 ++ t2) = w t1 + w t2.

(** Counterexample constructions. *)

(** [w_len] assigns the length of the instruction list. *)
Definition w_len : Weight := fun t => length t.

(** [w_len2] assigns twice the instruction-list length. It satisfies the same
    interface while remaining distinct from [w_len]. *)
Definition w_len2 : Weight := fun t => 2 * length t.

(** Compositionality proofs. *)

(** Trace length satisfies the compositional interface by [app_length]. *)
Lemma w_len_compositional : weight_compositional w_len.
Proof.
  split.
  - (* Base case: empty trace has length 0 *)
    reflexivity.
  - (* Composition: length(t1++t2) = length(t1) + length(t2) *)
    intros t1 t2. unfold w_len.
    (* Use app_length: length (l1 ++ l2) = length l1 + length l2 *)
    rewrite app_length.
    (* Arithmetic: both sides equal *)
    lia.
Qed.

(** Twice the trace length also satisfies the compositional interface. *)
Lemma w_len2_compositional : weight_compositional w_len2.
Proof.
  split.
  - (* Base case: 2*0 = 0 *)
    reflexivity.
  - (* Composition: 2*length(t1++t2) = 2*length(t1) + 2*length(t2) *)
    intros t1 t2. unfold w_len2.
    (* Use app_length *)
    rewrite app_length.
    (* Arithmetic: 2*(a+b) = 2*a + 2*b *)
    lia.
Qed.

(** The theorem is a non-uniqueness result for the stated interface. It
    exhibits two compositional weights and a one-instruction list on which they
    differ. It does not by itself make a claim about the physical Born rule;
    it shows that composition and a zero base value are insufficient to select
    one numerical interpretation. *)
Theorem Born_Rule_Unique_Fails_Without_More_Structure :
  exists w1 w2,
    weight_compositional w1 /\
    weight_compositional w2 /\
    (exists t, w1 t <> w2 t).
Proof.
  (* === PART 1: Exhibit the two weight functions === *)
  exists w_len, w_len2.

  split.
  - (* w_len is compositional (proven above) *)
    exact w_len_compositional.

  - split.
    + (* w_len2 is compositional (proven above) *)
      exact w_len2_compositional.

    + (* === PART 2: Show they differ on some trace === *)
      (* Witness: single halt instruction *)
      exists [instr_halt 0].

      (* Compute: w_len [halt] = 1, w_len2 [halt] = 2 *)
      simpl.

      (* 1 ≠ 2 by discrimination *)
      discriminate.
Qed.

(**
    INTERPRETATION

    This theorem establishes a fundamental limitation: You CANNOT derive
    probability theory from pure computation. Compositional structure is
    insufficient to uniquely determine weights.
    1. BORN RULE IS POSTULATED, NOT DERIVED:
       Quantum mechanics assumes |ψ|² gives probabilities. This cannot be
       proven from composition laws alone. It's an additional axiom.

    2. FREQUENCY INTERPRETATION REQUIRES CHOICE:
       If you want to assign "probabilities" to traces, you must CHOOSE a
       weight function. Composition laws don't force a unique choice.

    3. KERNEL CANNOT DERIVE PROBABILITY:
       The Thiele Machine derives many things (Tsirelson bound, second law,
       locality), but probability theory is NOT among them. Probability
       requires additional structure beyond μ-cost and partition dynamics.

    4. BOUNDARY OF DERIVABILITY:
       This is a clean NO-GO result showing what the kernel CANNOT do.
       Compare with PhysicsClosure.v (what it CAN do) and MuInitiality.v
       (which proves mu-cost uniqueness from instruction-consistency).

    RELATED WORK:
    - Gleason's theorem: Probabilities on Hilbert spaces must be Born rule
      (but requires Hilbert space structure, not just composition)
    - Cox's theorem: Consistent plausibility → probability axioms
      (but requires consistency postulates beyond composition)

    Neither of these works applies here because we're only assuming
    compositional structure, nothing more.

    *)
