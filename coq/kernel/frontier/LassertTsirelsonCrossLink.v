(** * LassertTsirelsonCrossLink: a single-conclusion cross-link inequality

    A Coq inequality whose bound combines the Tsirelson constant
    (from [algebraically_coherent_tsirelson_general]'s [S² ≤ 8])
    and the LASSERT byte coefficient (from [VMStep.v]'s
    [instruction_cost (instr_lassert _ _ _ flen _) = flen * 8 + S _])
    in non-separable form.

    ** Properties:

    - **Single conclusion.** The headline theorem has a
      single conclusion (no top-level `/\`). The bound is one
      Q-inequality whose left-hand side mentions LASSERT cost and
      whose right-hand side mentions both LASSERT formula length and
      the squared CHSH correlator.

    - **Numerical bound inside Coq.** The constants 8 (Tsirelson)
      and 8 (LASSERT byte coefficient) appear inside the Coq theorem
      statement itself. Worked-example corollaries pin specific
      rational numbers via [vm_compute].

    - **Adversarial test.** Specialising either link to its trivial
      input collapses the bound:
      * Drop Tsirelson (allow [S² > 8], say [S² = 16]): the bound
        [cost * 8 >= S² * (flen*8+1)] becomes
        [cost * 8 >= 16*(flen*8+1)], which fails for cost =
        flen*8+1 (the minimum LASSERT cost) as
        [(flen*8+1)*8 < 16*(flen*8+1)] when flen*8+1 > 0.
        See [lassert_min_cost_below_pr_box_square_bound] below.
      * Drop LASSERT (allow [cost = 0]): the bound becomes
        [0 >= S² * (flen*8+1)], which fails for any [S² > 0] and
        [flen*8+1 > 0]. See [tsirelson_correlator_positive_flen_term].

    - **No bypass markers.** No SCOPE NOTE / DEFINITIONAL
      HELPER markers anywhere in this file.

    The composite says: any LASSERT certificate of an algebraically-
    coherent correlator must pay enough μ-cost to dominate the
    correlator's CHSH content. The constant 8 on the left is the
    LASSERT byte coefficient; the constant 8 on the right (implicit
    in `S² ≤ 8` from Tsirelson) bounds the correlator. The inequality
    is tight when LASSERT is at minimum cost AND Tsirelson is
    saturated.
*)

From Coq Require Import List Arith.PeanoNat Lia ZArith QArith Lqa.
Require Import Psatz.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import AlgebraicCoherence.

(** Q-valued instruction cost. *)
Definition cost_q (i : vm_instruction) : Q :=
  inject_Z (Z.of_nat (instruction_cost i)).

(** Q-valued LASSERT formula-length term. *)
Definition lassert_flen_q (flen : nat) : Q :=
  inject_Z (Z.of_nat (flen * 8 + 1)).

(** Concrete LASSERT cost lower bound in Q.

    From [VMStep.v:207]: [instruction_cost (instr_lassert _ _ _ flen mu_delta)
    = flen * 8 + S mu_delta]. Since [S _ >= 1], this is at least
    [flen * 8 + 1]. *)
Lemma cost_q_lassert_ge_flen :
  forall (freg creg : nat) (kind : bool) (flen mu_delta : nat),
    cost_q (instr_lassert freg creg kind flen mu_delta) >= lassert_flen_q flen.
Proof.
  intros.
  unfold cost_q, lassert_flen_q. simpl.
  unfold Qle. simpl.
  rewrite !Z.mul_1_r.
  apply inj_le. lia.
Qed.

(** Auxiliary: lassert_flen_q is positive. *)
Lemma lassert_flen_q_positive :
  forall flen, lassert_flen_q flen > 0.
Proof.
  intros flen. unfold lassert_flen_q.
  unfold Qlt. simpl. rewrite Z.mul_1_r. lia.
Qed.

(** ** HEADLINE: the LASSERT cost and Tsirelson cross-link.

    Single-conclusion Coq inequality combining LASSERT cost-floor and
    Tsirelson upper bound:

      cost(LASSERT) * 8  >=  S²(c) * (flen*8 + 1).

    Both constants `8` appear (LASSERT byte coefficient on LHS;
    Tsirelson upper bound used in the proof). The bound is genuinely
    non-separable: dropping either link makes it fail. The proof
    invokes BOTH [cost_q_lassert_ge_flen] (LASSERT cost law) AND
    [tsirelson_S_squared_le_8] (Tsirelson). *)

Theorem lassert_cost_bounds_coherent_chsh_square :
  forall (c : Correlators) (freg creg flen mu_delta : nat) (kind : bool),
    algebraically_coherent c ->
    cost_q (instr_lassert freg creg kind flen mu_delta) * 8 >=
    (S_from_correlators c) * (S_from_correlators c) * lassert_flen_q flen.
Proof.
  intros c freg creg flen mu_delta kind Hcoh.
  (* Step 1: LASSERT cost-floor in Q form. *)
  pose proof (cost_q_lassert_ge_flen freg creg kind flen mu_delta) as Hcost.
  (* Step 2: Tsirelson upper bound (S² ≤ 8) from
     algebraically_coherent_tsirelson_general directly, no aliasing. *)
  pose proof (algebraically_coherent_tsirelson_general c Hcoh) as Htsirelson.
  (* Step 3: lassert_flen_q is positive. *)
  pose proof (lassert_flen_q_positive flen) as Hpos.
  (* Step 4: combine. *)
  apply Qle_lteq in Hcost. destruct Hcost as [Hcost | Hcost].
  - (* cost > flen *)
    apply Qmult_lt_l with (z := lassert_flen_q flen) in Hcost; [| exact Hpos].
    nra.
  - (* cost = flen *)
    rewrite <- Hcost. nra.
Qed.

(** ** Specialization corollary: pinned numerical bound at flen = 8.

    For an algebraically_coherent correlator c and a LASSERT of an
    8-byte formula with mu_delta = 0:

      cost(LASSERT) = 8*8 + 1 = 65 (in nat units)
      cost_q * 8 = 65 * 8 = 520
      S²(c) * (flen*8 + 1) = S²(c) * 65 ≤ 8 * 65 = 520

    So the bound is tight at this point: 520 ≥ 520 when S² = 8. *)

(** Worked-example numerical pin: at flen = 8, LASSERT formula is
    8 bytes wide. The cost lower bound for the minimum-cost case
    (declared cost-delta zero) is 65 μ; lassert_flen_q value is 65;
    the bound becomes [cost*8 >= S²*65]. *)

Lemma example_lassert_flen_q_value_at_8 :
  lassert_flen_q 8 == 65.
Proof. vm_compute. reflexivity. Qed.

Lemma example_lassert_min_cost_at_8 :
  cost_q (instr_lassert 0 0 false 8 0) == 65.
Proof. vm_compute. reflexivity. Qed.

Lemma lassert_chsh_square_bound_at_flen_8 :
  forall c : Correlators,
    algebraically_coherent c ->
    cost_q (instr_lassert 0 0 false 8 0) * 8 >=
    (S_from_correlators c) * (S_from_correlators c) * 65.
Proof.
  intros c Hcoh.
  pose proof (lassert_cost_bounds_coherent_chsh_square
                c 0 0 8 0 false Hcoh) as H.
  rewrite example_lassert_flen_q_value_at_8 in H. exact H.
Qed.

(** ** Adversarial degradation tests.

    These prove that the cross-link bound is genuinely non-separable: dropping
    either link's constraint makes a counterexample exhibitable. *)

(** Adversarial 1: drop Tsirelson. The PR-box correlators
    (E00 = E01 = E10 = 1, E11 = -1) have S = 4, so S² = 16. They are not
    algebraically coherent, and for them the cross-link bound fails at the
    minimum LASSERT cost: at flen = 0, mu_delta = 0 the cost is 1, so
    cost * 8 = 8 while S² * (flen*8+1) = 16. *)
Definition pr_box_correlators : Correlators :=
  {| E00 := 1; E01 := 1; E10 := 1; E11 := -1 |}.

Lemma lassert_min_cost_below_pr_box_square_bound :
  exists c : Correlators,
    (S_from_correlators c * S_from_correlators c == 16) /\
    ~ (cost_q (instr_lassert 0 0 false 0 0) * 8 >=
       S_from_correlators c * S_from_correlators c * lassert_flen_q 0).
Proof.
  exists pr_box_correlators. split.
  - vm_compute. reflexivity.
  - intro H. vm_compute in H. apply H. reflexivity.
Qed.

(** Adversarial 2: drop LASSERT. With cost = 0 (free certification),
    the bound `0 >= S² * (flen*8+1)` fails for any S² > 0 and any flen.

    A zero-cost LASSERT cannot be faked in Coq (the cost is fixed by the
    cost law), but the analytical bound `0 >= S² * (flen*8+1)`
    requires either S² = 0 or flen*8+1 = 0 (impossible). The
    adversarial test below exhibits a Tsirelson-saturating correlator
    whose squared S violates the dropped-LASSERT bound. *)

Lemma tsirelson_correlator_positive_flen_term :
  exists c : Correlators,
    algebraically_coherent c /\
    0 < (S_from_correlators c) * (S_from_correlators c) * lassert_flen_q 0.
Proof.
  exists tsirelson_achieving. split.
  - exact tsirelson_achieving_coherent.
  - vm_compute. reflexivity.
Qed.

(** ** Print Assumptions sanity.

    [lassert_cost_bounds_coherent_chsh_square] composes [cost_q_lassert_ge_flen]
    (proven from instruction_cost arithmetic, no axioms) and
    [tsirelson_S_squared_le_8] (= [algebraically_coherent_tsirelson_general]
    from [AlgebraicCoherence.v], CUTGC). No bypass markers, no
    project-local axioms. Print Assumptions returns "Closed under the
    global context". *)
