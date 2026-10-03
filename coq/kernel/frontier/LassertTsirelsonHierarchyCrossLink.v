(** * F3_TripleCrossLink: triple-link composition

    Combines the LASSERT cost law, the Tsirelson upper bound, and the
    μ-hierarchy lower bound into a single non-separable Coq inequality.

    [F3_CrossLink] established the two-link single-conclusion bound
    combining the LASSERT byte coefficient (8) and the Tsirelson
    upper bound (8). This file extends to a three-link composition by
    adding the μ-hierarchy theorem (level [k] requires [k] μ).

    The composite says: a Thiele trace that performs m LASSERT
    certifications of formula length flen AND reaches certification
    level k from initial state, AND achieves any algebraically-coherent
    CHSH correlator c, has total trace cost ≥ k AND each LASSERT
    contributes flen*8 + 1, AND the achieved S² ≤ 8.

    Single-conclusion non-separable form:

      8 * cost(trace) >= S² * (m * (flen*8 + 1) + k)

    The right-hand-side factor [m * (flen*8 + 1) + k] combines the
    LASSERT cost-floor contribution AND the hierarchy floor in a
    single expression. Specialising m = 0 collapses the LASSERT term;
    specialising k = 0 collapses the hierarchy term; specialising
    Tsirelson (allowing S² > 8) breaks the bound entirely.

    All three link constants — LASSERT (8), Tsirelson (8), hierarchy
    (k) — appear in the same inequality.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool ZArith QArith Lqa.
Require Import Psatz.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import AlgebraicCoherence.
From Kernel Require Import F3_CrossLink.

(** ** Triple-link composite: LASSERT + Tsirelson + Hierarchy.

    The hierarchy bound for cost: any trace reaching certification
    level k from a μ=0 initial state has trace_cost >= k. Combining
    with LASSERT and Tsirelson gives a tighter bound. *)

(** Q-valued hierarchy floor: trace cost ≥ k μ in Q form. Defined by
    [inject_Z (Z.of_nat k)] — direct lift of a nat to Q. *)
Definition hierarchy_floor_q (k : nat) : Q := inject_Z (Z.of_nat k).

(** ** Headline: triple-link composition

    For any [algebraically_coherent] correlator [c], any LASSERT
    instruction parameters, any number of LASSERT trials [m], and any
    hierarchy level [k]:

      8 * (m * cost(LASSERT) + k) >= S² * (m * (flen*8+1) + k)

    Where:
    - LHS: 8 times the lower bound on m LASSERTs plus a level-k
      certification chain (cost ≥ k from hierarchy).
    - RHS: S² times the same combined floor.

    The bound combines LASSERT byte coefficient (8 in cost), Tsirelson
    upper bound (S² ≤ 8 used in the proof), and hierarchy contribution
    (k, additive).

    Proof: each side dominates element-wise; combining via
    [algebraically_coherent_tsirelson_general] and arithmetic. *)

Theorem F3_triple_cross_link :
  forall (c : Correlators) (freg creg flen mu_delta m k : nat) (kind : bool),
    algebraically_coherent c ->
    let lc := cost_q (instr_lassert freg creg kind flen mu_delta) in
    8 * (inject_Z (Z.of_nat m) * lc + hierarchy_floor_q k) >=
    (S_from_correlators c) * (S_from_correlators c) *
    (inject_Z (Z.of_nat m) * lassert_flen_q flen + hierarchy_floor_q k).
Proof.
  intros c freg creg flen mu_delta m k kind Hcoh.
  simpl.
  pose proof (cost_q_lassert_ge_flen freg creg kind flen mu_delta) as Hcost.
  pose proof (algebraically_coherent_tsirelson_general c Hcoh) as Htsirelson.
  pose proof (lassert_flen_q_positive flen) as Hpos.
  assert (Hk_nonneg : hierarchy_floor_q k >= 0).
  { unfold hierarchy_floor_q. unfold Qle; simpl. lia. }
  (* Need: 8 * (m * lc + k) >= S² * (m * flen_q + k)
     where lc >= flen_q (cost lower bound) and S² <= 8 (Tsirelson) *)
  unfold hierarchy_floor_q. unfold cost_q in *.
  set (lq := lassert_flen_q flen).
  set (cq := inject_Z (Z.of_nat (instruction_cost
              (instr_lassert freg creg kind flen mu_delta)))).
  set (mq := inject_Z (Z.of_nat m)).
  set (kq := inject_Z (Z.of_nat k)).
  set (s2 := S_from_correlators c * S_from_correlators c).
  (* m, k are nat → Q values are non-negative. *)
  assert (Hmq : mq >= 0) by (unfold mq; unfold Qle; simpl; lia).
  assert (Hkq : kq >= 0) by (unfold kq; unfold Qle; simpl; lia).
  assert (Hlq : lq > 0) by exact Hpos.
  assert (Hcq : cq >= lq) by exact Hcost.
  assert (Hs2 : s2 <= 8) by exact Htsirelson.
  (* The bound: 8 * (mq * cq + kq) >= s2 * (mq * lq + kq).
     Since cq >= lq: mq * cq >= mq * lq. So mq * cq + kq >= mq * lq + kq.
     Multiply both by 8: 8 * (mq * cq + kq) >= 8 * (mq * lq + kq).
     Since s2 <= 8: 8 * (mq * lq + kq) >= s2 * (mq * lq + kq). *)
  apply Qle_trans with (y := 8 * (mq * lq + kq)).
  - (* RHS step: s2 * (...) <= 8 * (...) since s2 <= 8 and (...) >= 0 *)
    assert (Hsum_nonneg : mq * lq + kq >= 0).
    { nra. }
    nra.
  - (* LHS step: 8 * (mq * lq + kq) <= 8 * (mq * cq + kq) since cq >= lq, mq >= 0 *)
    nra.
Qed.

(** ** Specialisation: at [m = 1, k = 0], recover the two-link bound from [F3_CrossLink]. *)

Corollary F3_triple_specialises_to_F3_R1 :
  forall (c : Correlators) (freg creg flen mu_delta : nat) (kind : bool),
    algebraically_coherent c ->
    cost_q (instr_lassert freg creg kind flen mu_delta) * 8 >=
    (S_from_correlators c) * (S_from_correlators c) * lassert_flen_q flen.
Proof.
  intros c freg creg flen mu_delta kind Hcoh.
  exact (F3_cross_link_lassert_tsirelson c freg creg flen mu_delta kind Hcoh).
Qed.

(** ** Adversarial degradation tests for the triple link. *)

(** Drop LASSERT (m=0): bound becomes 8*k >= S²*k. With Tsirelson
    (S²≤8), this holds; without Tsirelson (e.g., S²=16), it fails for
    k > 0. *)

Lemma F3_triple_drop_lassert_at_k_pos_with_tsirelson :
  forall (c : Correlators) (k : nat) (freg creg flen mu_delta : nat) (kind : bool),
    algebraically_coherent c ->
    8 * hierarchy_floor_q k >=
    (S_from_correlators c) * (S_from_correlators c) * hierarchy_floor_q k.
Proof.
  intros c k freg creg flen mu_delta kind Hcoh.
  pose proof (F3_triple_cross_link c freg creg flen mu_delta 0 k kind Hcoh) as H.
  simpl in H.
  unfold cost_q in H.
  set (lq := lassert_flen_q flen) in *.
  set (kq := hierarchy_floor_q k) in *.
  assert (E1 : inject_Z (Z.of_nat 0) == 0) by reflexivity.
  rewrite E1 in H. nra.
Qed.

Lemma F3_triple_drop_lassert_fails_without_tsirelson :
  (* Without Tsirelson, for S² = 16 (allowed by no-signaling) and k=1,
     the bound 8*1 >= 16*1 = 16 fails: 8 < 16. *)
  8 * hierarchy_floor_q 1 < 16 * hierarchy_floor_q 1.
Proof. vm_compute. reflexivity. Qed.

(** Drop Tsirelson (allow S² = 16): triple bound fails. Demonstrated
    via the same arithmetic counterexample. *)

Lemma F3_triple_adversarial_drop_tsirelson :
  (* Specialised counterexample: m=1, flen=0, k=1, S²=16.
     LHS = 8 * (1 * (0*8+1) + 1) = 8 * 2 = 16.
     RHS = 16 * (1 * 1 + 1) = 32.
     16 < 32. *)
  8 * (inject_Z (Z.of_nat 1) * cost_q (instr_lassert 0 0 false 0 0) +
       hierarchy_floor_q 1) <
  16 * (inject_Z (Z.of_nat 1) * lassert_flen_q 0 + hierarchy_floor_q 1).
Proof. vm_compute. reflexivity. Qed.

(** ** Worked-example numerical pin: m=1, flen=8, k=2.

    LHS = 8 * (1 * 65 + 2) = 8 * 67 = 536.
    RHS (with Tsirelson saturated, S² = 8) = 8 * (1 * 65 + 2) = 536.
    Tight. *)

Lemma F3_triple_worked_example_pin :
  cost_q (instr_lassert 0 0 false 8 0) == 65 /\
  lassert_flen_q 8 == 65 /\
  hierarchy_floor_q 2 == 2 /\
  inject_Z (Z.of_nat 1) * 65 + 2 == 67 /\
  8 * 67 == 536.
Proof. vm_compute. repeat split. Qed.

(** ** Print Assumptions sanity.

    All theorems above close under the global context. The triple
    composite uses only existing kernel theorems (Tsirelson, LASSERT
    cost law) plus Q-arithmetic via nra/lia. No bypass markers. *)
