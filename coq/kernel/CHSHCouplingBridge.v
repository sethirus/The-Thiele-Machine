(** CHSHCouplingBridge: connecting categorical coupling language to CHSH bounds.

    This file establishes the precise connection between:
    - Morphism coupling separability (CategoryLaws.v)
    - CHSH statistical bounds (CHSHStatisticalBridge.v)

    The key structural facts proved here:

    1. locally_consistent_gives_separable: WCLocallyConsistent → separable coupling.
       A locally deterministic CHSH strategy (a0,a1,b0,b1) produces exactly one
       outcome type per setting, giving a functional (separable) coupling.

    2. separable_implies_no_locally_consistent_violation: If a WitnessCount is
       WCLocallyConsistent for some strategy, then |S| ≤ 2. Follows from
       local_bound_for_wc.

    3. chsh_violation_rules_out_local_coupling: S > 2 → no locally consistent
       strategy explains the data → no locally factorizable coupling.
       (This is chsh_stat_violation_not_local restated in coupling language.)

    IMPORTANT SUBTLETY: "Separable coupling → S ≤ 2" is FALSE.
    A separable (functional) coupling can produce S > 2. Example: if each setting
    maps to exactly one outcome type but the pattern is globally inconsistent
    with any local strategy (e.g., all diff for (0,0),(0,1),(1,0) and all same
    for (1,1) gives S = -4). The CHSH violation captures non-local JOINT
    consistency constraints, not just per-setting determinism.

    The correct statement is: locally FACTORIZABLE coupling (product of Alice's
    and Bob's independent couplings) → S ≤ 2. A locally factorizable coupling
    is exactly WCLocallyConsistent for some (a0,a1,b0,b1). S > 2 rules out all
    such locally factorizable explanations.

    Zero Admitted. Zero Section Variables. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.
From Coq Require Import QArith QArith.Qabs.
From Kernel Require Import VMState.
From Kernel Require Import CategoryLaws.
From Kernel Require Import VMStep.
From Kernel Require Import CHSHStatisticalBridge.

Local Open Scope nat_scope.

(** The settings-outcome coupling: maps each of the 4 CHSH settings
    (encoded: setting (a,b) → 2a+b ∈ {0,1,2,3}) to outcome types
    (0=same, 1=different), recording which outcome types were observed. *)

Definition chsh_setting_outcome_coupling (wc : WitnessCounts) : Coupling :=
  (if Nat.eqb (wc_same_00 wc) 0 then [] else [(0%nat, 0%nat)]) ++
  (if Nat.eqb (wc_diff_00 wc) 0 then [] else [(0%nat, 1%nat)]) ++
  (if Nat.eqb (wc_same_01 wc) 0 then [] else [(1%nat, 0%nat)]) ++
  (if Nat.eqb (wc_diff_01 wc) 0 then [] else [(1%nat, 1%nat)]) ++
  (if Nat.eqb (wc_same_10 wc) 0 then [] else [(2%nat, 0%nat)]) ++
  (if Nat.eqb (wc_diff_10 wc) 0 then [] else [(2%nat, 1%nat)]) ++
  (if Nat.eqb (wc_same_11 wc) 0 then [] else [(3%nat, 0%nat)]) ++
  (if Nat.eqb (wc_diff_11 wc) 0 then [] else [(3%nat, 1%nat)]).

(** ** Theorem 1: Locally consistent strategies produce separable couplings.

    WCLocallyConsistent a0 a1 b0 b1 wc forces each setting to have at most
    one outcome type: either wc_same_ab = 0 or wc_diff_ab = 0 (per the wclc_XX
    fields). This makes each source in the coupling map to exactly one target
    — a functional (separable) coupling. *)

(** Tactic: after unfolding and zero-rewriting one bucket, discharge the
    remaining In-false goals by splitting ++ chains, closing In-[]-False,
    and destructing each if-then-else conditional singleton. *)
Ltac solve_not_in_chsh_coupling :=
  repeat match goal with
  | Hin : In _ (_ ++ _) |- _ =>
      apply in_app_or in Hin; destruct Hin as [Hin | Hin]
  | Hin : In _ [] |- _ => exact Hin
  | Hin : In _ (if ?b then [] else [_]) |- _ =>
      destruct b; simpl in Hin;
      [ exact Hin
      | destruct Hin as [Heq | []]; injection Heq; intros; lia ]
  end.

Lemma not_in_coupling_same_00 : forall wc,
    (wc_same_00 wc = 0)%nat -> ~ In (0, 0) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_diff_00 : forall wc,
    (wc_diff_00 wc = 0)%nat -> ~ In (0, 1) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_same_01 : forall wc,
    (wc_same_01 wc = 0)%nat -> ~ In (1, 0) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_diff_01 : forall wc,
    (wc_diff_01 wc = 0)%nat -> ~ In (1, 1) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_same_10 : forall wc,
    (wc_same_10 wc = 0)%nat -> ~ In (2, 0) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_diff_10 : forall wc,
    (wc_diff_10 wc = 0)%nat -> ~ In (2, 1) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_same_11 : forall wc,
    (wc_same_11 wc = 0)%nat -> ~ In (3, 0) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.

Lemma not_in_coupling_diff_11 : forall wc,
    (wc_diff_11 wc = 0)%nat -> ~ In (3, 1) (chsh_setting_outcome_coupling wc).
Proof.
  intros wc H Hin. unfold chsh_setting_outcome_coupling in Hin.
  rewrite (proj2 (Nat.eqb_eq _ _) H) in Hin. simpl in Hin.
  solve_not_in_chsh_coupling.
Qed.


(** Auxiliary bounds used in the main proof. *)
Lemma chsh_coupling_snd_bound : forall wc s c,
    In (s, c) (chsh_setting_outcome_coupling wc) -> c = 0 \/ c = 1.
Proof.
  intros wc s c Hin. unfold chsh_setting_outcome_coupling in Hin.
  repeat match goal with
  | Hin : In _ (_ ++ _) |- _ => apply in_app_or in Hin; destruct Hin as [Hin | Hin]
  | Hin : In _ [] |- _ => simpl in Hin; contradiction
  | Hin : In _ (if ?b then [] else [_]) |- _ =>
      destruct b; simpl in Hin;
      [ simpl in Hin; contradiction
      | destruct Hin as [Heq | []]; injection Heq; intros; subst; auto ]
  end.
Qed.

Lemma chsh_coupling_fst_bound : forall wc s c,
    In (s, c) (chsh_setting_outcome_coupling wc) -> s = 0 \/ s = 1 \/ s = 2 \/ s = 3.
Proof.
  intros wc s c Hin. unfold chsh_setting_outcome_coupling in Hin.
  repeat match goal with
  | Hin : In _ (_ ++ _) |- _ => apply in_app_or in Hin; destruct Hin as [Hin | Hin]
  | Hin : In _ [] |- _ => simpl in Hin; contradiction
  | Hin : In _ (if ?b then [] else [_]) |- _ =>
      destruct b; simpl in Hin;
      [ simpl in Hin; contradiction
      | destruct Hin as [Heq | []]; injection Heq; intros; subst; auto ]
  end.
Qed.

(** Main separability theorem. *)

Theorem locally_consistent_gives_separable_coupling :
  forall a0 a1 b0 b1 wc,
    WCLocallyConsistent a0 a1 b0 b1 wc ->
    separable_coupling (chsh_setting_outcome_coupling wc).
Proof.
  intros a0 a1 b0 b1 wc Hlc.
  destruct Hlc as [H00 H01 H10 H11 _].
  assert (K00 : (wc_same_00 wc = 0)%nat \/ (wc_diff_00 wc = 0)%nat).
  { destruct (Nat.eqb a0 b0); [right|left]; exact H00. }
  assert (K01 : (wc_same_01 wc = 0)%nat \/ (wc_diff_01 wc = 0)%nat).
  { destruct (Nat.eqb a0 b1); [right|left]; exact H01. }
  assert (K10 : (wc_same_10 wc = 0)%nat \/ (wc_diff_10 wc = 0)%nat).
  { destruct (Nat.eqb a1 b0); [right|left]; exact H10. }
  assert (K11 : (wc_same_11 wc = 0)%nat \/ (wc_diff_11 wc = 0)%nat).
  { destruct (Nat.eqb a1 b1); [right|left]; exact H11. }
  unfold separable_coupling.
  intros s c1 c2 H1 H2.
  destruct (Nat.eq_dec c1 c2) as [|Hne]; [exact e|].
  exfalso.
  assert (Hc1 : c1 = 0 \/ c1 = 1) by exact (chsh_coupling_snd_bound wc s c1 H1).
  assert (Hc2 : c2 = 0 \/ c2 = 1) by exact (chsh_coupling_snd_bound wc s c2 H2).
  assert (Hs : s = 0 \/ s = 1 \/ s = 2 \/ s = 3) by exact (chsh_coupling_fst_bound wc s c1 H1).
  (* c1 ≠ c2 with both in {0,1}: only (c1=0,c2=1) or (c1=1,c2=0). *)
  destruct Hc1 as [Hc1|Hc1], Hc2 as [Hc2|Hc2]; subst;
  try exact (Hne eq_refl);
  destruct Hs as [Hs|[Hs|[Hs|Hs]]]; subst.
  (* c1=0, c2=1: H1 is In(s,0), H2 is In(s,1) *)
  - destruct K00 as [Ks|Kd]; [exact (not_in_coupling_same_00 wc Ks H1) | exact (not_in_coupling_diff_00 wc Kd H2)].
  - destruct K01 as [Ks|Kd]; [exact (not_in_coupling_same_01 wc Ks H1) | exact (not_in_coupling_diff_01 wc Kd H2)].
  - destruct K10 as [Ks|Kd]; [exact (not_in_coupling_same_10 wc Ks H1) | exact (not_in_coupling_diff_10 wc Kd H2)].
  - destruct K11 as [Ks|Kd]; [exact (not_in_coupling_same_11 wc Ks H1) | exact (not_in_coupling_diff_11 wc Kd H2)].
  (* c1=1, c2=0: H1 is In(s,1), H2 is In(s,0) — swap K-lemma args *)
  - destruct K00 as [Ks|Kd]; [exact (not_in_coupling_same_00 wc Ks H2) | exact (not_in_coupling_diff_00 wc Kd H1)].
  - destruct K01 as [Ks|Kd]; [exact (not_in_coupling_same_01 wc Ks H2) | exact (not_in_coupling_diff_01 wc Kd H1)].
  - destruct K10 as [Ks|Kd]; [exact (not_in_coupling_same_10 wc Ks H2) | exact (not_in_coupling_diff_10 wc Kd H1)].
  - destruct K11 as [Ks|Kd]; [exact (not_in_coupling_same_11 wc Ks H2) | exact (not_in_coupling_diff_11 wc Kd H1)].
Qed.

(** ** Theorem 2: Locally consistent strategies produce classical statistics.

    Since WCLocallyConsistent → separable coupling AND WCLocallyConsistent → |S| ≤ 2,
    any locally factorizable explanation of the data is classically bounded. *)

Theorem locally_consistent_classical_bound :
  forall a0 a1 b0 b1 wc,
    is_bit a0 = true -> is_bit a1 = true ->
    is_bit b0 = true -> is_bit b1 = true ->
    WCLocallyConsistent a0 a1 b0 b1 wc ->
    Qle (Qabs (chsh_stat_from_wc wc)) 2.
Proof.
  intros a0 a1 b0 b1 wc Ha0 Ha1 Hb0 Hb1 Hlc.
  exact (local_bound_for_wc a0 a1 b0 b1 wc Ha0 Ha1 Hb0 Hb1 Hlc).
Qed.

(** ** Theorem 3: S > 2 rules out all locally factorizable explanations.

    If S > 2, no locally deterministic strategy (a0,a1,b0,b1) is consistent
    with the data. In coupling terms: no locally factorizable coupling
    (product of Alice's and Bob's individual strategies) explains the statistics.

    This is chsh_stat_violation_not_local restated in coupling language. *)

Theorem chsh_violation_rules_out_locally_factorizable_coupling :
  forall wc,
    Qlt 2 (chsh_stat_from_wc wc) ->
    forall a0 a1 b0 b1,
      is_bit a0 = true -> is_bit a1 = true ->
      is_bit b0 = true -> is_bit b1 = true ->
      ~ WCLocallyConsistent a0 a1 b0 b1 wc.
Proof.
  intros wc Hviolation a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 Hlc.
  exact (chsh_stat_violation_not_local wc Hviolation a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 Hlc).
Qed.

(** ** Corollary: S > 2 → for any locally factorizable strategy, the coupling
    it would require is separable — but no such strategy is consistent with S > 2.

    This combines the three theorems: any consistent local strategy gives a
    separable coupling. S > 2 rules out all consistent local strategies. Therefore
    S > 2 rules out all locally-consistent separable couplings. *)

Theorem chsh_violation_rules_out_locally_consistent_separable :
  forall wc a0 a1 b0 b1,
    is_bit a0 = true -> is_bit a1 = true ->
    is_bit b0 = true -> is_bit b1 = true ->
    Qlt 2 (chsh_stat_from_wc wc) ->
    ~ (WCLocallyConsistent a0 a1 b0 b1 wc /\
       separable_coupling (chsh_setting_outcome_coupling wc)).
Proof.
  intros wc a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 Hviolation [Hlc _].
  exact (chsh_stat_violation_not_local wc Hviolation a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 Hlc).
Qed.

(** ** What this establishes for the Thiele Machine.

    MORPH_ASSERT certifies that a morphism EXISTS with the claimed coupling data.
    A morphism coupling between two modules represents potential correlations.

    Locally factorizable morphisms: the coupling between module A's cells and
    module B's cells factors as fA × fB (each side determines its response
    independently). These give locally consistent CHSH strategies and produce
    S ≤ 2.

    The CHSH violation (S > 2): no locally factorizable morphism coupling can
    explain the statistics. If a certified morphism is asserted with coupling data
    that witnesses S > 2, the certification is proof that the correlations are
    non-local — beyond what any locally factorizable coupling can produce.

    This gives the morphism coupling language a precise CHSH semantics:
    the no-go theorem for locally factorizable couplings under CHSH violation. *)
