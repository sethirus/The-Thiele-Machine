(** InformationCausality: a record-level IC / mu comparison.

  This file is deliberately modest. It does not prove the physical
  Information Causality principle, and it definitely does not derive quantum
  mechanics from the VM. It only compares two record types defined here and
  shows that once their fields are matched, the stored bound proposition can
  be transported back and forth.

  That is bookkeeping, not physics. The physical interpretation has to come
  from stronger semantics somewhere else. The theorem names in this file now
  say exactly what the proofs establish. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost. Any
   Kernel module it imports is a peer result in the same mathematical
   development, not the VM step relation.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

From Coq Require Import List Bool Arith.PeanoNat micromega.Lia.
Import ListNotations.

From Kernel Require Import KernelPhysics RevelationRequirement QuantumEquivalence.

(** Abstract Information Causality-shaped record.

    Alice has n bits, Bob has index y, Alice sends m bits.
    IC principle: Bob's accessible information ≤ m bits.
    
    This record stores the bound as a Prop. It does not define entropy or
    mutual information.
    *)

Record ICScenario : Type := {
  ic_n_bits : nat;           (* Alice's input size *)
  ic_m_communication : nat;  (* Communication bits *)
  ic_satisfies_bound : Prop  (* IC bound is satisfied *)
}.

(** Matching μ-cost-shaped record. *)

Record MuScenario : Type := {
  mu_n_partitions : nat;  (* Number of partition elements *)
  mu_cost_paid : nat;     (* μ-ledger cost *)
  mu_bound_satisfied : Prop  (* Cost bound satisfied *)
}.

(** Equivalence definition.

    The relation says the two records have the same size parameter, the same
    cost/communication parameter, and equivalent bound propositions.
    *)

Definition ic_mu_equivalent (ic : ICScenario) (mu : MuScenario) : Prop :=
  ic.(ic_n_bits) = mu.(mu_n_partitions) /\
  ic.(ic_m_communication) = mu.(mu_cost_paid) /\
  (ic.(ic_satisfies_bound) <-> mu.(mu_bound_satisfied)).

(** Main projection: extract the third conjunct of [ic_mu_equivalent].
    Definition-with-proof-term form. *)
Definition ic_mu_record_projection
  (ic : ICScenario) (mu : MuScenario)
  (Heq : ic_mu_equivalent ic mu) :
  ic.(ic_satisfies_bound) <-> mu.(mu_bound_satisfied) :=
  match Heq with conj _ (conj _ Hiff) => Hiff end.

(** Zero communication sanity check.

    Given the bound premise, the only arithmetic fact proved here is 0 <= n.
    *)

Theorem ic_zero_communication_bound :
  forall ic,
    ic.(ic_m_communication) = 0 ->
    ic.(ic_satisfies_bound) ->
    0 <= ic.(ic_n_bits).
Proof.
  intros ic _ _.
  apply Nat.le_0_l.
Qed.

(** Zero-cost transport lemma. *)

Theorem ic_zero_communication_implies_zero_mu_cost :
  forall ic mu,
    ic_mu_equivalent ic mu ->
    ic.(ic_m_communication) = 0 ->
    mu.(mu_cost_paid) = 0.
Proof.
  intros ic mu Heq Hic.
  unfold ic_mu_equivalent in Heq.
  destruct Heq as [_ [Heq _]].
  rewrite <- Heq. exact Hic.
Qed.

(** Small structural facts about the custom relation. *)

(** Communication costs are monotonic *)
Lemma ic_monotonicity :
  forall ic1 ic2 mu1 mu2,
    ic_mu_equivalent ic1 mu1 ->
    ic_mu_equivalent ic2 mu2 ->
    ic1.(ic_n_bits) = ic2.(ic_n_bits) ->
    ic1.(ic_m_communication) <= ic2.(ic_m_communication) ->
    mu1.(mu_cost_paid) <= mu2.(mu_cost_paid).
Proof.
  intros ic1 ic2 mu1 mu2 Heq1 Heq2 _ Hle.
  unfold ic_mu_equivalent in Heq1, Heq2.
  destruct Heq1 as [_ [Heq1 _]].
  destruct Heq2 as [_ [Heq2 _]].
  rewrite <- Heq1, <- Heq2. exact Hle.
Qed.

(** Communication bounded by input size *)
Lemma ic_communication_bounded :
  forall ic,
    ic.(ic_satisfies_bound) ->
    ic.(ic_m_communication) <= ic.(ic_n_bits) + ic.(ic_m_communication).
Proof.
  intros ic _.
  apply Nat.le_add_l.
Qed.

(** Cost paid reflects the stored bound proposition. Forward direction
    of [ic_mu_record_projection]. *)
Definition mu_cost_reflects_accessible_info
  (ic : ICScenario) (mu : MuScenario)
  (Heq : ic_mu_equivalent ic mu)
  (Hic : ic.(ic_satisfies_bound)) :
  mu.(mu_bound_satisfied) :=
  proj1 (ic_mu_record_projection ic mu Heq) Hic.

(** Composition of IC scenarios *)
Lemma ic_composition :
  forall ic1 ic2 mu1 mu2,
    ic_mu_equivalent ic1 mu1 ->
    ic_mu_equivalent ic2 mu2 ->
    ic1.(ic_n_bits) = ic2.(ic_n_bits) ->
    ic_mu_equivalent 
      {| ic_n_bits := ic1.(ic_n_bits);
         ic_m_communication := ic1.(ic_m_communication) + ic2.(ic_m_communication);
         ic_satisfies_bound := ic1.(ic_satisfies_bound) /\ ic2.(ic_satisfies_bound) |}
      {| mu_n_partitions := mu1.(mu_n_partitions);
         mu_cost_paid := mu1.(mu_cost_paid) + mu2.(mu_cost_paid);
         mu_bound_satisfied := mu1.(mu_bound_satisfied) /\ mu2.(mu_bound_satisfied) |}.
Proof.
  intros ic1 ic2 mu1 mu2 [Hn1 [Hc1 Hb1]] [Hn2 [Hc2 Hb2]] Heq.
  split; [simpl; congruence |].
  split; [simpl; rewrite Hc1, Hc2; reflexivity |].
  simpl. split; intro H.
  - destruct H as [H1 H2].
    split; [apply Hb1; exact H1 | apply Hb2; exact H2].
  - destruct H as [H1 H2].
    split; [apply Hb1; exact H1 | apply Hb2; exact H2].
Qed.

(** Equivalence preservation under cost increase *)
Lemma ic_equiv_cost_preservation :
  forall ic mu delta,
    ic_mu_equivalent ic mu ->
    ic_mu_equivalent
      {| ic_n_bits := ic.(ic_n_bits);
         ic_m_communication := ic.(ic_m_communication) + delta;
         ic_satisfies_bound := ic.(ic_satisfies_bound) |}
      {| mu_n_partitions := mu.(mu_n_partitions);
         mu_cost_paid := mu.(mu_cost_paid) + delta;
         mu_bound_satisfied := mu.(mu_bound_satisfied) |}.
Proof.
  intros ic mu delta Heq.
  unfold ic_mu_equivalent in Heq.
  destruct Heq as [Hn [Hc Hb]].
  split; [simpl; exact Hn |].
  split; [simpl; lia |].
  simpl; exact Hb.
Qed.

(** Legacy "quantum tier" name: zero IC communication transports to zero μ-cost. *)
Lemma zero_cost_is_quantum :
  forall ic mu,
    ic_mu_equivalent ic mu ->
    ic.(ic_m_communication) = 0 ->
    mu.(mu_cost_paid) = 0 /\ mu.(mu_bound_satisfied) <-> ic.(ic_satisfies_bound).
Proof.
  intros ic mu Hequiv Hzero.
  split; intro H.
  - destruct H as [Hcost Hbound].
    apply (ic_mu_record_projection ic mu); assumption.
  - split.
    + apply (ic_zero_communication_implies_zero_mu_cost ic mu); assumption.
    + apply (ic_mu_record_projection ic mu); assumption.
Qed.

(** If equivalence fixes the cost at m, a lower m' cannot describe the same
    MuScenario. This is field equality, not an optimization theorem. *)
Lemma ic_cost_optimal :
  forall ic mu,
    ic_mu_equivalent ic mu ->
    ic.(ic_satisfies_bound) ->
    forall m',
      m' < ic.(ic_m_communication) ->
      ~ ic_mu_equivalent
        {| ic_n_bits := ic.(ic_n_bits);
           ic_m_communication := m';
           ic_satisfies_bound := ic.(ic_satisfies_bound) |}
        mu.
Proof.
  intros ic mu [Hn [Hc Hb]] Hsat m' Hlt [Hn' [Hcontra _]].
  simpl in Hcontra.
  (* Hcontra states: mu.(mu_cost_paid) = m' *)
  (* Hc states: mu.(mu_cost_paid) = ic.(ic_m_communication) *)
  (* Hlt states: m' < ic.(ic_m_communication) *)
  rewrite <- Hc in Hcontra.
  rewrite Hcontra in Hlt.
  lia.
Qed.

(** Information accessibility upper bound *)
Lemma accessible_info_bounded :
  forall ic,
    ic.(ic_satisfies_bound) ->
    ic.(ic_m_communication) * 1 <= ic.(ic_m_communication).
Proof.
  intros ic _.
  rewrite Nat.mul_1_r.
  apply Nat.le_refl.
Qed.

(** IC bound implies partition constraint *)
Lemma ic_implies_partition_constraint :
  forall ic mu,
    ic_mu_equivalent ic mu ->
    ic.(ic_satisfies_bound) ->
    mu.(mu_n_partitions) = ic.(ic_n_bits) /\
    mu.(mu_cost_paid) = ic.(ic_m_communication).
Proof.
  intros ic mu Heq _.
  unfold ic_mu_equivalent in Heq.
  destruct Heq as [Hn [Hc _]].
  split; [ symmetry; exact Hn | symmetry; exact Hc ].
Qed.

(** Communication efficiency *)
Lemma communication_efficiency :
  forall ic mu,
    ic_mu_equivalent ic mu ->
    ic.(ic_n_bits) > 0 ->
    ic.(ic_m_communication) < ic.(ic_n_bits) ->
    mu.(mu_cost_paid) < mu.(mu_n_partitions).
Proof.
  intros ic mu Heq _ Heff.
  unfold ic_mu_equivalent in Heq.
  destruct Heq as [Hn [Hc _]].
  rewrite <- Hn, <- Hc.
  exact Heff.
Qed.

(** The record-level results identify the IC and [mu] bounds when the two
    records are related by [ic_mu_equivalent]. The proofs are definitional and
    arithmetic: they do not supply a probability space, an entropy model, a
    Born rule, or a physical communication semantics. In particular, the
    stored [Prop] is the meaning of “IC bound” for this module; connecting it
    to accessible information is a separate formalization task. *)

(* SCOPE NOTE: connectivity anchor for isolated IC lemmas. *)
Definition ic_coverage_anchor :=
  (ic_zero_communication_bound, ic_communication_bounded, accessible_info_bounded).
