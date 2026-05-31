(** CommitmentCostDecomposition: A2 as the exact incremental component
    inside a richer cost model.

    [CommitmentPredicateAdequacy.v] proves the substitution gate in a
    predicate-only pricing model.  Real machines also charge background work:
    payload bits, arithmetic, IO, proof checking, etc.  This file factors that
    richer situation.

    A decomposed system has:

      total_cost = background_cost + unit(local_charge)

    The theorems here say the commitment component lower-bounds, and exactly
    equals, the number of certification commitments precisely when the
    local-charge predicate contains, respectively equals, the cert-flip
    predicate.  The final section instantiates the decomposition for the real
    VM's [vm_certified] channel: the [instruction_cost] schedule splits into
    background cost plus one A2 unit exactly on certification flips.
*)

From Coq Require Import List Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

Record DecomposedCommitmentSystem := mk_decomposed_commitment_system {
  dcs_state  : Type;
  dcs_instr  : Type;
  dcs_step   : dcs_state -> dcs_instr -> dcs_state;
  dcs_cost   : dcs_state -> dcs_instr -> nat;
  dcs_base   : dcs_state -> dcs_instr -> nat;
  dcs_cert   : dcs_state -> bool;
  dcs_charge : dcs_state -> dcs_instr -> bool;

  dcs_cost_decomposes :
    forall (s : dcs_state) (i : dcs_instr),
      dcs_cost s i =
      dcs_base s i + (if dcs_charge s i then 1 else 0);
}.

Fixpoint dcs_run (DCS : DecomposedCommitmentSystem)
                 (trace : list (dcs_instr DCS))
                 (s : dcs_state DCS) : dcs_state DCS :=
  match trace with
  | [] => s
  | i :: rest => dcs_run DCS rest (dcs_step DCS s i)
  end.

Fixpoint dcs_total_cost (DCS : DecomposedCommitmentSystem)
                        (trace : list (dcs_instr DCS))
                        (s : dcs_state DCS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      dcs_cost DCS s i
      + dcs_total_cost DCS rest (dcs_step DCS s i)
  end.

Fixpoint dcs_total_base (DCS : DecomposedCommitmentSystem)
                        (trace : list (dcs_instr DCS))
                        (s : dcs_state DCS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      dcs_base DCS s i
      + dcs_total_base DCS rest (dcs_step DCS s i)
  end.

Fixpoint dcs_commitment_component (DCS : DecomposedCommitmentSystem)
                                  (trace : list (dcs_instr DCS))
                                  (s : dcs_state DCS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      (if dcs_charge DCS s i then 1 else 0)
      + dcs_commitment_component DCS rest (dcs_step DCS s i)
  end.

Definition dcs_cert_flip_local (DCS : DecomposedCommitmentSystem)
           (s : dcs_state DCS) (i : dcs_instr DCS) : bool :=
  andb (negb (dcs_cert DCS s))
       (dcs_cert DCS (dcs_step DCS s i)).

Fixpoint dcs_cert_flip_count (DCS : DecomposedCommitmentSystem)
                             (trace : list (dcs_instr DCS))
                             (s : dcs_state DCS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      (if dcs_cert_flip_local DCS s i then 1 else 0)
      + dcs_cert_flip_count DCS rest (dcs_step DCS s i)
  end.

Definition dcs_local_predicate_le (DCS : DecomposedCommitmentSystem)
           (P Q : dcs_state DCS -> dcs_instr DCS -> bool) : Prop :=
  forall s i, P s i = true -> Q s i = true.

Definition dcs_local_predicate_same (DCS : DecomposedCommitmentSystem)
           (P Q : dcs_state DCS -> dcs_instr DCS -> bool) : Prop :=
  dcs_local_predicate_le DCS P Q /\ dcs_local_predicate_le DCS Q P.

Theorem dcs_total_cost_splits :
  forall (DCS : DecomposedCommitmentSystem)
         (trace : list (dcs_instr DCS))
         (s0 : dcs_state DCS),
    dcs_total_cost DCS trace s0 =
    dcs_total_base DCS trace s0
    + dcs_commitment_component DCS trace s0.
Proof.
  intros DCS trace.
  induction trace as [| i rest IH]; intros s0.
  - reflexivity.
  - simpl.
    rewrite dcs_cost_decomposes.
    rewrite IH.
    lia.
Qed.

Theorem dcs_commitment_component_lower_bound_iff :
  forall (DCS : DecomposedCommitmentSystem),
    (forall trace s0,
        dcs_commitment_component DCS trace s0 >=
        dcs_cert_flip_count DCS trace s0)
    <->
    dcs_local_predicate_le DCS (dcs_cert_flip_local DCS) (dcs_charge DCS).
Proof.
  intros DCS. split.
  - intros Hfloor s i Hflip.
    destruct (dcs_charge DCS s i) eqn:Hcharge; [reflexivity|].
    exfalso.
    pose proof (Hfloor [i] s) as Hone.
    simpl in Hone.
    rewrite Hflip, Hcharge in Hone.
    lia.
  - intros Hle trace.
    induction trace as [| i rest IH]; intros s0.
    + simpl. lia.
    + simpl.
      destruct (dcs_cert_flip_local DCS s0 i) eqn:Hflip.
      * pose proof (Hle s0 i Hflip) as Hcharge.
        rewrite Hcharge.
        pose proof (IH (dcs_step DCS s0 i)).
        lia.
      * pose proof (IH (dcs_step DCS s0 i)).
        destruct (dcs_charge DCS s0 i); lia.
Qed.

Theorem dcs_commitment_component_exact_iff :
  forall (DCS : DecomposedCommitmentSystem),
    (forall trace s0,
        dcs_commitment_component DCS trace s0 =
        dcs_cert_flip_count DCS trace s0)
    <->
    dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS).
Proof.
  intros DCS. split.
  - intros Heq. split.
    + apply dcs_commitment_component_lower_bound_iff.
      intros trace s0. rewrite Heq. lia.
    + intros s i Hcharge.
      destruct (dcs_cert_flip_local DCS s i) eqn:Hflip; [reflexivity|].
      pose proof (Heq [i] s) as Hone.
      simpl in Hone.
      rewrite Hcharge, Hflip in Hone.
      discriminate.
  - intros [Hcf_le_charge Hcharge_le_cf] trace.
    induction trace as [| i rest IH]; intros s0.
    + reflexivity.
    + simpl.
      assert (Heq_step :
        dcs_charge DCS s0 i = dcs_cert_flip_local DCS s0 i).
      { destruct (dcs_charge DCS s0 i) eqn:Hcharge;
        destruct (dcs_cert_flip_local DCS s0 i) eqn:Hflip; try reflexivity.
        - pose proof (Hcharge_le_cf s0 i Hcharge) as Hcontra.
          rewrite Hflip in Hcontra. discriminate.
        - pose proof (Hcf_le_charge s0 i Hflip) as Hcontra.
          rewrite Hcharge in Hcontra. discriminate. }
      rewrite Heq_step.
      rewrite IH.
      reflexivity.
Qed.

Theorem dcs_exact_total_cost_formula_iff :
  forall (DCS : DecomposedCommitmentSystem),
    (forall trace s0,
        dcs_total_cost DCS trace s0 =
        dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0)
    <->
    dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS).
Proof.
  intros DCS. split.
  - intros Htotal.
    apply dcs_commitment_component_exact_iff.
    intros trace s0.
    pose proof (dcs_total_cost_splits DCS trace s0) as Hsplit.
    rewrite Htotal in Hsplit.
    lia.
  - intros Hsame trace s0.
    rewrite dcs_total_cost_splits.
    pose proof (proj2 (dcs_commitment_component_exact_iff DCS) Hsame trace s0)
      as Hcomp.
    rewrite Hcomp.
    reflexivity.
Qed.

(** In a decomposed machine with arbitrary background costs, the substitution
    test lands on the commitment component: an exact "background plus one per
    commitment" formula is impossible for any non-A2 local charge predicate. *)
Theorem dcs_substitution_test_rejects_non_a2_exact_component :
  forall (DCS : DecomposedCommitmentSystem),
    ~ dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS) ->
    ~ (forall trace s0,
          dcs_total_cost DCS trace s0 =
          dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0).
Proof.
  intros DCS Hnot_same Htotal.
  apply Hnot_same.
  apply dcs_exact_total_cost_formula_iff.
  exact Htotal.
Qed.

Theorem dcs_exact_component_substitute_is_a2 :
  forall (DCS : DecomposedCommitmentSystem),
    (forall trace s0,
        dcs_total_cost DCS trace s0 =
        dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0) ->
    dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS).
Proof.
  intros DCS Htotal.
  apply dcs_exact_total_cost_formula_iff.
  exact Htotal.
Qed.

(** ** Real VM instantiation for [vm_certified]. *)

Definition vm_cert_flip (s : VMState) (i : vm_instruction) : bool :=
  andb (negb s.(vm_certified))
       (vm_apply s i).(vm_certified).

Definition vm_commitment_background_cost (s : VMState) (i : vm_instruction) : nat :=
  if vm_cert_flip s i then instruction_cost i - 1 else instruction_cost i.

Lemma vm_instruction_cost_decomposes_cert_commitment :
  forall (s : VMState) (i : vm_instruction),
    instruction_cost i =
    vm_commitment_background_cost s i + (if vm_cert_flip s i then 1 else 0).
Proof.
  intros s i.
  unfold vm_commitment_background_cost.
  destruct (vm_cert_flip s i) eqn:Hflip.
  - unfold vm_cert_flip in Hflip.
    apply Bool.andb_true_iff in Hflip.
    destruct Hflip as [Hbefore Hafter].
    apply Bool.negb_true_iff in Hbefore.
    pose proof (no_free_certification_certified s i Hbefore Hafter) as Hcost.
    lia.
  - lia.
Qed.

Definition vm_certified_decomposed_system : DecomposedCommitmentSystem :=
  {| dcs_state := VMState;
     dcs_instr := vm_instruction;
     dcs_step := vm_apply;
     dcs_cost := fun _ i => instruction_cost i;
     dcs_base := vm_commitment_background_cost;
     dcs_cert := vm_certified;
     dcs_charge := vm_cert_flip;
     dcs_cost_decomposes := vm_instruction_cost_decomposes_cert_commitment |}.

Theorem vm_certified_commitment_component_exact :
  forall trace s0,
    dcs_commitment_component vm_certified_decomposed_system trace s0 =
    dcs_cert_flip_count vm_certified_decomposed_system trace s0.
Proof.
  apply dcs_commitment_component_exact_iff.
  split; intros s i H; exact H.
Qed.

Theorem vm_instruction_cost_exactly_background_plus_cert_commitments :
  forall trace s0,
    dcs_total_cost vm_certified_decomposed_system trace s0 =
    dcs_total_base vm_certified_decomposed_system trace s0
    + dcs_cert_flip_count vm_certified_decomposed_system trace s0.
Proof.
  apply dcs_exact_total_cost_formula_iff.
  split; intros s i H; exact H.
Qed.

Print Assumptions dcs_total_cost_splits.
Print Assumptions dcs_commitment_component_lower_bound_iff.
Print Assumptions dcs_commitment_component_exact_iff.
Print Assumptions dcs_exact_total_cost_formula_iff.
Print Assumptions dcs_substitution_test_rejects_non_a2_exact_component.
Print Assumptions dcs_exact_component_substitute_is_a2.
Print Assumptions vm_instruction_cost_decomposes_cert_commitment.
Print Assumptions vm_certified_commitment_component_exact.
Print Assumptions vm_instruction_cost_exactly_background_plus_cert_commitments.
