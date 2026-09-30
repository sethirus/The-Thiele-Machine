(** Closed outcomes for Part 1, Item 1.3: the frozen swap theorem. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import EventSwapCore EventGeneralization.
From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality AbstractNoFI PrimeAxiom.
From Kernel Require Import ShadowPricing ProjectionNonExistence.

(** The counterexample starts from the ordinary initialized VM state, whose
    register file has the intended fixed width. *)
Lemma item1_3_init_register_width :
  length (vm_regs init_state) = REG_COUNT.
Proof. reflexivity. Qed.

Lemma item1_3_graph_latchable_fixed : latchable eg_graph_reading.
Proof.
  split.
  - exact (proj1 eg_graph_latchable).
  - exists init_state, (instr_pnew [] 0). split; reflexivity.
Qed.

Theorem item1_3_swap_refuted : ~ swap_preserves_main_results.
Proof.
  intro Hswap.
  destruct (Hswap eg_graph_reading item1_3_graph_latchable_fixed)
    as [Hpriced _].
  specialize (Hpriced init_state (instr_pnew [] 0) eq_refl eq_refl).
  simpl in Hpriced. lia.
Qed.

Lemma item1_3_certification_permanent :
  permanent_reading certification_reading.
Proof.
  intros s i Hcert.
  unfold certification_reading in *.
  rewrite vm_apply_certified.
  destruct i; simpl; exact Hcert || reflexivity.
Qed.

Lemma item1_3_certification_written : written certification_reading.
Proof.
  exists init_state, (instr_certify 0). split; reflexivity.
Qed.

Lemma item1_3_certification_hidden_from_bare :
  hidden_from_bare certification_reading.
Proof.
  intros [read Hread].
  assert (Hshows : forall s, vm_cert s = read (bare_observable s)).
  { intros s. unfold vm_cert, certification_reading in Hread.
    symmetry. exact (Hread s). }
  pose proof (window_showing_reading_has_no_collision
                VMState vm_instruction BareTMObservable
                vm_apply vm_cert bare_observable read Hshows) as Hno.
  exact (Hno vm_bare_observable_collision).
Qed.

Theorem item1_3_certification_sanity : certification_main_results.
Proof.
  split.
  - split.
    + exact item1_3_certification_permanent.
    + exact item1_3_certification_written.
  - split.
    + intros s i Hbefore Hafter.
      exact (no_free_certification_certified s i Hbefore Hafter).
    + split.
      * exact cert_not_function_of_forget.
      * split.
        -- exact item1_3_certification_hidden_from_bare.
        -- split.
           ++ exact vm_bare_shadow_cannot_price_exactly.
           ++ exact vm_forget_shadow_cannot_price_exactly.
Qed.

Print Assumptions item1_3_swap_refuted.
Print Assumptions item1_3_certification_sanity.
