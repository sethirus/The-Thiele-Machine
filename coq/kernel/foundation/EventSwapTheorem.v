(** Proved outcomes for the swap theorem of [EventSwapCore]. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import EventSwapCore EventGeneralization.
From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality AbstractNoFI PrimeAxiom.
From Kernel Require Import ShadowPricing ProjectionNonExistence.

(** The counterexample starts from the ordinary initialized VM state, whose
    register file has the intended fixed width. *)
Lemma init_state_register_width :
  length (vm_regs init_state) = REG_COUNT.
Proof. reflexivity. Qed.

Lemma eg_graph_reading_latchable : latchable eg_graph_reading.
Proof.
  split.
  - exact (proj1 eg_graph_latchable).
  - exists init_state, (instr_pnew [] 0). split; reflexivity.
Qed.

Theorem swap_preserves_main_results_refuted : ~ swap_preserves_main_results.
Proof.
  intro Hswap.
  destruct (Hswap eg_graph_reading eg_graph_reading_latchable)
    as [Hpriced _].
  specialize (Hpriced init_state (instr_pnew [] 0) eq_refl eq_refl).
  simpl in Hpriced. lia.
Qed.

Lemma certification_reading_permanent :
  permanent_reading certification_reading.
Proof.
  intros s i Hcert.
  unfold certification_reading in *.
  rewrite vm_apply_certified.
  destruct i; simpl; exact Hcert || reflexivity.
Qed.

Lemma certification_reading_written : written certification_reading.
Proof.
  exists init_state, (instr_certify 0). split; reflexivity.
Qed.

Lemma certification_hidden_from_bare :
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

Theorem certification_main_results_hold : certification_main_results.
Proof.
  split.
  - split.
    + exact certification_reading_permanent.
    + exact certification_reading_written.
  - split.
    + intros s i Hbefore Hafter.
      exact (no_free_certification_certified s i Hbefore Hafter).
    + split.
      * exact cert_not_function_of_forget.
      * split.
        -- exact certification_hidden_from_bare.
        -- split.
           ++ exact vm_bare_shadow_cannot_price_exactly.
           ++ exact vm_forget_shadow_cannot_price_exactly.
Qed.

Print Assumptions swap_preserves_main_results_refuted.
Print Assumptions certification_main_results_hold.
