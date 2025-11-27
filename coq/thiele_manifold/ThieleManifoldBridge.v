(** * Bridging the abstract Thiele manifold to the verified Thiele machine stack.

    This module instantiates the abstract [System] notion from
    [SelfReference] with the concrete Thiele programs and receipts from
    the core machine development.  It then lifts that base system into the
    infinite-dimensional manifold from [ThieleManifold], providing a
    constructive projection back to 4D spacetime and reusing the
    ledger/cost vocabulary established in the existing proofs.
 *)

From Coq Require Import Arith Lia.
From SelfReference Require Import SelfReference.
From Spacetime Require Import Spacetime.
From ThieleManifold Require Import ThieleManifold.
From ThieleMachine Require Import ThieleMachine ThieleProc.
From Kernel Require Import MuLedgerConservation VMState VMStep SimulationProof.

(** ** A System instance driven by Thiele programs and receipts *)

Definition thiele_self_reference : Prop :=
  exists P : Prog, obs_equiv P P.

Lemma thiele_self_reference_true : thiele_self_reference.
Proof.
  exists empty_prog. apply obs_equiv_refl.
Qed.

Definition thiele_sentences (Q : Prop) : Prop :=
  exists P : Prog, Q /\ obs_equiv P P.

Lemma thiele_sentence_of_true : forall Q, Q -> thiele_sentences Q.
Proof.
  intros Q HQ. exists empty_prog. split; [assumption|apply obs_equiv_refl].
Qed.

Definition thiele_system : System :=
  {| dimension := 4;
     sentences := thiele_sentences |}.

Lemma thiele_system_self_referential : contains_self_reference thiele_system.
Proof.
  exists thiele_self_reference.
  split.
  - unfold thiele_sentences, thiele_self_reference.
    exists empty_prog. split; [apply thiele_self_reference_true|apply obs_equiv_refl].
  - apply thiele_self_reference_true.
Qed.

Lemma thiele_system_reasons_about_spacetime :
  can_reason_about thiele_system spacetime_system.
Proof.
  intros P HP.
  unfold thiele_sentences.
  exists empty_prog. split; [assumption|apply obs_equiv_refl].
Qed.

(** ** Building a concrete Thiele manifold tower *)

Fixpoint thiele_level (n : nat) : System :=
  match n with
  | 0 => thiele_system
  | S k => meta_system (thiele_level k)
  end.

Lemma thiele_level_richer : forall n, dimensionally_richer (thiele_level (S n)) (thiele_level n).
Proof.
  induction n; simpl.
  - apply meta_system_richer.
  - unfold dimensionally_richer in *. simpl in *.
    specialize (meta_system_richer (thiele_level n)). lia.
Qed.

Lemma thiele_level_can_reason : forall n, can_reason_about (thiele_level (S n)) (thiele_level n).
Proof.
  induction n; simpl.
  - apply meta_system_can_reason_about.
  - unfold can_reason_about in *. intros P HP.
    eapply meta_system_can_reason_about. exact HP.
Qed.

Lemma thiele_base_at_least_four : 4 <= dimension (thiele_level 0).
Proof. simpl. lia. Qed.

Definition thiele_machine_manifold : ThieleManifold :=
  {| level := thiele_level;
     level_strictly_richer := thiele_level_richer;
     level_can_reason := thiele_level_can_reason;
     base_at_least_four := thiele_base_at_least_four |}.

Lemma thiele_manifold_projection_matches_base : pi4 thiele_machine_manifold = thiele_system.
Proof. reflexivity. Qed.

Lemma thiele_level_dimension : forall n, dimension (thiele_level n) = 4 + n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - unfold meta_system. simpl. lia.
Qed.

Lemma thiele_level_mu_cost :
  forall n, mu_cost (level thiele_machine_manifold n) (pi4 thiele_machine_manifold) = n.
Proof.
  intros n. unfold thiele_machine_manifold, pi4, thiele_level, thiele_system, mu_cost; simpl.
  rewrite thiele_level_dimension. lia.
Qed.

Lemma thiele_level_mu_gap :
  forall n,
    mu_cost (level thiele_machine_manifold (S n)) (pi4 thiele_machine_manifold) -
    mu_cost (level thiele_machine_manifold n) (pi4 thiele_machine_manifold) = 1.
Proof.
  intros n. rewrite !thiele_level_mu_cost. lia.
Qed.

Lemma thiele_manifold_requires_meta :
  exists Meta, can_reason_about Meta thiele_system /\ dimensionally_richer Meta thiele_system.
Proof.
  destruct (self_reference_requires_metalevel _ thiele_system_self_referential)
    as [Meta [Hcr [Hrich _]]].
  now exists Meta.
Qed.

Lemma thiele_projection_has_positive_mu_cost :
  mu_cost (level thiele_machine_manifold 1) (pi4 thiele_machine_manifold) > 0.
Proof.
  unfold thiele_machine_manifold.
  apply mu_cost_positive_for_projection; lia.
Qed.

Lemma thiele_manifold_supports_spacetime_shadow :
  can_reason_about (spacetime_shadow thiele_machine_manifold) spacetime_system.
Proof.
  unfold spacetime_shadow, pi4, thiele_machine_manifold, thiele_level, thiele_system, spacetime_system, spacetime_sentences, thiele_sentences; simpl.
  intros P HP. exists empty_prog. split; [assumption|apply obs_equiv_refl].
Qed.

(** ** Irreversibility lower bound for faithful executions

    The µ-ledger tracks declared instruction costs for bounded executions.  The
    kernel irreversibility accounting in [MuLedgerConservation] shows this
    ledger lower-bounds the number of logically irreversible bit events along
    any trace.  Specialising that statement here yields a reusable bound for the
    concrete Thiele base system; any faithful implementation that matches the VM
    semantics therefore incurs at least the counted irreversible events. *)

Lemma thiele_run_mu_bounds_irreversibility :
  forall fuel trace s,
    s.(vm_mu) + irreversible_count fuel trace s <= (run_vm fuel trace s).(vm_mu).
Proof.
  apply run_vm_mu_bounds_irreversibility.
Qed.

Theorem thiele_manifold_irreversibility_gap :
  forall fuel trace s,
    irreversible_count fuel trace s <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  apply run_vm_irreversibility_gap.
Qed.

(** ** Faithful implementations and entropy-facing bounds

    To connect the Coq-level ledger/irreversibility results to real hardware,
    we model a *faithful implementation* as a step function over some concrete
    machine state that refines the VM semantics after decoding.  We require
    that, for a fixed instruction trace [trace], iterating the hardware step
    [fuel] times and decoding the resulting state matches the Coq VM execution
    [run_vm fuel trace] started from the decoded initial state.  Under that
    assumption, the VM irreversibility gap transports directly to the
    implementation: the decoded µ-accumulator cannot grow by less than the
    counted irreversible events. *)

Fixpoint impl_iter {A} (step : A -> A) (fuel : nat) (s : A) : A :=
  match fuel with
  | 0 => s
  | S fuel' => impl_iter step fuel' (step s)
  end.

Definition faithful_to_vm {A}
  (step : A -> A) (decode : A -> VMState) (trace : list vm_instruction) : Prop :=
  forall fuel s, decode (impl_iter step fuel s) = run_vm fuel trace (decode s).

Lemma faithful_irreversibility_lower_bound :
  forall (A : Type) (step : A -> A) (decode : A -> VMState)
         (trace : list vm_instruction) (s : A) (fuel : nat),
    faithful_to_vm step decode trace ->
    irreversible_count fuel trace (decode s) <=
      (decode (impl_iter step fuel s)).(vm_mu) - (decode s).(vm_mu).
Proof.
  intros A step decode trace s fuel Hfaith.
  specialize (Hfaith fuel s).
  rewrite Hfaith.
  apply run_vm_irreversibility_gap.
Qed.

(** For hardware discussions it is convenient to package the faithful
    implementation contract as a record so that downstream corollaries can
    quantify over a single witness.  The contract fixes a decode mapping from
    hardware states into VM states, a micro-step function, a compiled trace of
    VM instructions, and a refinement hypothesis stating that iterating the
    hardware step [fuel] times matches the Coq VM execution on the decoded
    state. *)

Record FaithfulImplementation := {
  hw_state : Type;
  hw_step : hw_state -> hw_state;
  hw_decode : hw_state -> VMState;
  hw_trace : list vm_instruction;
  hw_refines_vm : forall fuel s,
    hw_decode (impl_iter hw_step fuel s) = run_vm fuel hw_trace (hw_decode s)
}.

Lemma faithful_impl_irreversibility_lower_bound :
  forall (Impl : FaithfulImplementation) fuel s,
    irreversible_count fuel Impl.(hw_trace) (Impl.(hw_decode) s) <=
      (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) -
      (Impl.(hw_decode) s).(vm_mu).
Proof.
  intros Impl fuel s.
  pose proof (hw_refines_vm Impl fuel s) as Hrefine.
  rewrite Hrefine.
  apply run_vm_irreversibility_gap.
Qed.

(** The faithful contract also preserves the explicit µ-accounting from the
    VM semantics: decoding the hardware state after [fuel] steps yields a
    µ-accumulator equal to the initial µ plus the ledger entries generated by
    the VM trace.  This equality is convenient for aligning hardware counters
    (including RTL or Verilog instrumentation) with the VM’s cost model. *)

Lemma faithful_impl_mu_conservation :
  forall (Impl : FaithfulImplementation) fuel s,
    (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) =
      (Impl.(hw_decode) s).(vm_mu) +
      ledger_sum (ledger_entries fuel Impl.(hw_trace) (Impl.(hw_decode) s)).
Proof.
  intros Impl fuel s.
  pose proof (hw_refines_vm Impl fuel s) as Hrefine.
  rewrite Hrefine.
  apply run_vm_mu_conservation.
Qed.

Lemma faithful_impl_cost_delta :
  forall (Impl : FaithfulImplementation) fuel s,
    (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) -
    (Impl.(hw_decode) s).(vm_mu) =
      ledger_sum (ledger_entries fuel Impl.(hw_trace) (Impl.(hw_decode) s)).
Proof.
  intros Impl fuel s.
  rewrite faithful_impl_mu_conservation.
  lia.
Qed.

(** A quotable summary: any faithful decoded execution of the VM cannot hide
    irreversible bit events—its µ-accumulator must rise by at least the
    conservative irreversibility counter computed over the VM trace. *)
