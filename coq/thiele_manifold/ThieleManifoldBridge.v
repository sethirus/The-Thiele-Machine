(** * ThieleManifoldBridge: instantiating the manifold on the Thiele VM

    This file packages the verified Thiele machine stack as a [System] in
    the [SelfReference] framework, lifts that base system into a
    [ThieleManifold] tower, and reuses [pi4] / [meta_system] to obtain a
    constructive 4D projection. On top of that abstract scaffold it
    transports the kernel's μ-ledger and irreversibility-count results
    from [MuLedgerConservation] into a faithful-implementation
    interface ([FaithfulImplementation]) suitable for hardware/RTL
    refinement statements.

    Three layers of content:

      - A minimal [Prog] type and a trivial observational equivalence
        [obs_equiv] used to put a [System] structure on Thiele programs
        ([thiele_system], [thiele_system_self_referential]).
      - A concrete tower [thiele_machine_manifold] whose level [n]
        applies [meta_system] iteratively, with explicit dimension
        formulae and μ-cost bounds.
      - Ledger/irreversibility transport theorems
        ([thiele_run_mu_bounds_irreversibility],
        [thiele_manifold_irreversibility_gap]) and the
        [FaithfulImplementation] record carrying a hardware-side
        refinement contract. *)

From Coq Require Import Arith Lia.
From SelfReference Require Import SelfReference.
From Spacetime Require Import Spacetime.
From ThieleManifold Require Import ThieleManifold.
From Coq Require Import List.
From Kernel Require Import MuLedgerConservation VMState VMStep SimulationProof.
Import ListNotations.

(** ** Minimal program type for the bridge

    A program is a list of VM instructions; observational equivalence
    is the trivial syntactic equality. The bridge does not need a
    finer notion: the only role [Prog] plays here is to act as a
    sentence-bearing carrier for the [System] structure. *)
Definition Prog := list vm_instruction.
Definition empty_prog : Prog := nil.
Definition obs_equiv (P Q : Prog) : Prop := P = Q.

(** Reflexivity of [obs_equiv]. *)
Lemma obs_equiv_refl : forall P, obs_equiv P P.
Proof. intros P. unfold obs_equiv. exact eq_refl. Qed.

(** ** A [System] instance driven by Thiele programs and receipts *)

(** The self-reference predicate at this level is the existence of a
    program observationally equivalent to itself — trivially populated
    by [empty_prog]. *)
Definition thiele_self_reference : Prop :=
  exists P : Prog, obs_equiv P P.

Lemma thiele_self_reference_true : thiele_self_reference.
Proof.
  exists empty_prog. apply obs_equiv_refl.
Qed.

(** [thiele_sentences Q] says that [Q] holds and witnesses its holding by
    pointing to some self-equivalent program. The conjunction enforces
    that every sentence is locally grounded in a Thiele program. *)
Definition thiele_sentences (Q : Prop) : Prop :=
  exists P : Prog, Q /\ obs_equiv P P.

(** True propositions are [thiele_sentences] via the empty program. *)
Lemma thiele_sentence_of_true : forall Q, Q -> thiele_sentences Q.
Proof.
  intros Q HQ. exists empty_prog. split; [assumption|apply obs_equiv_refl].
Qed.

(** The Thiele [System]: 4-dimensional, with sentences as defined above. *)
Definition thiele_system : System :=
  {| dimension := 4;
     sentences := thiele_sentences |}.

(** [thiele_system] is self-referential: its sentence "there is a
    self-equivalent program" is itself one of its sentences and is true. *)
Lemma thiele_system_self_referential : contains_self_reference thiele_system.
Proof.
  exists thiele_self_reference.
  split.
  - unfold thiele_sentences, thiele_self_reference.
    exists empty_prog. split; [apply thiele_self_reference_true|apply obs_equiv_refl].
  - apply thiele_self_reference_true.
Qed.

(** [thiele_system] can reason about [spacetime_system]: it absorbs every
    spacetime sentence by witnessing it through the empty program. The
    proof unwinds [spacetime_sentences] to extract a witness event and
    licenses [P] via the local entailment at that event. *)
Lemma thiele_system_reasons_about_spacetime :
  can_reason_about thiele_system spacetime_system.
Proof.
  unfold can_reason_about. intros P HP.
  unfold thiele_system. simpl.
  unfold spacetime_system in HP. simpl in HP.
  unfold spacetime_sentences in HP.
  destruct HP as [Q [e [He Himpl]]].
  unfold at_event in He.
  unfold thiele_sentences.
  exists empty_prog. split.
  - exact (Himpl e He).
  - apply obs_equiv_refl.
Qed.

(** ** Building a concrete Thiele manifold tower

    Level 0 is [thiele_system]; each successor level applies
    [meta_system]. The tower-laws below all reduce to properties of
    [meta_system]. *)
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

(** The shadow of the Thiele manifold can reason about spacetime: it
    absorbs spacetime sentences into [thiele_sentences] by witnessing
    them through the empty program. *)
Lemma thiele_manifold_supports_spacetime_shadow :
  can_reason_about (spacetime_shadow thiele_machine_manifold) spacetime_system.
Proof.
  unfold can_reason_about. intros P HP.
  unfold spacetime_shadow, pi4, thiele_machine_manifold. simpl.
  unfold spacetime_system in HP. simpl in HP.
  unfold spacetime_sentences in HP.
  destruct HP as [Q [e [He Himpl]]].
  unfold at_event in He.
  unfold thiele_level. simpl.
  unfold thiele_sentences.
  exists empty_prog. split.
  - exact (Himpl e He).
  - apply obs_equiv_refl.
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
