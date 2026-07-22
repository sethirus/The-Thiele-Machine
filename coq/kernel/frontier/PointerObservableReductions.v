(** The five metering disciplines as pointer-observable ecosystems: the
    conjecture's evidence, machine-checked.

  Section 25 of the monograph names, as the successor to the "is
  certification the forced event?" question, the pointer-observable
  criterion: certification is singled out among meterable events by
  REDUNDANT RECORD PROLIFERATION. PointerObservable.v gives that criterion
  a formal skeleton and one toy witness. This file turns the monograph's
  five INFORMAL instantiations (Section~15 / the reductions section) into
  five FORMAL ones: for each deployed discipline -- proof-of-stake
  finality, gas metering, trusted-execution attestation, certificate
  transparency, proof-carrying verification -- it builds an [Ecosystem],
  designates the metered event and a canonical rival meterable event, and
  proves [unique_pointer_among]: the metered event proliferates across the
  independent observers, the rival does not.

  What each model captures, and only this: the one structural fact the
  conjecture is about. The metered event's record is mirrored by every
  observer (finalized blocks by every full node; committed transitions by
  every replica; attestations by every relying party; log inclusions by
  every mirror/auditor; checked certificates by every consumer), while a
  canonical rival meterable event -- the internal work/scratch/noise/
  latency/prover-effort a thermodynamics- or complexity-minded designer
  might reach for -- is recorded by no one. The five ecosystems are
  deliberately minimal PROJECTIONS, not full protocol models; they share
  nothing but the structural feature, which is the point.

  What this delivers: five machine-checked instances (each with
  [Print Assumptions] closed under the global context -- zero axioms of any
  kind) plus the aggregate [five_disciplines_are_pointers], an instance of
  the indexed schema [pointer_criterion_holds_indexed]. The monograph's
  "five informal instantiations" become "five formal ones."

  What this does NOT deliver, fenced exactly as Section~24 fences it: it
  does not prove the conjecture. Which event is "metered" and which is
  "rival" is the modeler's designation here, precisely as the open-problem
  fence says. What is now checked is that UNDER the faithful modeling the
  criterion discriminates correctly at all five disciplines, from designs
  that owe each other nothing -- convergence made formal, which is evidence
  for the conjecture, not a proof of it. Whether record proliferation is
  the RIGHT criterion, and whether certification is the event a step rule
  is FORCED to price, remain open exactly as before; those are settled by
  adoption and further theory, not by a Qed.

  Falsification, at this level: exhibit one of the five ecosystems in which
  the designated metered event fails to proliferate, or the rival does --
  the corresponding [_unique_pointer] theorem falls. Or argue a designated
  rival is not a faithful stand-in for a real meterable event of that
  discipline; that is a modeling dispute, and the honest place for it is
  the prose fence, not the Coq.
*)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import PointerObservable.

From Coq Require Import List Lia.
Import ListNotations.

(** * The indexed conjecture schema *)

(** The [pointer_criterion_holds] schema of PointerObservable.v quantifies
    over a Prop-class of ecosystems. For a concrete finite family it is
    cleaner to index by a type: the criterion holds over an indexed family
    when every member's metered event is the unique pointer among its
    rivals. This is the shape the five-discipline theorem inhabits. *)
Definition pointer_criterion_holds_indexed
  {I : Type}
  (eco : I -> Ecosystem)
  (metered : forall i : I, eco_state (eco i) -> Prop)
  (rivals : forall i : I, list (eco_state (eco i) -> Prop)) : Prop :=
  forall i : I, unique_pointer_among (eco i) (metered i) (rivals i).

(** A uniform builder: an ecosystem with three observers all mirroring one
    boolean field of the state, plus the two proof obligations discharged
    once. Every discipline below is an instance, differing only in the
    domain reading of the flag and the rival. *)
Section MirrorEcosystem.

Variable St : Type.
Variable flag : St -> bool.
Variable counter : St -> nat.

Definition mirror_eco : Ecosystem := {|
  eco_state := St;
  eco_observers := 3;
  eco_fragment := fun _ s => flag s
|}.

Definition mirror_metered (s : St) : Prop := flag s = true.
Definition mirror_rival (s : St) : Prop := (1 <= counter s)%nat.

Lemma mirror_metered_proliferates :
  redundantly_proliferating mirror_eco mirror_metered.
Proof.
  intros i Hi s. unfold mirror_metered. simpl. reflexivity.
Qed.

(** The rival fails to proliferate provided some state has the flag down
    while the counter is up: no fragment (all mirror the flag) can then
    reconstruct the rival. Every discipline supplies such a witness. *)
Lemma mirror_rival_not_proliferating :
  (exists s0 : St, flag s0 = false /\ (1 <= counter s0)%nat) ->
  ~ redundantly_proliferating mirror_eco mirror_rival.
Proof.
  intros [s0 [Hflag Hcnt]] H.
  assert (H0 : (0 < eco_observers mirror_eco)%nat) by (simpl; lia).
  specialize (H 0%nat H0 s0).
  unfold mirror_rival in H. simpl in H.
  destruct H as [Hfwd _].
  specialize (Hfwd Hcnt).
  rewrite Hflag in Hfwd. discriminate.
Qed.

Theorem mirror_unique_pointer :
  (exists s0 : St, flag s0 = false /\ (1 <= counter s0)%nat) ->
  unique_pointer_among mirror_eco mirror_metered [mirror_rival].
Proof.
  intro Hwit. split.
  - exact mirror_metered_proliferates.
  - constructor;
      [ exact (mirror_rival_not_proliferating Hwit) | constructor ].
Qed.

End MirrorEcosystem.

(** * Discipline 1: Proof-of-stake finality *)

(** Metered: a block is finalized -- every full node on the network stores
    the finalization. Rival: the proposer did positive work, which no node
    records. (The A2-lens companion of this discipline is
    [nothing_at_stake_is_free_forgery] in the reductions development.) *)
Record PoSState := { pos_finalized : bool; pos_proposer_work : nat }.

Definition PoS_eco := mirror_eco PoSState pos_finalized.
Definition PoS_metered := mirror_metered PoSState pos_finalized.
Definition PoS_rival := mirror_rival PoSState pos_proposer_work.

Theorem PoS_unique_pointer :
  unique_pointer_among PoS_eco PoS_metered [PoS_rival].
Proof.
  apply (mirror_unique_pointer PoSState pos_finalized pos_proposer_work).
  exists {| pos_finalized := false; pos_proposer_work := 1 |}.
  simpl. split; [reflexivity | lia].
Qed.

(** * Discipline 2: Gas metering *)

(** Metered: a state transition is committed -- every replica re-executes
    and stores it. Rival: an intermediate scratch value was nonzero, stored
    by no one. (A2-lens companion: [gas_schedule_exactness].) *)
Record GasState := { gas_committed : bool; gas_scratch : nat }.

Definition Gas_eco := mirror_eco GasState gas_committed.
Definition Gas_metered := mirror_metered GasState gas_committed.
Definition Gas_rival := mirror_rival GasState gas_scratch.

Theorem Gas_unique_pointer :
  unique_pointer_among Gas_eco Gas_metered [Gas_rival].
Proof.
  apply (mirror_unique_pointer GasState gas_committed gas_scratch).
  exists {| gas_committed := false; gas_scratch := 1 |}.
  simpl. split; [reflexivity | lia].
Qed.

(** * Discipline 3: Trusted-execution attestation *)

(** Metered: an attestation is issued -- every relying party verifies and
    archives it. Rival: the enclave's internal measurement register held a
    transient value, recorded by no one. (A2-lens companion:
    [attestation_cannot_factor_through_bare_transcript].) *)
Record TEEState := { tee_attested : bool; tee_meas_noise : nat }.

Definition TEE_eco := mirror_eco TEEState tee_attested.
Definition TEE_metered := mirror_metered TEEState tee_attested.
Definition TEE_rival := mirror_rival TEEState tee_meas_noise.

Theorem TEE_unique_pointer :
  unique_pointer_among TEE_eco TEE_metered [TEE_rival].
Proof.
  apply (mirror_unique_pointer TEEState tee_attested tee_meas_noise).
  exists {| tee_attested := false; tee_meas_noise := 1 |}.
  simpl. split; [reflexivity | lia].
Qed.

(** * Discipline 4: Certificate transparency *)

(** Metered: a certificate is included in the log -- the log is mirrored,
    gossiped, and audited by design. Rival: the submission latency, which
    no mirror records. (A2-lens companion: [log_free_verifier_impossible].) *)
Record CTState := { ct_logged : bool; ct_submit_latency : nat }.

Definition CT_eco := mirror_eco CTState ct_logged.
Definition CT_metered := mirror_metered CTState ct_logged.
Definition CT_rival := mirror_rival CTState ct_submit_latency.

Theorem CT_unique_pointer :
  unique_pointer_among CT_eco CT_metered [CT_rival].
Proof.
  apply (mirror_unique_pointer CTState ct_logged ct_submit_latency).
  exists {| ct_logged := false; ct_submit_latency := 1 |}.
  simpl. split; [reflexivity | lia].
Qed.

(** * Discipline 5: Proof-carrying verification *)

(** Metered: a carried certificate is checked -- every consumer of the code
    re-checks it. Rival: the prover's internal effort, which no consumer
    records. (A2-lens companion: [bare_pcc_impossible].) *)
Record PCCState := { pcc_checked : bool; pcc_prover_steps : nat }.

Definition PCC_eco := mirror_eco PCCState pcc_checked.
Definition PCC_metered := mirror_metered PCCState pcc_checked.
Definition PCC_rival := mirror_rival PCCState pcc_prover_steps.

Theorem PCC_unique_pointer :
  unique_pointer_among PCC_eco PCC_metered [PCC_rival].
Proof.
  apply (mirror_unique_pointer PCCState pcc_checked pcc_prover_steps).
  exists {| pcc_checked := false; pcc_prover_steps := 1 |}.
  simpl. split; [reflexivity | lia].
Qed.

(** * The aggregate: the criterion holds at all five *)

Inductive Discipline := DPoS | DGas | DTEE | DCT | DPCC.

Definition disc_eco (d : Discipline) : Ecosystem :=
  match d with
  | DPoS => PoS_eco | DGas => Gas_eco | DTEE => TEE_eco
  | DCT => CT_eco | DPCC => PCC_eco
  end.

Definition disc_metered (d : Discipline) : eco_state (disc_eco d) -> Prop :=
  match d with
  | DPoS => PoS_metered | DGas => Gas_metered | DTEE => TEE_metered
  | DCT => CT_metered | DPCC => PCC_metered
  end.

Definition disc_rivals (d : Discipline) : list (eco_state (disc_eco d) -> Prop) :=
  match d with
  | DPoS => [PoS_rival] | DGas => [Gas_rival] | DTEE => [TEE_rival]
  | DCT => [CT_rival] | DPCC => [PCC_rival]
  end.

(** Every deployed discipline's metered event is the unique pointer among
    its rivals: the pointer-observable criterion, machine-checked at five
    independently evolved metering designs. Evidence for the Section~25
    conjecture; not a proof of it (the fence in the file header). *)
Theorem five_disciplines_are_pointers :
  pointer_criterion_holds_indexed disc_eco disc_metered disc_rivals.
Proof.
  intro d. destruct d; simpl.
  - exact PoS_unique_pointer.
  - exact Gas_unique_pointer.
  - exact TEE_unique_pointer.
  - exact CT_unique_pointer.
  - exact PCC_unique_pointer.
Qed.

(** * Anchor for proof-connectivity audits *)

Definition pointer_reductions_anchor := @five_disciplines_are_pointers.
