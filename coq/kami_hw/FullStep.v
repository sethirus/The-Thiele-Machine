(** FullStep.v

    Exact full-state step/run semantics over [KamiSnapshotFull].

    This file lifts the richer full-state snapshot from [FullAbstraction.v] to
    a full-state local step model.  The model is intentionally stated at the
    snapshot/abstraction boundary:

      kami_step_full : KamiSnapshotFull -> vm_instruction -> KamiSnapshotFull
      kami_run_full  : nat -> list vm_instruction -> KamiSnapshotFull -> KamiSnapshotFull

    and is connected to the kernel semantics by exact abstraction theorems:

      abs_full_snapshot (kami_step_full ks i) = vm_apply (abs_full_snapshot ks) i
      abs_full_snapshot (kami_run_full fuel tr ks) = run_vm fuel tr (abs_full_snapshot ks)

    This is stronger than the legacy projected [abs_phase1]/[kami_step] story:
    no VM fields are dropped.  It is also deliberately honest about scope: this
    file proves a full-state local snapshot model, not yet that the existing
    lower-level hardware-oriented [kami_step] implementation computes the same
    thing instruction by instruction.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof MuLedgerConservation.
From KamiHW Require Import FullAbstraction.

Import VMStep.VMStep.

Definition kami_step_full
  (ks : KamiSnapshotFull) (i : vm_instruction) : KamiSnapshotFull :=
  full_snapshot_repr (vm_apply (abs_full_snapshot ks) i).

Theorem kami_step_full_refines :
  forall ks i,
    abs_full_snapshot (kami_step_full ks i) =
    vm_apply (abs_full_snapshot ks) i.
Proof.
  intros ks i. unfold kami_step_full.
  apply abs_full_snapshot_repr.
Qed.

Fixpoint kami_run_full
  (fuel : nat) (trace : list vm_instruction) (ks : KamiSnapshotFull)
  : KamiSnapshotFull :=
  match fuel with
  | 0 => ks
  | S fuel' =>
      match nth_error trace ks.(full_snap_pc) with
      | Some instr => kami_run_full fuel' trace (kami_step_full ks instr)
      | None => ks
      end
  end.

Theorem kami_run_full_refines :
  forall fuel trace ks,
    abs_full_snapshot (kami_run_full fuel trace ks) =
    run_vm fuel trace (abs_full_snapshot ks).
Proof.
  induction fuel as [|fuel IH]; intros trace ks; simpl.
  - reflexivity.
  - destruct (nth_error trace (full_snap_pc ks)) as [instr|] eqn:Hnth; simpl.
    + rewrite IH. rewrite kami_step_full_refines. reflexivity.
    + reflexivity.
Qed.

Definition full_kami_states_correspond (ks : KamiSnapshotFull) (vs : VMState) : Prop :=
  abs_full_snapshot ks = vs.

Theorem initial_full_kami_correspondence :
  forall s, full_kami_states_correspond (full_snapshot_repr s) s.
Proof.
  intro s. unfold full_kami_states_correspond.
  apply abs_full_snapshot_repr.
Qed.
