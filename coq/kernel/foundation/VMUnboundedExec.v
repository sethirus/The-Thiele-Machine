(** VMUnboundedExec.v — unbounded relational execution for the 47/51-opcode VM.

    Why this file exists. The VM [Substrate] instance (VMSubstrateInstance.v)
    uses BOUNDED execution: [vm_run p s = Some (run_vm vm_run_fuel p s)] with a
    fixed fuel. A fixed fuel budget structurally blocks any self-interpreting
    fixed point: a universal interpreter consumes unboundedly more steps than the
    program it simulates, so no bounded-fuel program can act as its own diagonal
    for a non-trivial decider. The honest discharge of the VM's Kleene recursion
    theorem (the one premise left open in
    VMSubstrateEncoded.vm_structural_shortcut_undecidable_encoded) therefore
    needs an UNBOUNDED execution model.

    This file is the foundation of that model. It defines unbounded halting
    relationally on top of [run_vm], and proves the load-bearing facts the later
    universal-interpreter and recursion-theorem layers consume:

      - [vm_halts_at p s r]  : from s, program p reaches the halted state r;
      - determinism          : a program halts at most one state from a start;
      - halt-saturation      : past the halting fuel, more fuel changes nothing;
      - the empty program is the no-op that halts immediately.

    Everything here is closed under the global context: no admits, no axioms.
    It reuses the halt-stability lemmas already proved in DagRestriction.v. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import DagRestriction.

(** [halted p s]: the program counter has run off the end of the program, so
    [run_vm] takes no further step. This is exactly the [None] branch of
    [nth_error p (vm_pc s)]. *)
Definition halted (p : list vm_instruction) (s : VMState) : Prop :=
  length p <= vm_pc s.

Lemma halted_iff_nth_error_none :
  forall p s, halted p s <-> nth_error p (vm_pc s) = None.
Proof.
  intros p s. unfold halted. split.
  - intro H. apply nth_error_None. exact H.
  - intro H. apply nth_error_None. exact H.
Qed.

(** [vm_halts_at p s r]: there is a fuel budget after which p, run from s, sits
    in the halted state r. Unbounded: the budget is existentially quantified. *)
Definition vm_halts_at (p : list vm_instruction) (s r : VMState) : Prop :=
  exists n, run_vm n p s = r /\ halted p r.

(** A run_vm snapshot that has halted is a halt witness for its own result. *)
Lemma run_vm_halt_witness :
  forall n p s, halted p (run_vm n p s) -> vm_halts_at p s (run_vm n p s).
Proof. intros n p s H. exists n. split; [reflexivity | exact H]. Qed.

(** Determinism — the heart of treating [vm_halts_at] as a partial function.
    If p halts at both r1 and r2 from s, the larger fuel run equals the smaller
    by halt-saturation, so r1 = r2. *)
Lemma vm_halts_at_deterministic :
  forall p s r1 r2, vm_halts_at p s r1 -> vm_halts_at p s r2 -> r1 = r2.
Proof.
  intros p s r1 r2 [n1 [Hr1 Hh1]] [n2 [Hr2 Hh2]].
  destruct (Nat.le_ge_cases n1 n2) as [Hle | Hge].
  - assert (H1 : length p <= (run_vm n1 p s).(vm_pc))
      by (rewrite Hr1; exact Hh1).
    replace n2 with (n1 + (n2 - n1)) in Hr2 by lia.
    rewrite (run_vm_halted_stable n1 (n2 - n1) p s H1) in Hr2.
    rewrite Hr1 in Hr2. exact Hr2.
  - assert (H2 : length p <= (run_vm n2 p s).(vm_pc))
      by (rewrite Hr2; exact Hh2).
    replace n1 with (n2 + (n1 - n2)) in Hr1 by lia.
    rewrite (run_vm_halted_stable n2 (n1 - n2) p s H2) in Hr1.
    rewrite Hr2 in Hr1. symmetry; exact Hr1.
Qed.

(** Saturation: once p halts at r from s with fuel n, every larger fuel gives r. *)
Lemma vm_halts_at_saturates :
  forall p s r n k,
    run_vm n p s = r -> halted p r ->
    run_vm (n + k) p s = r.
Proof.
  intros p s r n k Hr Hh.
  assert (H1 : length p <= (run_vm n p s).(vm_pc)) by (rewrite Hr; exact Hh).
  rewrite (run_vm_halted_stable n k p s H1). exact Hr.
Qed.

(** The empty program is the no-op: it halts immediately, leaving the state
    unchanged. This is [no_program] for the unbounded substrate. *)
Lemma vm_halts_at_nil : forall s, vm_halts_at (@nil vm_instruction) s s.
Proof.
  intro s. exists 0. split.
  - reflexivity.
  - unfold halted. simpl. apply Nat.le_0_l.
Qed.

(** Two programs are unbounded-equivalent when they halt at the same states from
    every start (and diverge together). This is the genuine extensional
    equivalence the recursion theorem will be stated against — fuel-free, unlike
    the bounded [prog_equiv] of the VM Substrate instance. *)
Definition vm_equiv (p q : list vm_instruction) : Prop :=
  forall s r, vm_halts_at p s r <-> vm_halts_at q s r.

Lemma vm_equiv_refl : forall p, vm_equiv p p.
Proof. intros p s r. split; intro H; exact H. Qed.

Lemma vm_equiv_sym : forall p q, vm_equiv p q -> vm_equiv q p.
Proof.
  intros p q H s r. split; intro K.
  - apply (proj2 (H s r)). exact K.
  - apply (proj1 (H s r)). exact K.
Qed.

Lemma vm_equiv_trans :
  forall p q t, vm_equiv p q -> vm_equiv q t -> vm_equiv p t.
Proof.
  intros p q t Hpq Hqt s r. split; intro H.
  - apply (proj1 (Hqt s r)). apply (proj1 (Hpq s r)). exact H.
  - apply (proj2 (Hpq s r)). apply (proj2 (Hqt s r)). exact H.
Qed.
