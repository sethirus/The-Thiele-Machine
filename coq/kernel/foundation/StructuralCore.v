(** StructuralCore: record-carrying machines, adequacy, and core equivalence.

    The monograph asks whether every adequate record-carrying machine has
    the same structural core as the Thiele Machine. That question needs
    three definitions: what a record-carrying machine is, when one is
    adequate, and when two cores are the same. This file gives them in their
    weak form. It proves only what the definitions need to be well posed:
    the Thiele core is itself adequate, and a machine that keeps its whole
    history is equivalent to the Thiele core, so retained history is
    quotiented out.

    - A record-carrying machine is a deterministic machine with a set of
      starting states, a yes/no record reading, a ledger carried in the
      state, and a halting observation.
    - It is adequate when the ledger never goes down, a step that switches
      the reading on raises the ledger by at least one (A2), some run from a
      starting state reaches a certified state (it carries a record at all),
      and every two-counter halting instance has some starting state whose
      observed halt agrees with that instance. This last clause is only
      existential halting-problem coverage. It supplies neither a uniform
      effective input encoding nor a reverse simulation, and is not a claim
      of Turing equivalence.
    - Two machines have equivalent cores when some relation between their
      states relates every starting state of each to a starting state of the
      other, and related states agree on the reading, price their next step
      the same, and step to related states. This is bisimulation
      up to the reading and the ledger's increments. The relation need not be
      a function, so extra state one machine keeps, such as its history, is
      quotiented out.
    - The Thiele core is the unbounded VM [vm_apply_u] with the program
      carried in the state, started from any program and any state. It
      halts when the program counter reaches the end of the program with
      register 9 equal to one, the two-counter interpreter's success
      convention.

    The conjecture stated here: every adequate machine has a core equivalent
    to the Thiele core. It is false; [StructuralUniqueness] gives the
    counterexample. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From Undecidability.MinskyMachines Require Import MM2.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedLedger.
From Kernel Require Import VMUnboundedCM2Interpreter VMUnboundedCM2Bridge.
From Kernel Require Import MuInitiality.

(** * Definitions *)

Record RCM : Type := {
  rc_state : Type;
  rc_next : rc_state -> rc_state;
  rc_init : rc_state -> Prop;
  rc_cert : rc_state -> bool;
  rc_mu : rc_state -> nat;
  rc_halted : rc_state -> Prop
}.

Definition rc_run (M : RCM) (n : nat) (s : rc_state M) : rc_state M :=
  Nat.iter n (rc_next M) s.

Definition step_cost (M : RCM) (s : rc_state M) : nat :=
  rc_mu M (rc_next M s) - rc_mu M s.

Definition ledger_carried (M : RCM) : Prop :=
  forall s, rc_mu M s <= rc_mu M (rc_next M s).

Definition rc_a2 (M : RCM) : Prop :=
  forall s, rc_cert M s = false -> rc_cert M (rc_next M s) = true -> step_cost M s >= 1.

Definition carries_record (M : RCM) : Prop :=
  exists s n, rc_init M s /\ rc_cert M (rc_run M n s) = true.

(** Weak, per-instance halting coverage. The existential start state may
    depend on the MM2 problem without being supplied by a uniform effective
    encoder; no simulation in either direction is part of this definition. *)
Definition halting_problem_coverage (M : RCM) : Prop :=
  forall P : MM2_PROBLEM,
    exists s0, rc_init M s0 /\ (MM2_HALTING P <-> exists n, rc_halted M (rc_run M n s0)).

Definition Adequate (M : RCM) : Prop :=
  ledger_carried M /\ rc_a2 M /\ carries_record M /\ halting_problem_coverage M.

Definition core_bisim (M N : RCM) (R : rc_state M -> rc_state N -> Prop) : Prop :=
  (forall m, rc_init M m -> exists n, rc_init N n /\ R m n) /\
  (forall n, rc_init N n -> exists m, rc_init M m /\ R m n) /\
  (forall m n, R m n ->
     rc_cert M m = rc_cert N n /\
     step_cost M m = step_cost N n /\
     R (rc_next M m) (rc_next N n)).

Definition core_equiv (M N : RCM) : Prop := exists R, core_bisim M N R.

(** * The Thiele core *)

Definition thiele_next (ps : list vm_instruction * VMState) : list vm_instruction * VMState :=
  (fst ps, run_vm_u 1 (fst ps) (snd ps)).

Definition ThieleCore : RCM := {|
  rc_state := list vm_instruction * VMState;
  rc_next := thiele_next;
  rc_init := fun _ => True;
  rc_cert := fun ps => (snd ps).(vm_certified);
  rc_mu := fun ps => (snd ps).(vm_mu);
  rc_halted := fun ps =>
    (snd ps).(vm_pc) = length (fst ps) /\ read_reg (snd ps) 9 = 1
|}.

(** The uniqueness conjecture, weak form. *)
Definition uniqueness_round1 : Prop :=
  forall M, Adequate M -> core_equiv M ThieleCore.

(** * The definitions are well posed: the Thiele core is adequate *)

Lemma run_vm_u_stopped : forall n p s,
  nth_error p s.(vm_pc) = None -> run_vm_u n p s = s.
Proof.
  induction n; intros p s H; simpl; [reflexivity |]. rewrite H. reflexivity.
Qed.

Lemma run_vm_u_succ : forall n p s,
  run_vm_u (S n) p s = run_vm_u n p (run_vm_u 1 p s).
Proof.
  intros n p s. simpl. destruct (nth_error p (vm_pc s)) eqn:H; [reflexivity |].
  symmetry. apply run_vm_u_stopped. exact H.
Qed.

Lemma thiele_core_run : forall n p s, rc_run ThieleCore n (p, s) = (p, run_vm_u n p s).
Proof.
  induction n; intros p s; [reflexivity |].
  unfold rc_run in *. rewrite Nat.iter_succ_r.
  replace (rc_next ThieleCore (p, s)) with (p, run_vm_u 1 p s) by reflexivity.
  rewrite IHn, (run_vm_u_succ n p s). reflexivity.
Qed.

Lemma thiele_step_mu : forall p s,
  vm_mu (run_vm_u 1 p s) =
  vm_mu s + match nth_error p s.(vm_pc) with Some i => instruction_cost i | None => 0 end.
Proof.
  intros p s. simpl. destruct (nth_error p (vm_pc s)); [apply vm_apply_u_mu | lia].
Qed.

Theorem thiele_core_ledger : ledger_carried ThieleCore.
Proof.
  intros [p s]. change (vm_mu s <= vm_mu (run_vm_u 1 p s)).
  rewrite thiele_step_mu. lia.
Qed.

Theorem thiele_core_a2 : rc_a2 ThieleCore.
Proof.
  intros [p s]. unfold step_cost.
  change (vm_certified s = false -> vm_certified (run_vm_u 1 p s) = true ->
          vm_mu (run_vm_u 1 p s) - vm_mu s >= 1).
  intros H0 H1. rewrite thiele_step_mu.
  simpl in H1. destruct (nth_error p (vm_pc s)) as [i |] eqn:Hf.
  - pose proof (vm_apply_u_no_free_certification s i H0 H1). lia.
  - congruence.
Qed.

Theorem thiele_core_carries_record : carries_record ThieleCore.
Proof.
  exists ([instr_certify 0], init_state), 1. split; [exact I |].
  reflexivity.
Qed.

Theorem thiele_core_halting_problem_coverage : halting_problem_coverage ThieleCore.
Proof.
  intro P. exists (cm2_interpreter_program, mm2_host_input init_state P).
  split; [exact I |].
  rewrite mm2_halting_host_iff. unfold cm2_host_halts, cm2_halted.
  split; intros [n Hn]; exists n; rewrite ?thiele_core_run in *; exact Hn.
Qed.

Theorem thiele_core_adequate : Adequate ThieleCore.
Proof.
  split; [exact thiele_core_ledger |].
  split; [exact thiele_core_a2 |].
  split; [exact thiele_core_carries_record | exact thiele_core_halting_problem_coverage].
Qed.

(** * Retained history is quotiented out *)

(** The Thiele core with every state it has passed through kept alongside.
    This is the autonomous counterpart of the history-keeping target in
    [certification_agreement_does_not_imply_descent]: it agrees with the VM
    on every reading and every charge and remembers more. *)
Definition HistoryCore : RCM := {|
  rc_state := list vm_instruction * VMState * list VMState;
  rc_next := fun x => let '(p, s, h) := x in (p, run_vm_u 1 p s, s :: h);
  rc_init := fun x => let '(_, _, h) := x in h = [];
  rc_cert := fun x => let '(_, s, _) := x in s.(vm_certified);
  rc_mu := fun x => let '(_, s, _) := x in s.(vm_mu);
  rc_halted := fun x => let '(p, s, _) := x in
    s.(vm_pc) = length p /\ read_reg s 9 = 1
|}.

Theorem history_core_equiv_thiele : core_equiv HistoryCore ThieleCore.
Proof.
  exists (fun x ps => let '(p, s, _) := x in ps = (p, s)).
  split; [| split].
  - intros [[p s] h] _. exists (p, s). split; [exact I | reflexivity].
  - intros [p s] _. exists (p, s, []). split; reflexivity.
  - intros [[p s] h] ps Hr. subst ps.
    split; [reflexivity |]. split; reflexivity.
Qed.
