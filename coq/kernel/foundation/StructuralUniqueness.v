(** StructuralUniqueness: the uniqueness conjectures of [StructuralCore]
    and [StructuralCoreRound2] are false.

    The counterexample is a machine that bills CPU time. [BilledCore] runs
    the Thiele core and carries a step counter, and its ledger is the Thiele
    ledger plus the counter. So every step costs one unit more than the same
    step of the Thiele core.

    - It is adequate in the weak sense ([billed_core_adequate]). A2 is a
      lower bound, and a surcharge only raises the price.
    - It is an honest VM extension in the strong sense
      ([billed_core_honest_extension]). Dropping the counter is a cover:
      it commutes with the step, keeps halting, and hits every starting
      state of the Thiele core.
    - Its core is not equivalent to the Thiele core in either sense
      ([billed_core_not_equiv], [billed_core_not_equiv_round2]). A Thiele
      state with an empty program never moves and prices every step at
      zero. Any state related to it must price its next step the same, and
      every step of [BilledCore] costs at least one.

    What fails is the pricing half of adequacy. Both forms ask for a floor
    (A2) and neither forbids overcharging, so a machine that charges for
    something besides certification is adequate and not the same.
    [StructuralCoreRound3] states uniqueness up to the price schedule. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedLedger.
From Kernel Require Import MuInitiality.
From Kernel Require Import StructuralCore StructuralCoreRound2.

(** * The CPU-billed Thiele core *)

Definition BilledCore : RCM := {|
  rc_state := list vm_instruction * VMState * nat;
  rc_next := fun x => let '(p, s, k) := x in (p, run_vm_u 1 p s, S k);
  rc_init := fun _ => True;
  rc_cert := fun x => let '(_, s, _) := x in s.(vm_certified);
  rc_mu := fun x => let '(_, s, k) := x in s.(vm_mu) + k;
  rc_halted := fun x => let '(p, s, _) := x in
    s.(vm_pc) = length p /\ read_reg s 9 = 1
|}.

Lemma billed_run : forall n p s k,
  rc_run BilledCore n (p, s, k) = (p, run_vm_u n p s, n + k).
Proof.
  induction n; intros p s k; [reflexivity |].
  unfold rc_run in *. rewrite Nat.iter_succ_r.
  replace (rc_next BilledCore (p, s, k)) with (p, run_vm_u 1 p s, S k)
    by reflexivity.
  rewrite IHn, (run_vm_u_succ n p s), Nat.add_succ_r. reflexivity.
Qed.

(** Every step costs the Thiele price plus one. *)
Lemma billed_step_cost : forall p s k,
  step_cost BilledCore (p, s, k) = step_cost ThieleCore (p, s) + 1.
Proof.
  intros p s k. unfold step_cost.
  change (vm_mu (run_vm_u 1 p s) + S k - (vm_mu s + k) =
          vm_mu (run_vm_u 1 p s) - vm_mu s + 1).
  rewrite thiele_step_mu. lia.
Qed.

Lemma billed_step_cost_pos : forall x, step_cost BilledCore x >= 1.
Proof. intros [[p s] k]. rewrite billed_step_cost. lia. Qed.

(** * The billed core is adequate *)

Theorem billed_core_ledger : ledger_carried BilledCore.
Proof.
  intros [[p s] k].
  change (vm_mu s + k <= vm_mu (run_vm_u 1 p s) + S k).
  rewrite thiele_step_mu. lia.
Qed.

Theorem billed_core_a2 : rc_a2 BilledCore.
Proof. intros x _ _. apply billed_step_cost_pos. Qed.

Theorem billed_core_carries_record : carries_record BilledCore.
Proof.
  exists ([instr_certify 0], init_state, 0), 1. split; [exact I |].
  reflexivity.
Qed.

Theorem billed_core_halting_problem_coverage :
  halting_problem_coverage BilledCore.
Proof.
  intro P.
  destruct (thiele_core_halting_problem_coverage P) as [[p s] [_ Hiff]].
  exists (p, s, 0). split; [exact I |].
  rewrite Hiff.
  split; intros [n Hn]; exists n.
  - rewrite thiele_core_run in Hn. rewrite billed_run. exact Hn.
  - rewrite billed_run in Hn. rewrite thiele_core_run. exact Hn.
Qed.

Theorem billed_core_adequate : Adequate BilledCore.
Proof.
  split; [exact billed_core_ledger |].
  split; [exact billed_core_a2 |].
  split; [exact billed_core_carries_record |
          exact billed_core_halting_problem_coverage].
Qed.

(** * The Thiele core has a state that never pays *)

(** A state whose program is empty never moves and prices each step at
    zero. *)
Lemma empty_program_stuck : forall s, run_vm_u 1 [] s = s.
Proof.
  intro s. apply run_vm_u_stopped. destruct (vm_pc s); reflexivity.
Qed.

Lemma empty_program_free : forall s, step_cost ThieleCore ([], s) = 0.
Proof.
  intro s. unfold step_cost.
  change (vm_mu (run_vm_u 1 [] s) - vm_mu s = 0).
  rewrite empty_program_stuck. lia.
Qed.

(** * The weak form is false *)

Theorem billed_core_not_equiv : ~ core_equiv BilledCore ThieleCore.
Proof.
  intros [R [_ [Hback Hstep]]].
  destruct (Hback ([], init_state) I) as [m [_ Hr]].
  destruct (Hstep m ([], init_state) Hr) as [_ [Hcost _]].
  pose proof (billed_step_cost_pos m) as Hpos.
  rewrite Hcost, empty_program_free in Hpos. lia.
Qed.

Theorem uniqueness_round1_refuted : ~ uniqueness_round1.
Proof.
  intro H. exact (billed_core_not_equiv (H BilledCore billed_core_adequate)).
Qed.

(** * The billed core is an honest VM extension *)

(** Dropping the counter. *)
Definition billed_cover_state (x : list vm_instruction * VMState * nat)
  : list vm_instruction * VMState :=
  let '(p, s, _) := x in (p, s).

Definition billed_cover : ComputationalCover BilledCore ThieleCore.
Proof.
  refine (Build_ComputationalCover BilledCore ThieleCore
            billed_cover_state _ _ _ _).
  - intros; exact I.
  - intros [p s] _. exists (p, s, 0). split; [exact I | reflexivity].
  - intros [[p s] k]. reflexivity.
  - intros [[p s] k]. simpl. tauto.
Defined.

Theorem billed_core_record_permanent : record_permanent BilledCore.
Proof.
  intros [[p s] k] H.
  change (vm_certified (run_vm_u 1 p s) = true).
  simpl. destruct (nth_error p (vm_pc s)) as [i |].
  - apply vm_apply_u_certified_permanent. exact H.
  - exact H.
Qed.

Theorem billed_core_reachable_record_write : reachable_record_write BilledCore.
Proof.
  exists ([instr_certify 0], init_state, 0), 0.
  split; [exact I |]. split; reflexivity.
Qed.

Theorem billed_core_honest_extension : HonestVMExtension BilledCore.
Proof.
  split; [exact (inhabits billed_cover) |].
  split; [exact billed_core_ledger |].
  split; [exact billed_core_a2 |].
  split; [exact billed_core_record_permanent |
          exact billed_core_reachable_record_write].
Qed.

(** * The strong form is false *)

Theorem billed_core_not_equiv_round2 :
  ~ core_equiv_round2 BilledCore ThieleCore.
Proof.
  intros [R [_ [Hback Hstep]]].
  destruct (Hback ([], init_state) I) as [m [_ Hr]].
  destruct (Hstep m ([], init_state) Hr) as [_ [_ [_ [Hcost _]]]].
  pose proof (billed_step_cost_pos m) as Hpos.
  rewrite Hcost, empty_program_free in Hpos. lia.
Qed.

Theorem uniqueness_round2_refuted : ~ uniqueness_round2.
Proof.
  intro H.
  exact (billed_core_not_equiv_round2 (H BilledCore billed_core_honest_extension)).
Qed.

Print Assumptions uniqueness_round1_refuted.
Print Assumptions uniqueness_round2_refuted.
