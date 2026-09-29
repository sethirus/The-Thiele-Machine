(** StructuralScheduleUniqueness: uniqueness up to the price schedule, both
    strengths of [StructuralCoreRound3].

    - With the record fixed to the certification reading, uniqueness holds
      ([uniqueness_round3b_holds]). Each state is related to the Thiele state
      its cover assigns. The CPU-billed machine of [StructuralUniqueness] is
      an instance ([billed_core_honest3b]) and is the same machine modulo its
      schedule ([billed_core_equiv_mod_schedule]). So is the Thiele core
      with any surcharge that depends on the current state, per step, per
      instruction, or per millisecond ([surcharged_core_equiv_mod_schedule]).
    - With the record only required to be some reading of the computation,
      uniqueness fails ([uniqueness_round3a_refuted]). [MeterCore] is the
      Thiele core whose record is "the meter has passed one." That reading
      is permanent, a paid step writes it, and A2 holds for it, but at a
      state with a positive meter and no certificate the two lights
      disagree, and the cover pins that state.

    So the structure and the schedule are not the whole story. Which
    permanent reading counts as the record is a second free choice. That
    choice is the pointer-observable question: what makes certification the
    event to record. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedLedger.
From Kernel Require Import MuInitiality.
From Kernel Require Import StructuralCore StructuralCoreRound2 StructuralCoreRound3.
From Kernel Require Import StructuralUniqueness.

(** * The certification strength holds *)

Theorem thiele_core_priced : priced ThieleCore.
Proof. split; [exact thiele_core_ledger | exact thiele_core_a2]. Qed.

Theorem uniqueness_round3b_holds : uniqueness_round3b.
Proof.
  intros M C [Hrec [Hpriced _]].
  split; [exact Hpriced |]. split; [exact thiele_core_priced |].
  exists (fun m t => cover_state M ThieleCore C m = t).
  split; [intros m t H; exact H |].
  split.
  - intros m Hm. exists (cover_state M ThieleCore C m).
    split; [exact (cover_initial M ThieleCore C m Hm) | reflexivity].
  - split.
    + intros t Ht.
      destruct (cover_surjective_initial M ThieleCore C t Ht) as [m [Hm Heq]].
      exists m. split; assumption.
    + intros m t Hmt. subst t.
      split; [apply Hrec |].
      split; [apply (cover_halted M ThieleCore C) |].
      apply (cover_step M ThieleCore C).
Qed.

(** The CPU-billed machine is an instance, and the same machine modulo its
    schedule. *)
Theorem billed_core_honest3b : HonestExtension3b BilledCore billed_cover.
Proof.
  split; [intros [[p s] k]; reflexivity |].
  split; [split; [exact billed_core_ledger | exact billed_core_a2] |].
  split; [exact billed_core_record_permanent |
          exact billed_core_reachable_record_write].
Qed.

Theorem billed_core_equiv_mod_schedule :
  equiv_mod_schedule_via BilledCore billed_cover.
Proof. exact (uniqueness_round3b_holds BilledCore billed_cover billed_core_honest3b). Qed.

(** Any time-based bill is a schedule. [SurchargedCore extra] runs the
    Thiele core and adds [extra] of the current state to its ledger at each
    step, so a step's price is the Thiele price plus any surcharge at all:
    per step, per instruction, per millisecond. Every such machine is an
    instance, and the same machine modulo its schedule. *)
Definition SurchargedCore (extra : list vm_instruction * VMState -> nat) : RCM := {|
  rc_state := list vm_instruction * VMState * nat;
  rc_next := fun x => let '(p, s, a) := x in (p, run_vm_u 1 p s, a + extra (p, s));
  rc_init := fun _ => True;
  rc_cert := fun x => let '(_, s, _) := x in s.(vm_certified);
  rc_mu := fun x => let '(_, s, a) := x in s.(vm_mu) + a;
  rc_halted := fun x => let '(p, s, _) := x in
    s.(vm_pc) = length p /\ read_reg s 9 = 1
|}.

Definition surcharged_cover_state (x : list vm_instruction * VMState * nat)
  : list vm_instruction * VMState :=
  let '(p, s, _) := x in (p, s).

Definition surcharged_cover (extra : list vm_instruction * VMState -> nat)
  : ComputationalCover (SurchargedCore extra) ThieleCore.
Proof.
  refine (Build_ComputationalCover (SurchargedCore extra) ThieleCore
            surcharged_cover_state _ _ _ _).
  - intros; exact I.
  - intros [p s] _. exists (p, s, 0). split; [exact I | reflexivity].
  - intros [[p s] a]. reflexivity.
  - intros [[p s] a]. simpl. tauto.
Defined.

Theorem surcharged_core_honest3b : forall extra,
  HonestExtension3b (SurchargedCore extra) (surcharged_cover extra).
Proof.
  intro extra.
  split; [intros [[p s] a]; reflexivity |].
  split; [split |].
  - intros [[p s] a].
    change (vm_mu s + a <= vm_mu (run_vm_u 1 p s) + (a + extra (p, s))).
    rewrite thiele_step_mu. lia.
  - intros [[p s] a] H0 H1. unfold step_cost.
    change (vm_certified s = false) in H0.
    change (vm_certified (run_vm_u 1 p s) = true) in H1.
    change (vm_mu (run_vm_u 1 p s) + (a + extra (p, s)) - (vm_mu s + a) >= 1).
    pose proof (thiele_core_a2 (p, s) H0 H1) as Ha2. unfold step_cost in Ha2.
    change (vm_mu (run_vm_u 1 p s) - vm_mu s >= 1) in Ha2. lia.
  - split.
    + intros [[p s] a] H.
      change (vm_certified s = true) in H.
      change (vm_certified (run_vm_u 1 p s) = true).
      simpl. destruct (nth_error p (vm_pc s)) as [i |].
      * apply vm_apply_u_certified_permanent. exact H.
      * exact H.
    + exists ([instr_certify 0], init_state, 0), 0.
      split; [exact I |]. split; reflexivity.
Qed.

Theorem surcharged_core_equiv_mod_schedule : forall extra,
  equiv_mod_schedule_via (SurchargedCore extra) (surcharged_cover extra).
Proof.
  intro extra.
  exact (uniqueness_round3b_holds _ _ (surcharged_core_honest3b extra)).
Qed.

(** * The computation-reading strength fails *)

(** The Thiele core whose record is "the meter has passed one." *)
Definition MeterCore : RCM := {|
  rc_state := list vm_instruction * VMState;
  rc_next := thiele_next;
  rc_init := fun _ => True;
  rc_cert := fun ps => Nat.leb 1 (snd ps).(vm_mu);
  rc_mu := fun ps => (snd ps).(vm_mu);
  rc_halted := fun ps =>
    (snd ps).(vm_pc) = length (fst ps) /\ read_reg (snd ps) 9 = 1
|}.

Definition meter_cover : ComputationalCover MeterCore ThieleCore.
Proof.
  refine (Build_ComputationalCover MeterCore ThieleCore (fun x => x) _ _ _ _).
  - intros; exact I.
  - intros t _. exists t. split; [exact I | reflexivity].
  - intros x. reflexivity.
  - intros x. simpl. tauto.
Defined.

Lemma meter_step_mu : forall p s, vm_mu s <= vm_mu (run_vm_u 1 p s).
Proof. intros p s. rewrite thiele_step_mu. lia. Qed.

Theorem meter_core_honest3a : HonestExtension3a MeterCore meter_cover.
Proof.
  split; [exists (fun t => Nat.leb 1 (snd t).(vm_mu)); intro m; reflexivity |].
  split.
  - split.
    + intros [p s]. exact (meter_step_mu p s).
    + intros [p s] H0 H1. unfold step_cost.
      change (Nat.leb 1 (vm_mu s) = false) in H0.
      change (Nat.leb 1 (vm_mu (run_vm_u 1 p s)) = true) in H1.
      change (vm_mu (run_vm_u 1 p s) - vm_mu s >= 1).
      apply Nat.leb_gt in H0. apply Nat.leb_le in H1. lia.
  - split.
    + intros [p s] H.
      change (Nat.leb 1 (vm_mu s) = true) in H.
      change (Nat.leb 1 (vm_mu (run_vm_u 1 p s)) = true).
      apply Nat.leb_le in H. apply Nat.leb_le.
      pose proof (meter_step_mu p s). lia.
    + exists ([instr_certify 0], init_state), 0.
      split; [exact I |]. split; vm_compute; reflexivity.
Qed.

(** A starting state of the Thiele core with a positive meter and no certificate. *)
Definition paid_uncertified : VMState := {|
  vm_graph := init_graph;
  vm_csrs := init_csrs;
  vm_regs := repeat 0 REG_COUNT;
  vm_mem := repeat 0 MEM_SIZE;
  vm_pc := 0;
  vm_mu := 1;
  vm_mu_tensor := vm_mu_tensor_default;
  vm_err := false;
  vm_logic_acc := 0;
  vm_mstatus := 0;
  vm_witness := witness_counts_zero;
  vm_certified := false
|}.

Theorem meter_core_not_equiv_mod_schedule :
  ~ equiv_mod_schedule_via MeterCore meter_cover.
Proof.
  intros [_ [_ [R [Hcov [_ [Hback Hstep]]]]]].
  destruct (Hback ([], paid_uncertified) I) as [m [_ Hr]].
  pose proof (Hcov m _ Hr) as Hm. simpl in Hm. subst m.
  destruct (Hstep _ _ Hr) as [Hcert _].
  vm_compute in Hcert. discriminate.
Qed.

Theorem uniqueness_round3a_refuted : ~ uniqueness_round3a.
Proof.
  intro H.
  exact (meter_core_not_equiv_mod_schedule
           (H MeterCore meter_cover meter_core_honest3a)).
Qed.

Print Assumptions uniqueness_round3b_holds.
Print Assumptions uniqueness_round3a_refuted.
Print Assumptions billed_core_equiv_mod_schedule.
Print Assumptions surcharged_core_equiv_mod_schedule.
