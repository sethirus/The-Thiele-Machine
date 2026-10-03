(** EarnedCoreLinks.v: EarnedCore.v as an instance of the book's records.

    EarnedCore.v proves everything on the standard library alone. This file
    connects it to the records the rest of the work is stated over, with no
    new assumptions:

      - the vendored two-counter machine (MM2) is EarnedCore's INC/DEC
        fragment, step for step, so this machine's halting problem is
        undecidable                       [mm2_step_iff, mm2_halting_iff,
                                           earned_core_halting_undecidable];
      - EarnedCore is a CertificationSystem, so universal_nfi_any_substrate
        applies to it                     [earned_cs, earned_core_floor];
      - run as a closed machine it is an RCM that is Adequate
                                          [earned_core_adequate];
      - its flag is an honest extension of its base (everything but mu and
        the flag), so by record_axis_is_latch_holds it is a latch of that
        base                              [earned_core_honest,
                                           earned_core_is_latch].         *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Coq Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase.
From Kernel Require Import StructuralRecordAxis.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* The vendored two-counter machine is the INC/DEC fragment.          *)
(* ================================================================= *)

Definition of_mm2 (i : mm2_instr) : E.minsky :=
  match i with
  | mm2_inc_a => E.MINC E.CA
  | mm2_inc_b => E.MINC E.CB
  | mm2_dec_a j => E.MDEC E.CA j
  | mm2_dec_b j => E.MDEC E.CB j
  end.

Lemma mm2_instr_at_iff : forall (r : mm2_instr) i P,
  mm2_instr_at r i P <-> E.fetch P i = Some r.
Proof.
  intros r i P. split.
  - intros [l [rest [-> <-]]]. simpl.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - destruct i as [| i]; simpl; [discriminate |]. intro H.
    destruct (nth_error_split P i H) as [l [rest [-> Hl]]].
    exists l, rest. split; [reflexivity | lia].
Qed.

Lemma mm2_step_iff : forall P x y,
  mm2_step P x y <-> E.mstep (map of_mm2 P) x = Some y.
Proof.
  intros P [i [a b]] y. unfold mm2_step, E.mstep. simpl.
  rewrite E.fetch_map. split.
  - intros [r [Hat Hr]]. apply mm2_instr_at_iff in Hat. simpl in Hat.
    rewrite Hat. inversion Hr; subst; reflexivity.
  - destruct (E.fetch P i) as [r |] eqn:Hf; simpl; [| discriminate].
    intro H. exists r. split; [apply mm2_instr_at_iff; exact Hf |].
    destruct r; simpl in H;
      [ | | destruct a | destruct b]; injection H as <-; constructor.
Qed.

Lemma mm2_stop_iff : forall P x, mm2_stop P x <-> E.mstep (map of_mm2 P) x = None.
Proof.
  intros P x. unfold mm2_stop. split.
  - intro H. destruct (E.mstep (map of_mm2 P) x) as [y |] eqn:Hm; [| reflexivity].
    exfalso. apply (H y). apply mm2_step_iff. exact Hm.
  - intros H y Hs. apply mm2_step_iff in Hs. congruence.
Qed.

Lemma mm2_terminates_iff : forall P x,
  mm2_terminates P x <-> exists n, E.mstep (map of_mm2 P) (E.mrun n (map of_mm2 P) x) = None.
Proof.
  intros P x. unfold mm2_terminates. split.
  - intros [z [Hrt Hstop]]. apply clos_rt_rt1n_iff in Hrt.
    induction Hrt as [x | x y z Hs _ IH].
    + exists 0. simpl. apply mm2_stop_iff. exact Hstop.
    + destruct (IH Hstop) as [n Hn]. exists (S n). simpl.
      apply mm2_step_iff in Hs. rewrite Hs. exact Hn.
  - intros [n Hn]. revert x Hn. induction n as [| n IH]; intros x Hn; simpl in Hn.
    + exists x. split; [apply rt_refl | apply mm2_stop_iff; exact Hn].
    + destruct (E.mstep (map of_mm2 P) x) as [y |] eqn:Hm.
      * destruct (IH y Hn) as [z [Hrt Hstop]]. exists z. split; [| exact Hstop].
        apply rt_trans with y; [apply rt_step, mm2_step_iff; exact Hm | exact Hrt].
      * exists x. split; [apply rt_refl | apply mm2_stop_iff; exact Hm].
Qed.

(* This machine's halting problem: does program P halt from start a b. *)
Definition EARNED_HALTING (q : list E.instr * nat * nat) : Prop :=
  let '(P, a, b) := q in
  exists n, E.halted P (E.core_of (E.run_prog n P (E.start a b))).

Theorem mm2_halting_iff : forall P a b,
  MM2_HALTING (P, a, b) <-> EARNED_HALTING (E.compile (map of_mm2 P), a, b).
Proof.
  intros P a b. simpl. rewrite mm2_terminates_iff. apply E.halting_correspondence.
Qed.

Theorem earned_core_halting_undecidable : undecidable EARNED_HALTING.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exists (fun q => let '(P, a, b) := q in (E.compile (map of_mm2 P), a, b)).
  intros [[P a] b]. apply mm2_halting_iff.
Qed.

(* ================================================================= *)
(* A CertificationSystem.                                             *)
(* ================================================================= *)

Definition earned_cs : CertificationSystem :=
  mk_cert_system E.state E.instr E.exec E.cost E.cert E.a2.

Lemma cs_run_is_run : forall tr s, cs_run earned_cs tr s = E.run tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Lemma cs_total_cost_is_total_cost : forall tr,
  cs_total_cost earned_cs tr = E.total_cost tr.
Proof. induction tr; simpl; auto. Qed.

Theorem earned_core_floor : forall tr s0,
  E.cert s0 = false -> E.cert (E.run tr s0) = true -> E.total_cost tr >= 1.
Proof.
  intros tr s0 H0 H1. rewrite <- cs_total_cost_is_total_cost.
  apply (universal_nfi_any_substrate earned_cs tr s0 H0).
  rewrite cs_run_is_run. exact H1.
Qed.

(* ================================================================= *)
(* The closed machine: an RCM, Adequate, and its flag a latch.        *)
(* ================================================================= *)

Definition EarnedRCM : RCM := {|
  rc_state := list E.instr * E.state;
  rc_next := fun ps => (fst ps, E.step (fst ps) (snd ps));
  rc_init := fun ps => exists a b, snd ps = E.start a b;
  rc_cert := fun ps => E.cert (snd ps);
  rc_mu := fun ps => E.mu (snd ps);
  rc_halted := fun ps => E.halted (fst ps) (E.core_of (snd ps))
|}.

Lemma earned_rc_run : forall n P s, rc_run EarnedRCM n (P, s) = (P, E.run_prog n P s).
Proof.
  induction n; intros P s; [reflexivity |].
  unfold rc_run in *. rewrite Nat.iter_succ_r. apply IHn.
Qed.

Theorem earned_core_ledger : ledger_carried EarnedRCM.
Proof. intros [P s]. simpl. rewrite E.step_mu. lia. Qed.

Theorem earned_core_a2 : rc_a2 EarnedRCM.
Proof.
  intros [P s]. unfold step_cost. simpl. intros H0 H1.
  rewrite E.step_mu. unfold E.step in H1.
  destruct (E.next_instr P (E.core_of s)) as [i |]; [| congruence].
  pose proof (E.a2 s i H0 H1). lia.
Qed.

Theorem earned_core_permanent : record_permanent EarnedRCM.
Proof.
  intros [P s] H. simpl in *. rewrite E.step_cert, H. reflexivity.
Qed.

Theorem earned_core_record_write : reachable_record_write EarnedRCM.
Proof.
  exists (E.witness, E.start 0 0), 2. split; [exists 0, 0; reflexivity |].
  split; reflexivity.
Qed.

Theorem earned_core_adequate : Adequate EarnedRCM.
Proof.
  split; [exact earned_core_ledger |].
  split; [exact earned_core_a2 |].
  split.
  - exists (E.witness, E.start 0 0), 3. split; [exists 0, 0; reflexivity | reflexivity].
  - intros [[P a] b].
    exists (E.compile (map of_mm2 P), E.start a b).
    split; [exists a, b; reflexivity |].
    rewrite mm2_halting_iff. simpl.
    split; intros [n Hn]; exists n; rewrite ?earned_rc_run in *; exact Hn.
Qed.

(* The base: the stored program and everything but mu and the flag. *)
Definition EarnedBase : BaseMachine := {|
  b_state := list E.instr * E.core;
  b_next := fun pk => (fst pk, E.core_step (fst pk) (snd pk));
  b_init := fun pk => exists a b, snd pk = E.start_core a b;
  b_halted := fun pk => E.halted (fst pk) (snd pk)
|}.

Definition earned_cover : BaseCover EarnedRCM EarnedBase.
Proof.
  refine (Build_BaseCover EarnedRCM EarnedBase
            (fun ps => (fst ps, E.core_of (snd ps))) _ _ _ _).
  - intros [P s] [a [b Hs]]. exists a, b. simpl in *. rewrite Hs. reflexivity.
  - intros [P k] [a [b Hk]]. exists (P, E.start a b).
    split; [exists a, b; reflexivity |]. simpl in *. rewrite Hk. reflexivity.
  - intros [P s]. simpl. rewrite E.step_core. reflexivity.
  - intros [P s]. simpl. tauto.
Defined.

Theorem earned_core_honest : HonestBaseExtension EarnedRCM EarnedBase earned_cover.
Proof.
  split.
  - exists (fun pk r => orb r (match E.next_instr (fst pk) (snd pk) with
                              | Some i => E.fires (snd pk) i | None => false end)).
    intros [P s]. simpl. apply E.step_cert.
  - split; [exact earned_core_ledger |].
    split; [exact earned_core_a2 |].
    split; [exact earned_core_permanent | exact earned_core_record_write].
Qed.

Theorem earned_core_is_latch :
  exists h, latch_factorization EarnedRCM EarnedBase earned_cover h.
Proof. exact (record_axis_is_latch_holds _ _ _ earned_core_honest). Qed.

Print Assumptions mm2_halting_iff.
Print Assumptions earned_core_halting_undecidable.
Print Assumptions earned_core_floor.
Print Assumptions earned_core_adequate.
Print Assumptions earned_core_honest.
Print Assumptions earned_core_is_latch.
