(** NecFFloor: the universal floor, pushed to its limit.

    The book's floor says: in any certification system, a run from a state
    reading no to a state reading yes costs at least one. This file shows:

    - The premise A2 is exactly what the floor needs. The floor for every
      start holds if and only if A2 holds ([nec_f_floor_iff_a2]).
    - For one fixed start, A2 is only needed at the states the start reaches
      for free, and there it is needed exactly ([nec_f_floor_at_iff_free_reach]).
      A free flip at a state reachable only by a paid run does not break the
      floor ([nec_f_paid_door_floor], [nec_f_paid_door_not_a2]).
    - The bound one is too weak. A run pays at least once for every time the
      reading goes from no to yes ([nec_f_cost_ge_rises]); no permanence is
      needed. That bound is attained for every number of rises
      ([nec_f_bit_rises_exact]) and is equivalent to A2 ([nec_f_rises_iff_a2]).
    - The plain bound one is attained ([nec_f_floor_one_attained]), and the
      floor fails for a concrete system without A2 ([nec_f_free_stamp_floor_fails]). *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import CostSemanticsComparison.

(** * The floor over a bare system: a step, a cost and a reading, with no A2. *)

Section Bare.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable cert : S -> bool.

Notation run := (CostSemanticsComparison.run S I step).
Notation total := (CostSemanticsComparison.total I cost).

Definition nec_f_floor_everywhere : Prop :=
  forall t s, cert s = false -> cert (run t s) = true -> total t >= 1.

Definition nec_f_floor_at (s0 : S) : Prop :=
  forall t, cert (run t s0) = true -> total t >= 1.

Lemma nec_f_run_app : forall t1 t2 s, run (t1 ++ t2) s = run t2 (run t1 s).
Proof. induction t1 as [| i t1 IH]; intros t2 s; simpl; [reflexivity | apply IH]. Qed.

Lemma nec_f_total_app : forall t1 t2, total (t1 ++ t2) = total t1 + total t2.
Proof. induction t1 as [| i t1 IH]; intros t2; simpl; [reflexivity | rewrite IH; lia]. Qed.

(** A2 for every state is exactly the floor for every start. *)
Theorem nec_f_floor_iff_a2 :
  a2 S I step cost cert <-> nec_f_floor_everywhere.
Proof.
  split.
  - intros Ha t s H0 H1. exact (nfi_by_potential S I step cost cert Ha t s H0 H1).
  - intros Hf s i H0 H1. specialize (Hf [i] s H0 H1). simpl in Hf. lia.
Qed.

(** The states a start reaches by runs of total cost zero. *)
Inductive nec_f_free_reach (s0 : S) : S -> Prop :=
| nec_f_fr_refl : nec_f_free_reach s0 s0
| nec_f_fr_step : forall r i, nec_f_free_reach s0 r -> cost i = 0 ->
    nec_f_free_reach s0 (step r i).

Lemma nec_f_free_reach_run :
  forall s0 r, nec_f_free_reach s0 r -> exists u, total u = 0 /\ run u s0 = r.
Proof.
  intros s0 r H. induction H as [| r i Hr IH Hc].
  - exists []. split; reflexivity.
  - destruct IH as [u [Hu Hrun]]. exists (u ++ [i]). split.
    + rewrite nec_f_total_app. simpl. lia.
    + rewrite nec_f_run_app. simpl. rewrite Hrun. reflexivity.
Qed.

(** The A2 premise restricted to the states the start reaches for free. *)
Definition nec_f_a2_free_from (s0 : S) : Prop :=
  forall r i, nec_f_free_reach s0 r -> cert r = false -> cert (step r i) = true ->
    cost i >= 1.

(** For one start reading no, the floor holds exactly when A2 holds at every
    state that start reaches for free. *)
Theorem nec_f_floor_at_iff_free_reach :
  forall s0, cert s0 = false ->
    nec_f_floor_at s0 <-> nec_f_a2_free_from s0.
Proof.
  intros s0 H0. split.
  - intros Hf r i Hr Hrn Hry.
    destruct (nec_f_free_reach_run s0 r Hr) as [u [Hu Hrun]].
    specialize (Hf (u ++ [i])).
    rewrite nec_f_run_app, Hrun, nec_f_total_app, Hu in Hf. simpl in Hf.
    specialize (Hf Hry). lia.
  - intros Hl.
    assert (Hgen : forall t s, nec_f_free_reach s0 s -> cert s = false ->
                     cert (run t s) = true -> total t >= 1).
    { intro t. induction t as [| i t' IH]; intros s Hs Hsn Hend.
      - simpl in Hend. congruence.
      - simpl in Hend |- *.
        destruct (cert (step s i)) eqn:Hy.
        + pose proof (Hl s i Hs Hsn Hy). lia.
        + destruct (cost i) as [| c] eqn:Hc; [| lia].
          apply (IH (step s i)); [apply nec_f_fr_step; assumption | exact Hy | exact Hend]. }
    intros t Hend. exact (Hgen t s0 (nec_f_fr_refl s0) H0 Hend).
Qed.

(** The states a start reaches at all. *)
Inductive nec_f_reach (s0 : S) : S -> Prop :=
| nec_f_r_refl : nec_f_reach s0 s0
| nec_f_r_step : forall r i, nec_f_reach s0 r -> nec_f_reach s0 (step r i).

(** A2 at the reachable states is enough for the floor at that start: the
    premise "for every state" can be dropped to "for every reachable state". *)
Corollary nec_f_floor_at_from_reachable_a2 :
  forall s0, cert s0 = false ->
    (forall r i, nec_f_reach s0 r -> cert r = false -> cert (step r i) = true ->
       cost i >= 1) ->
    nec_f_floor_at s0.
Proof.
  intros s0 H0 Hr. apply (nec_f_floor_at_iff_free_reach s0 H0).
  intros r i Hfr. apply Hr.
  clear i. induction Hfr; [constructor | constructor; assumption].
Qed.

(** How many times the reading goes from no to yes along the run. *)
Fixpoint nec_f_rises (t : list I) (s : S) : nat :=
  match t with
  | [] => 0
  | i :: t' => (if negb (cert s) && cert (step s i) then 1 else 0)
               + nec_f_rises t' (step s i)
  end.

(** Under A2 a run pays at least once per rise. No permanence is assumed. *)
Theorem nec_f_cost_ge_rises :
  a2 S I step cost cert -> forall t s, total t >= nec_f_rises t s.
Proof.
  intros Ha t. induction t as [| i t IH]; intros s; simpl; [lia |].
  specialize (IH (step s i)).
  destruct (cert s) eqn:Hs, (cert (step s i)) eqn:Hy; simpl; try lia.
  pose proof (Ha s i Hs Hy). lia.
Qed.

(** A run from no to yes rises at least once, so the rise bound contains the
    floor. *)
Lemma nec_f_rises_pos :
  forall t s, cert s = false -> cert (run t s) = true -> nec_f_rises t s >= 1.
Proof.
  induction t as [| i t IH]; intros s H0 H1; simpl in *; [congruence |].
  rewrite H0. simpl. destruct (cert (step s i)) eqn:Hy; [lia |].
  specialize (IH _ Hy H1). lia.
Qed.

(** The rise bound for every run is equivalent to A2: it asks nothing more. *)
Theorem nec_f_rises_iff_a2 :
  a2 S I step cost cert <-> (forall t s, total t >= nec_f_rises t s).
Proof.
  split; [apply nec_f_cost_ge_rises |].
  intros H s i H0 H1. specialize (H [i] s). simpl in H. rewrite H0, H1 in H.
  simpl in H. lia.
Qed.

(** The rise bound is met with equality exactly by runs on which every step
    costs its rise indicator. *)
Fixpoint nec_f_pays_rises_exactly (t : list I) (s : S) : Prop :=
  match t with
  | [] => True
  | i :: t' => cost i = (if negb (cert s) && cert (step s i) then 1 else 0)
               /\ nec_f_pays_rises_exactly t' (step s i)
  end.

Theorem nec_f_rises_exact_iff :
  a2 S I step cost cert ->
  forall t s, total t = nec_f_rises t s <-> nec_f_pays_rises_exactly t s.
Proof.
  intros Ha t. induction t as [| i t IH]; intros s; simpl; [tauto |].
  pose proof (nec_f_cost_ge_rises Ha t (step s i)) as Hrest.
  assert (Hstep : cost i >= (if negb (cert s) && cert (step s i) then 1 else 0)).
  { destruct (cert s) eqn:Hs, (cert (step s i)) eqn:Hy; simpl; try lia.
    exact (Ha s i Hs Hy). }
  rewrite <- (IH (step s i)). split.
  - intro H. split; lia.
  - intros [H1 H2]. lia.
Qed.

End Bare.

(** * The same over the repo's record *)

Lemma nec_f_cs_run_is_run :
  forall CS t s, cs_run CS t s = CostSemanticsComparison.run _ _ (cs_step CS) t s.
Proof. intros CS t. induction t as [| i t IH]; intros s; simpl; [reflexivity | apply IH]. Qed.

Lemma nec_f_cs_total_is_total :
  forall CS t, cs_total_cost CS t = CostSemanticsComparison.total _ (cs_cost CS) t.
Proof. intros CS t. induction t as [| i t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** In every certification system a run pays at least once per rise. *)
Theorem nec_f_cs_cost_ge_rises :
  forall (CS : CertificationSystem) t s,
    cs_total_cost CS t >= nec_f_rises _ _ (cs_step CS) (cs_cert CS) t s.
Proof.
  intros CS t s. rewrite nec_f_cs_total_is_total.
  apply nec_f_cost_ge_rises. exact (cs_cert_costs CS).
Qed.

(** * Witnesses *)

(** A bit with a paid SET and a free RESET. It meets A2; certifying, revoking
    and certifying again costs two, not one. *)
Inductive NecFBitOp := NecFSet | NecFReset.

Definition nec_f_bit_step (b : bool) (o : NecFBitOp) : bool :=
  match o with NecFSet => true | NecFReset => false end.
Definition nec_f_bit_cost (o : NecFBitOp) : nat :=
  match o with NecFSet => 1 | NecFReset => 0 end.

Lemma nec_f_bit_a2 : a2 bool NecFBitOp nec_f_bit_step nec_f_bit_cost (fun b => b).
Proof. intros s [|] _ H; simpl in *; [lia | discriminate]. Qed.

Definition nec_f_bit_cs : CertificationSystem :=
  {| cs_state := bool; cs_instr := NecFBitOp; cs_step := nec_f_bit_step;
     cs_cost := nec_f_bit_cost; cs_cert := fun b => b; cs_cert_costs := nec_f_bit_a2 |}.

Fixpoint nec_f_set_reset (k : nat) : list NecFBitOp :=
  match k with 0 => [] | S k' => NecFSet :: NecFReset :: nec_f_set_reset k' end.

(** For every k, the run SET, RESET repeated k times from no rises k times and
    costs exactly k: the rise bound is attained for every number of rises. *)
Theorem nec_f_bit_rises_exact :
  forall k,
    nec_f_rises bool NecFBitOp nec_f_bit_step (fun b => b) (nec_f_set_reset k) false = k /\
    cs_total_cost nec_f_bit_cs (nec_f_set_reset k) = k.
Proof.
  induction k as [| k [IH1 IH2]]; [split; reflexivity |].
  simpl in *. split; [rewrite IH1 | rewrite IH2]; reflexivity.
Qed.

(** Certify, revoke, certify: the plain floor says one, the true price is two. *)
Theorem nec_f_bit_recertify_costs_two :
  cs_cert nec_f_bit_cs false = false /\
  cs_cert nec_f_bit_cs (cs_run nec_f_bit_cs [NecFSet; NecFReset; NecFSet] false) = true /\
  cs_total_cost nec_f_bit_cs [NecFSet; NecFReset; NecFSet] = 2 /\
  (forall CS : CertificationSystem, forall t s,
     cs_total_cost CS t >= nec_f_rises _ _ (cs_step CS) (cs_cert CS) t s) /\
  nec_f_rises bool NecFBitOp nec_f_bit_step (fun b => b) [NecFSet; NecFReset; NecFSet] false = 2.
Proof.
  repeat split; try reflexivity. apply nec_f_cs_cost_ge_rises.
Qed.

(** The plain bound one is attained: one SET from no costs exactly one. *)
Theorem nec_f_floor_one_attained :
  cs_cert nec_f_bit_cs false = false /\
  cs_cert nec_f_bit_cs (cs_run nec_f_bit_cs [NecFSet] false) = true /\
  cs_total_cost nec_f_bit_cs [NecFSet] = 1.
Proof. repeat split. Qed.

(** The start must read no: from a state reading yes the empty run reaches
    yes at cost zero, in a system that meets A2. *)
Theorem nec_f_floor_needs_no_start :
  cs_cert nec_f_bit_cs true = true /\
  cs_cert nec_f_bit_cs (cs_run nec_f_bit_cs [] true) = true /\
  cs_total_cost nec_f_bit_cs [] = 0.
Proof. repeat split. Qed.

(** Without A2 the floor fails: the free stamp certifies at cost zero. *)
Theorem nec_f_free_stamp_floor_fails :
  ~ nec_f_floor_everywhere bool NecFBitOp nec_f_bit_step (fun _ => 0) (fun b => b).
Proof.
  intro H. specialize (H [NecFSet] false eq_refl eq_refl). simpl in H. lia.
Qed.

(** A free flip behind a paid door. Three rooms: A and B read no, C reads yes.
    PAY moves A to B and costs one; FREE moves B to C and costs zero. The
    floor holds from A, yet A2 fails at B, which A reaches. *)
Inductive NecFRoom := NecFA | NecFB | NecFC.
Inductive NecFDoor := NecFPay | NecFFree.

Definition nec_f_door_step (r : NecFRoom) (d : NecFDoor) : NecFRoom :=
  match r, d with
  | NecFA, NecFPay => NecFB
  | NecFB, NecFFree => NecFC
  | r, _ => r
  end.
Definition nec_f_door_cost (d : NecFDoor) : nat :=
  match d with NecFPay => 1 | NecFFree => 0 end.
Definition nec_f_door_cert (r : NecFRoom) : bool :=
  match r with NecFC => true | _ => false end.

Lemma nec_f_door_free_reach_A :
  forall r, nec_f_free_reach NecFRoom NecFDoor nec_f_door_step nec_f_door_cost NecFA r ->
    r = NecFA.
Proof.
  intros r H. induction H as [| r d Hr IH Hc]; [reflexivity |].
  subst r. destruct d; [discriminate | reflexivity].
Qed.

Theorem nec_f_paid_door_floor :
  nec_f_floor_at NecFRoom NecFDoor nec_f_door_step nec_f_door_cost nec_f_door_cert NecFA.
Proof.
  apply (nec_f_floor_at_iff_free_reach _ _ _ _ _ NecFA eq_refl).
  intros r d Hr. apply nec_f_door_free_reach_A in Hr. subst r.
  destruct d; simpl; discriminate.
Qed.

Theorem nec_f_paid_door_not_a2 :
  nec_f_reach NecFRoom NecFDoor nec_f_door_step NecFA NecFB /\
  ~ a2 NecFRoom NecFDoor nec_f_door_step nec_f_door_cost nec_f_door_cert.
Proof.
  split.
  - change NecFB with (nec_f_door_step NecFA NecFPay). repeat constructor.
  - intro H. specialize (H NecFB NecFFree eq_refl eq_refl). simpl in H. lia.
Qed.

Print Assumptions nec_f_floor_iff_a2.
Print Assumptions nec_f_floor_at_iff_free_reach.
Print Assumptions nec_f_floor_at_from_reachable_a2.
Print Assumptions nec_f_cost_ge_rises.
Print Assumptions nec_f_rises_pos.
Print Assumptions nec_f_rises_iff_a2.
Print Assumptions nec_f_rises_exact_iff.
Print Assumptions nec_f_cs_cost_ge_rises.
Print Assumptions nec_f_bit_rises_exact.
Print Assumptions nec_f_bit_recertify_costs_two.
Print Assumptions nec_f_floor_one_attained.
Print Assumptions nec_f_free_stamp_floor_fails.
Print Assumptions nec_f_floor_needs_no_start.
Print Assumptions nec_f_paid_door_floor.
Print Assumptions nec_f_paid_door_not_a2.
