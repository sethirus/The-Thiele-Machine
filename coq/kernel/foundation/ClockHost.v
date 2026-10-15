(* ClockHost.v: the clock program on the host machine of U.

   The PAY-free host machine of U (EarnedMulti with the property PSlot),
   which UniversalRun.v proves Thiele-complete [universal_thiele_complete],
   runs every two-counter program with its ledger rising by exactly one per
   base step, with the trap and the flag down throughout, and with halting
   matched.  Register 2 is set to 1 (PSlot holds of 1), checked once, and a
   COMMIT of that claim is placed before every instruction.  No PAY.      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalRun.
Require Minimal.ThieleComplete.
Module TC := Minimal.ThieleComplete.

Notation hst := (@M.state hprop).
Notation hins := (@M.instr hprop).
Notation hstep := (M.step hprop_eqb heval).
Notation hrunp := (M.run_prog hprop_eqb heval).

Definition cj (j : nat) : nat := match j with 0 => 0 | S _ => S (2 * j) end.

Definition clk_instr (i : TC.cm_instr) : hins :=
  match i with
  | TC.CINC r => M.INC (hreg_of r)
  | TC.CDEC r j => M.DEC (hreg_of r) (cj j)
  end.

Fixpoint body (P : list TC.cm_instr) : list hins :=
  match P with [] => [] | i :: rest => M.COMMIT PSlot 2 :: clk_instr i :: body rest end.

Definition clock_prog (P : list TC.cm_instr) : list hins :=
  M.INC 2 :: M.CHECK PSlot 2 :: body P.

Lemma body_even : forall P m,
  nth_error (body P) (2 * m) = option_map (fun _ => M.COMMIT PSlot 2) (nth_error P m).
Proof.
  induction P as [| i P IH]; intros [| m]; simpl; auto.
  replace (m + S (m + 0)) with (S (2 * m)) by lia. simpl. apply IH.
Qed.

Lemma body_odd : forall P m,
  nth_error (body P) (S (2 * m)) = option_map clk_instr (nth_error P m).
Proof.
  induction P as [| i P IH]; intros [| m]; simpl; auto.
  replace (m + S (m + 0)) with (S (2 * m)) by lia. apply IH.
Qed.

(* The invariant: line l of P sits at host line cj l; registers 0 and 1 are
   the two-counter registers; register 2 holds 1 at version 1 and the fact
   (PSlot, 2, 1) is in the table; trap and flag down; ledger m. *)
Definition Inv (s : hst) (x : TC.cm_conf) (m : nat) : Prop :=
  M.pc (M.core_of s) = cj (fst x) /\
  M.vals (M.core_of s) 0 = fst (snd x) /\ M.vals (M.core_of s) 1 = snd (snd x) /\
  M.vals (M.core_of s) 2 = 1 /\ M.vers (M.core_of s) 2 = 1 /\
  In (M.mkfact PSlot 2 1) (M.facts (M.core_of s)) /\
  M.err (M.core_of s) = false /\ M.cert s = false /\ M.mu s = m.

Lemma fact_in_existsb : forall f l, In f l -> existsb (M.fact_eqb hprop_eqb f) l = true.
Proof.
  intros f l H. apply existsb_exists. exists f. split; [exact H |].
  apply (M.multi_fact_eqb_eq hprop_eqb hprop_eqb_eq). reflexivity.
Qed.

Lemma step_exec : forall P (s : hst) i,
  M.err (M.core_of s) = false -> M.fetch P (M.pc (M.core_of s)) = Some i -> i <> M.HALT ->
  hstep P s = M.exec hprop_eqb heval s i.
Proof.
  intros P s i He Hf Hi. unfold M.step, M.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. congruence.
Qed.

Lemma clock_step : forall P s x y m,
  Inv s x m -> TC.cm_step P x = Some y -> Inv (hrunp 2 (clock_prog P) s) y (S m).
Proof.
  intros P [[vs vr pc f ch e] mu c] [l [a b]] y m
    [Hpc [H0 [H1 [H2 [Hv2 [Hin [He [Hc Hmu]]]]]]]] Hst.
  simpl in *. subst pc e c mu.
  unfold TC.cm_step in Hst. destruct l as [| l]; [discriminate |].
  simpl in Hst. destruct (nth_error P l) as [i |] eqn:Hf; [| discriminate].
  injection Hst as <-.
  assert (Hfc : M.fetch (clock_prog P) (cj (S l)) = Some (M.COMMIT PSlot 2)).
  { unfold cj, clock_prog, M.fetch. replace (2 * S l) with (S (S (2 * l))) by lia.
    cbn [nth_error]. rewrite body_even, Hf. reflexivity. }
  assert (Hfi : M.fetch (clock_prog P) (S (cj (S l))) = Some (clk_instr i)).
  { unfold cj, clock_prog, M.fetch. replace (2 * S l) with (S (S (2 * l))) by lia.
    change (nth_error (body P) (S (2 * l)) = Some (clk_instr i)).
    rewrite body_odd, Hf. reflexivity. }
  assert (Hok : M.commit_ok hprop_eqb (M.mkcore vs vr (cj (S l)) f ch false) PSlot 2 = true).
  { unfold M.commit_ok, M.claim. simpl. rewrite Hv2. apply fact_in_existsb, Hin. }
  cbn [M.run_prog].
  rewrite (step_exec (clock_prog P) (M.mkst (M.mkcore vs vr (cj (S l)) f ch false) m false)
             (M.COMMIT PSlot 2)); [| reflexivity | exact Hfc | discriminate].
  set (s1 := M.exec hprop_eqb heval _ (M.COMMIT PSlot 2)).
  assert (Hs1 : s1 = M.mkst (M.mkcore vs vr (S (cj (S l))) f
                         (Some (M.mkfact PSlot 2 1)) false) (S m) false).
  { subst s1. unfold M.exec, M.cexec. cbn [M.core_of M.err]. rewrite Hok.
    unfold M.commit_to, M.claim. simpl. rewrite Hv2, Nat.add_1_r. reflexivity. }
  rewrite Hs1. clear s1 Hs1.
  rewrite (step_exec _ _ (clk_instr i)); [| reflexivity | exact Hfi | destruct i; discriminate].
  subst a b. unfold Inv.
  destruct i as [r | r j]; destruct r; cbn [clk_instr hreg_of TC.cm_exec TC.cm_get TC.cm_set fst snd].
  - unfold M.exec, M.cexec; cbn. unfold M.upd; cbn. rewrite H2, Hv2.
    repeat split; auto; lia.
  - unfold M.exec, M.cexec; cbn. unfold M.upd; cbn. rewrite H2, Hv2.
    repeat split; auto; lia.
  - unfold M.exec, M.cexec; cbn. destruct (vs 0) as [| n] eqn:Ea; cbn.
    + rewrite H2, Hv2, Ea. repeat split; auto; lia.
    + unfold M.upd; cbn. rewrite H2, Hv2. repeat split; auto; try lia.
      all: try (destruct j; reflexivity).
  - unfold M.exec, M.cexec; cbn. destruct (vs 1) as [| n] eqn:Eb; cbn.
    + rewrite H2, Hv2, Eb. repeat split; auto; lia.
    + unfold M.upd; cbn. rewrite H2, Hv2. repeat split; auto; try lia.
      all: try (destruct j; reflexivity).
Qed.

Fixpoint cm_exact (n : nat) (P : list TC.cm_instr) (x : TC.cm_conf) : option TC.cm_conf :=
  match n with
  | 0 => Some x
  | S k => match TC.cm_step P x with None => None | Some y => cm_exact k P y end
  end.

Lemma clock_init : forall P a b,
  Inv (hrunp 2 (clock_prog P) (host_load a b)) (1, (a, b)) 1.
Proof.
  intros P a b. cbn [M.run_prog].
  rewrite (step_exec (clock_prog P) (host_load a b) (M.INC 2)); [| reflexivity | reflexivity | discriminate].
  rewrite (step_exec (clock_prog P) _ (M.CHECK PSlot 2)); [| reflexivity | reflexivity | discriminate].

  unfold Inv, host_load, M.exec, M.cexec, M.start, M.start_core; cbn.
  unfold M.check_ok, M.upd; cbn.
  repeat split; auto.
Qed.

Lemma clock_run : forall n P s x0 x m,
  Inv s x0 m -> cm_exact n P x0 = Some x -> Inv (hrunp (2 * n) (clock_prog P) s) x (m + n).
Proof.
  induction n as [| n IH]; intros P s x0 x m HI He.
  - simpl in He. injection He as <-. rewrite Nat.add_0_r. exact HI.
  - simpl in He. destruct (TC.cm_step P x0) as [y |] eqn:Hs; [| discriminate].
    replace (2 * S n) with (2 + 2 * n) by lia. rewrite M.multi_run_prog_add.
    replace (m + S n) with (S m + n) by lia.
    apply (IH P _ y x (S m)); [apply (clock_step P s x0 y m HI Hs) | exact He].
Qed.

(* Halting is matched: where P has stopped the host has halted, and where
   P can step the host's next instruction is the COMMIT. *)
Lemma clock_halted : forall P s x m,
  Inv s x m -> TC.cm_step P x = None -> M.halted (clock_prog P) (M.core_of s).
Proof.
  intros P s [l [a b]] m [Hpc [_ [_ [_ [_ [_ [He _]]]]]]] Hst.
  unfold M.halted, M.next_instr. rewrite He, Hpc. simpl fst.
  unfold TC.cm_step in Hst. destruct l as [| l]; [reflexivity |].
  simpl in Hst. destruct (nth_error P l) eqn:Hf; [discriminate |].
  unfold cj, clock_prog, M.fetch. replace (2 * S l) with (S (S (2 * l))) by lia.
  cbn [nth_error]. rewrite body_even, Hf. reflexivity.
Qed.

Lemma clock_live : forall P s x m y,
  Inv s x m -> TC.cm_step P x = Some y ->
  M.next_instr (clock_prog P) (M.core_of s) = Some (M.COMMIT PSlot 2).
Proof.
  intros P s [l [a b]] m y [Hpc [_ [_ [_ [_ [_ [He _]]]]]]] Hst.
  unfold M.next_instr. rewrite He, Hpc. simpl fst.
  unfold TC.cm_step in Hst. destruct l as [| l]; [discriminate |].
  simpl in Hst. destruct (nth_error P l) eqn:Hf; [| discriminate].
  unfold cj, clock_prog, M.fetch. replace (2 * S l) with (S (S (2 * l))) by lia.
  cbn [nth_error]. rewrite body_even, Hf. reflexivity.
Qed.

(* THE CLOCK.  The host machine of U is Thiele-complete (UniversalRun.v), and
   for every two-counter program P and start (a, b): after the two set-up
   steps and n simulated steps (2 + 2n host steps) the host's registers 0, 1
   are P's after n steps, the trap and the flag are down, and the ledger is
   exactly 1 + n; the host has halted there exactly when P has stopped.  The
   ledger is a step counter of an arbitrary two-counter computation, and the
   machine has no PAY. *)
Theorem thiele_complete_host_clock :
  TC.thiele_complete host_machine /\
  forall P a b n x,
    cm_exact n P (1, (a, b)) = Some x ->
    let s := hrunp (2 + 2 * n) (clock_prog P) (host_load a b) in
    M.vals (M.core_of s) 0 = fst (snd x) /\ M.vals (M.core_of s) 1 = snd (snd x) /\
    M.err (M.core_of s) = false /\ M.cert s = false /\ M.mu s = 1 + n /\
    (TC.cm_step P x = None <-> M.halted (clock_prog P) (M.core_of s)).
Proof.
  split; [exact universal_thiele_complete |].
  intros P a b n x He s.
  assert (HI : Inv s x (1 + n)).
  { subst s. rewrite M.multi_run_prog_add. apply (clock_run n P _ (1, (a, b)) x 1);
      [apply clock_init | exact He]. }
  pose proof HI as [_ [H0 [H1 [_ [_ [_ [Her [Hc Hmu]]]]]]]].
  repeat split; auto.
  - intro Hn. exact (clock_halted P s x (1 + n) HI Hn).
  - intro Hh. destruct (TC.cm_step P x) as [y |] eqn:Hs; [| reflexivity].
    unfold M.halted in Hh. rewrite (clock_live P s x (1 + n) y HI Hs) in Hh. discriminate.
Qed.

(* Every COMMIT in the clocked program is read as a record move by the
   host's interface, and every two-counter instruction as a base move. *)
Lemma clock_kinds : host_kind (M.COMMIT PSlot 2) = TC.KCommit (PSlot, 2) /\
  forall i, host_kind (clk_instr i) = TC.KBase.
Proof. split; [reflexivity | intros [r | r j]; reflexivity]. Qed.

Print Assumptions thiele_complete_host_clock.
Print Assumptions clock_kinds.
