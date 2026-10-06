(** Tc2Collision.v: the first structural facts about a program that adds a
    constant to every input (the setting of [tc_LL] in TcPlain.v).

    [tc2_adds P t] says: started with x in counter A and 0 in counter B,
    P stops with x + t in counter A, for every x. (This is [tc_adds] of
    TcPlain.v with the definitions unfolded.)

    Proved here, for the machine of EarnedCore.v itself:

      [tc2_collision]       two runs of such a program, on different inputs,
                            never reach the same core state: the same state
                            has the same future, hence the same output.
      [tc2_collision_pure]  the same for a program that only uses INC, DEC
                            and HALT, where only the counters, the program
                            counter and the trap latch matter (versions and
                            the fact table are never read).
      [tc2_shift_run]       for such a pure program a run from A = x + d is
                            the run from A = x with counter A raised by d,
                            for as long as the run from x never tests
                            counter A while it is zero.
      [tc2_slaving]         for such a program that adds a constant: along
                            one run, before the first test of A at zero, the
                            counter A is a function of the program counter
                            and the counter B.

    No axioms and no unfinished proofs.                                                 *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Definition tc2_adds (P : list E.instr) (t : nat) : Prop :=
  forall x, exists N,
    E.halted P (E.core_of (E.run_prog N P (E.start x 0))) /\
    E.ca (E.core_of (E.run_prog N P (E.start x 0))) = x + t.

Lemma tc2_run_add : forall n m P s,
  E.run_prog (n + m) P s = E.run_prog m P (E.run_prog n P s).
Proof.
  induction n as [| n IH]; intros m P s; simpl; [reflexivity | apply IH].
Qed.

Lemma tc2_after_halt : forall P s0 N K,
  E.halted P (E.core_of (E.run_prog N P s0)) -> N <= K ->
  E.run_prog K P s0 = E.run_prog N P s0.
Proof.
  intros P s0 N K H HK. replace K with (N + (K - N)) by lia.
  rewrite tc2_run_add. apply E.run_prog_halted. exact H.
Qed.

Lemma tc2_out_from : forall P x N n,
  E.halted P (E.core_of (E.run_prog N P (E.start x 0))) -> forall K, N <= K ->
  E.run_prog K P (E.run_prog n P (E.start x 0)) = E.run_prog N P (E.start x 0).
Proof.
  intros P x N n H K HK. rewrite <- tc2_run_add. rewrite Nat.add_comm.
  rewrite tc2_run_add. rewrite (tc2_after_halt P (E.start x 0) N K H HK).
  apply E.run_prog_halted. exact H.
Qed.

Lemma tc2_core_run_eq : forall n P s s',
  E.core_of s = E.core_of s' ->
  E.core_of (E.run_prog n P s) = E.core_of (E.run_prog n P s').
Proof.
  induction n as [| n IH]; intros P s s' H; simpl; [exact H |].
  apply IH. rewrite !E.step_core. rewrite H. reflexivity.
Qed.

(* Same core state, same future: runs on different inputs never meet. *)
Theorem tc2_collision : forall P t x x' n m,
  tc2_adds P t ->
  E.core_of (E.run_prog n P (E.start x 0)) = E.core_of (E.run_prog m P (E.start x' 0)) ->
  x = x'.
Proof.
  intros P t x x' n m Hadd Hc.
  destruct (Hadd x) as [N [HN Ha]]. destruct (Hadd x') as [N' [HN' Ha']].
  assert (HK : N <= N + N') by lia. assert (HK' : N' <= N + N') by lia.
  pose proof (tc2_out_from P x N n HN (N + N') HK) as H1.
  pose proof (tc2_out_from P x' N' m HN' (N + N') HK') as H2.
  pose proof (tc2_core_run_eq (N + N') P _ _ Hc) as H3.
  rewrite H1, H2 in H3. rewrite H3 in Ha. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Pure programs: INC, DEC, HALT                                       *)
(* ------------------------------------------------------------------ *)

Definition tc2_pure (P : list E.instr) : Prop :=
  forall i, In i P ->
    match i with E.INC _ | E.DEC _ _ | E.HALT => True | _ => False end.

(* equal up to the part of the state a pure program reads *)
Definition tc2_pe (k k' : E.core) : Prop :=
  E.pc k = E.pc k' /\ E.ca k = E.ca k' /\ E.cb k = E.cb k' /\ E.err k = E.err k'.

Lemma tc2_next_in : forall P k i,
  E.next_instr P k = Some i -> E.err k = false /\ In i P.
Proof.
  intros P k i H. unfold E.next_instr in H.
  destruct (E.err k) eqn:Ee; [discriminate |]. split; [reflexivity |].
  destruct (E.fetch P (E.pc k)) as [j |] eqn:Ef; [| discriminate].
  assert (Hj : In j P).
  { unfold E.fetch in Ef. destruct (E.pc k) as [| m]; [discriminate |].
    eapply nth_error_In; eauto. }
  destruct j; simpl in H; try discriminate; injection H as <-; exact Hj.
Qed.

Lemma tc2_pe_step : forall P k k', tc2_pure P -> tc2_pe k k' ->
  tc2_pe (E.core_step P k) (E.core_step P k').
Proof.
  intros P k k' Hp (Hpc & Hca & Hcb & Her).
  assert (Hn : E.next_instr P k = E.next_instr P k').
  { unfold E.next_instr. rewrite Her, Hpc. reflexivity. }
  unfold E.core_step. rewrite <- Hn.
  destruct (E.next_instr P k) as [i |] eqn:E1.
  - destruct (tc2_next_in P k i E1) as [Ee Hin].
    pose proof (Hp i Hin) as Hi. unfold E.cexec. rewrite Ee. rewrite <- Her. rewrite Ee.
    destruct i as [c | c j | | p c | p c |]; simpl in Hi; try contradiction;
      unfold tc2_pe.
    + destruct c; unfold E.write, E.val; simpl; rewrite ?Hca, ?Hcb, ?Hpc; repeat split;
        try (first [reflexivity | assumption]).
    + destruct c; unfold E.val; simpl; rewrite ?Hca, ?Hcb;
        [destruct (E.ca k') eqn:Hk' | destruct (E.cb k') eqn:Hk'];
        unfold E.goto, E.write; simpl; rewrite ?Hca, ?Hcb, ?Hpc; repeat split;
        try (first [reflexivity | assumption | congruence]).
    + simpl. repeat split; assumption.
  - unfold tc2_pe. repeat split; assumption.
Qed.

Lemma tc2_pe_run : forall n P s s', tc2_pure P ->
  tc2_pe (E.core_of s) (E.core_of s') ->
  tc2_pe (E.core_of (E.run_prog n P s)) (E.core_of (E.run_prog n P s')).
Proof.
  induction n as [| n IH]; intros P s s' Hp H; simpl; [exact H |].
  apply IH; [exact Hp |]. rewrite !E.step_core. apply tc2_pe_step; assumption.
Qed.

Theorem tc2_collision_pure : forall P t x x' n m,
  tc2_pure P -> tc2_adds P t ->
  tc2_pe (E.core_of (E.run_prog n P (E.start x 0))) (E.core_of (E.run_prog m P (E.start x' 0))) ->
  x = x'.
Proof.
  intros P t x x' n m Hp Hadd Hc.
  destruct (Hadd x) as [N [HN Ha]]. destruct (Hadd x') as [N' [HN' Ha']].
  assert (HK : N <= N + N') by lia. assert (HK' : N' <= N + N') by lia.
  pose proof (tc2_out_from P x N n HN (N + N') HK) as H1.
  pose proof (tc2_out_from P x' N' m HN' (N + N') HK') as H2.
  pose proof (tc2_pe_run (N + N') P _ _ Hp Hc) as H3.
  rewrite H1, H2 in H3. destruct H3 as (_ & H3 & _). rewrite H3 in Ha. lia.
Qed.

(* the trap latch stays down in a pure run *)
Lemma tc2_err_false : forall n P s, tc2_pure P -> E.err (E.core_of s) = false ->
  E.err (E.core_of (E.run_prog n P s)) = false.
Proof.
  induction n as [| n IH]; intros P s Hp H; simpl; [exact H |].
  apply IH; [exact Hp |]. rewrite E.step_core. unfold E.core_step.
  destruct (E.next_instr P (E.core_of s)) as [i |] eqn:E1; [| exact H].
  destruct (tc2_next_in P _ i E1) as [Ee Hin]. pose proof (Hp i Hin) as Hi.
  unfold E.cexec. rewrite Ee.
  destruct i as [c | c j | | p c | p c |]; simpl in Hi; try contradiction.
  - destruct c; unfold E.write; simpl; exact Ee.
  - destruct c; unfold E.val; simpl;
      [destruct (E.ca (E.core_of s)) | destruct (E.cb (E.core_of s))];
      unfold E.goto, E.write; simpl; exact Ee.
  - exact Ee.
Qed.

(* ------------------------------------------------------------------ *)
(* The shift lemma                                                      *)
(* ------------------------------------------------------------------ *)

Definition tc2_shift (d : nat) (k : E.core) : E.core :=
  E.mkcore (E.ca k + d) (E.cb k) (E.va k) (E.vb k) (E.pc k) (E.facts k) (E.chan k) (E.err k).

(* the step reads counter A at zero *)
Definition tc2_zt (P : list E.instr) (k : E.core) : Prop :=
  match E.next_instr P k with
  | Some (E.DEC E.CA _) => E.ca k = 0
  | _ => False
  end.

Lemma tc2_shift_step : forall P d k, tc2_pure P -> ~ tc2_zt P k ->
  E.core_step P (tc2_shift d k) = tc2_shift d (E.core_step P k).
Proof.
  intros P d k Hp Hz. unfold E.core_step.
  assert (Hn : E.next_instr P (tc2_shift d k) = E.next_instr P k).
  { unfold E.next_instr, tc2_shift. simpl. reflexivity. }
  rewrite Hn. destruct (E.next_instr P k) as [i |] eqn:E1.
  - destruct (tc2_next_in P k i E1) as [Ee Hin]. pose proof (Hp i Hin) as Hi.
    unfold E.cexec. simpl. rewrite Ee. unfold tc2_shift at 2. simpl. rewrite Ee.
    destruct i as [c | c j | | p c | p c |]; simpl in Hi; try contradiction.
    + destruct c; unfold E.write, E.val, tc2_shift; simpl; reflexivity.
    + destruct c.
      * unfold tc2_zt in Hz. rewrite E1 in Hz. unfold E.val. simpl.
        destruct (E.ca k) as [| n].
        -- exfalso. apply Hz. reflexivity.
        -- replace (S n + d) with (S (n + d)) by lia.
           unfold E.write, tc2_shift. simpl. reflexivity.
      * unfold E.val. simpl. destruct (E.cb k);
          unfold E.goto, E.write, tc2_shift; simpl; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma tc2_shift_run : forall n P d s s', tc2_pure P ->
  E.core_of s' = tc2_shift d (E.core_of s) ->
  (forall j, j < n -> ~ tc2_zt P (E.core_of (E.run_prog j P s))) ->
  E.core_of (E.run_prog n P s') = tc2_shift d (E.core_of (E.run_prog n P s)).
Proof.
  induction n as [| n IH]; intros P d s s' Hp H Hs; simpl; [exact H |].
  apply IH; [exact Hp | | ].
  - rewrite !E.step_core. rewrite H. apply tc2_shift_step; [exact Hp |].
    apply (Hs 0). lia.
  - intros j Hj. apply (Hs (S j)). lia.
Qed.

Lemma tc2_start_shift : forall x d,
  E.core_of (E.start (x + d) 0) = tc2_shift d (E.core_of (E.start x 0)).
Proof. intros x d. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Slaving: before the first test of A at zero, A is a function of the  *)
(* program counter and B.                                               *)
(* ------------------------------------------------------------------ *)

Definition tc2_safe (P : list E.instr) (x n : nat) : Prop :=
  forall j, j < n -> ~ tc2_zt P (E.core_of (E.run_prog j P (E.start x 0))).

Lemma tc2_safe_mono : forall P x n m, tc2_safe P x n -> m <= n -> tc2_safe P x m.
Proof. intros P x n m H Hm j Hj. apply H. lia. Qed.

Lemma tc2_shifted_run : forall P x d n, tc2_pure P -> tc2_safe P x n ->
  E.core_of (E.run_prog n P (E.start (x + d) 0)) =
  tc2_shift d (E.core_of (E.run_prog n P (E.start x 0))).
Proof.
  intros P x d n Hp Hs. apply tc2_shift_run; [exact Hp | reflexivity | exact Hs].
Qed.

Theorem tc2_slaving : forall P t x n m,
  tc2_pure P -> tc2_adds P t -> tc2_safe P x n -> tc2_safe P x m ->
  E.pc (E.core_of (E.run_prog n P (E.start x 0))) = E.pc (E.core_of (E.run_prog m P (E.start x 0))) ->
  E.cb (E.core_of (E.run_prog n P (E.start x 0))) = E.cb (E.core_of (E.run_prog m P (E.start x 0))) ->
  E.ca (E.core_of (E.run_prog n P (E.start x 0))) = E.ca (E.core_of (E.run_prog m P (E.start x 0))).
Proof.
  intros P t x n m Hp Hadd Hn Hm Hpc Hcb.
  set (kn := E.core_of (E.run_prog n P (E.start x 0))) in *.
  set (km := E.core_of (E.run_prog m P (E.start x 0))) in *.
  assert (Hen : E.err kn = false).
  { subst kn. apply tc2_err_false; [exact Hp | reflexivity]. }
  assert (Hem : E.err km = false).
  { subst km. apply tc2_err_false; [exact Hp | reflexivity]. }
  destruct (Nat.lt_trichotomy (E.ca kn) (E.ca km)) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - (* ca kn < ca km: raise the input by e and compare time n with time m *)
    exfalso.
    assert (He : exists e, E.ca km = E.ca kn + e /\ e > 0)
      by (exists (E.ca km - E.ca kn); lia).
    destruct He as [e [He Hpos]].
    assert (Hr : E.core_of (E.run_prog n P (E.start (x + e) 0)) = tc2_shift e kn)
      by (apply tc2_shifted_run; assumption).
    assert (Hx : x + e = x).
    { apply (tc2_collision_pure P t (x + e) x n m Hp Hadd).
      rewrite Hr. change (E.core_of (E.run_prog m P (E.start x 0))) with km.
      unfold tc2_pe, tc2_shift. simpl. repeat split;
        [exact Hpc | lia | exact Hcb | rewrite Hen; symmetry; exact Hem]. }
    lia.
  - exfalso.
    assert (He : exists e, E.ca kn = E.ca km + e /\ e > 0)
      by (exists (E.ca kn - E.ca km); lia).
    destruct He as [e [He Hpos]].
    assert (Hr : E.core_of (E.run_prog m P (E.start (x + e) 0)) = tc2_shift e km)
      by (apply tc2_shifted_run; assumption).
    assert (Hx : x + e = x).
    { apply (tc2_collision_pure P t (x + e) x m n Hp Hadd).
      rewrite Hr. change (E.core_of (E.run_prog n P (E.start x 0))) with kn.
      unfold tc2_pe, tc2_shift. simpl. repeat split;
        [symmetry; exact Hpc | lia | symmetry; exact Hcb | rewrite Hem; symmetry; exact Hen]. }
    lia.
Qed.

Print Assumptions tc2_collision.
Print Assumptions tc2_collision_pure.
Print Assumptions tc2_shift_run.
Print Assumptions tc2_slaving.
