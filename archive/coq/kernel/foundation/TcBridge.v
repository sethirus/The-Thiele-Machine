(** TcBridge.v: the vendored two-register alternate Minsky machine (MMA with
    two registers) read through EarnedCore's counter machine [mstep].

    The vendored machine keeps its state as a program counter and a vector of
    two numbers; EarnedCore keeps (pc, (A, B)). Register 1 of the vendored
    machine is counter A and register 0 is counter B (so the register that
    holds a Goedel code in the vendored compiler is the counter A). Both
    machines decrement-and-jump when the register is positive and fall
    through when it is 0.

    What is proved: one step of one machine is one step of the other
    [tc_step_iff]; the same for n steps [tc_steps_iff]; a vendored program
    outputs (stops at) a state exactly when the counter program stops there
    [tc_output_iff]; and a vendored program that does not terminate never
    stops in the counter machine [tc_nonterm_never_stops].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedCore.v. No axioms and no unfinished proofs.                         *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Definition tc_ctr (x : pos 2) : E.ctr := if pos_eq_dec x pos1 then E.CA else E.CB.

Definition tc_conv (i : mm_instr (pos 2)) : E.minsky :=
  match i with
  | mm_inc x => E.MINC (tc_ctr x)
  | mm_dec x j => E.MDEC (tc_ctr x) j
  end.

Definition tc_ofvec (v : vec nat 2) : nat * nat := (v#>pos1, v#>pos0).
Definition tc_tovec (a b : nat) : vec nat 2 := b ## a ## vec_nil.

Lemma tc_vec2 : forall v : vec nat 2, v = tc_tovec (v#>pos1) (v#>pos0).
Proof.
  intro v. apply vec_pos_ext. intro p. unfold tc_tovec. pos_inv p; simpl.
  - reflexivity.
  - pos_inv p; simpl.
    + reflexivity.
    + invert pos p.
Qed.

Lemma tc_vec2_ex : forall v : vec nat 2, exists a b, v = tc_tovec a b.
Proof. intro v. exists (v#>pos1), (v#>pos0). apply tc_vec2. Qed.

Lemma tc_ofvec_tovec : forall a b, tc_ofvec (tc_tovec a b) = (a, b).
Proof. reflexivity. Qed.

Lemma tc_ofvec_inj : forall v w, tc_ofvec v = tc_ofvec w -> v = w.
Proof.
  intros v w H. unfold tc_ofvec in H. injection H as H1 H2.
  rewrite (tc_vec2 v), (tc_vec2 w). rewrite H1, H2. reflexivity.
Qed.

Definition tc_exec (m : E.minsky) (x : E.mconf) : E.mconf :=
  match m with
  | E.MINC c => E.mset x c (S (E.mval x c)) (S (fst x))
  | E.MDEC c j =>
      match E.mval x c with
      | 0 => (S (fst x), snd x)
      | S n => E.mset x c n j
      end
  end.

Lemma tc_mstep_fetch : forall M x m, E.fetch M (fst x) = Some m -> E.mstep M x = Some (tc_exec m x).
Proof.
  intros M x m H. unfold E.mstep. rewrite H. destruct m as [c | c j]; [reflexivity |]. simpl. destruct (E.mval x c); reflexivity.
Qed.

Lemma tc_mstep_none : forall M x, E.fetch M (fst x) = None -> E.mstep M x = None.
Proof. intros M x H. unfold E.mstep. rewrite H. reflexivity. Qed.

Lemma tc_mstep_none_iff : forall M x, E.mstep M x = None <-> E.fetch M (fst x) = None.
Proof.
  intros M x. split.
  - intro H. destruct (E.fetch M (fst x)) as [m |] eqn:Hf; [| reflexivity].
    rewrite (tc_mstep_fetch M x m Hf) in H. discriminate.
  - apply tc_mstep_none.
Qed.

Lemma tc_ctr_0 : tc_ctr (pos0 : pos 2) = E.CB.
Proof. unfold tc_ctr. destruct (pos_eq_dec (pos0 : pos 2) (pos1 : pos 2)) as [E1 | E1]; [discriminate E1 | reflexivity]. Qed.

Lemma tc_ctr_1 : tc_ctr (pos1 : pos 2) = E.CA.
Proof. unfold tc_ctr. destruct (pos_eq_dec (pos1 : pos 2) (pos1 : pos 2)) as [E1 | E1]; [reflexivity | exfalso; apply E1; reflexivity]. Qed.

Lemma tc_inst_forward : forall (rho : mm_instr (pos 2)) i v j w,
  mma_sss rho (i, v) (j, w) -> (j, tc_ofvec w) = tc_exec (tc_conv rho) (i, tc_ofvec v).
Proof.
  intros rho i v j w H. destruct (tc_vec2_ex v) as [a [b ->]].
  destruct rho as [x | x k]; simpl tc_conv.
  - apply mma_sss_INC_inv in H as [-> ->].
    pos_inv x; simpl.
    + reflexivity.
    + pos_inv x; simpl.
      * try rewrite tc_ctr_1. reflexivity.
      * invert pos x.
  - destruct (vec_pos (tc_tovec a b) x) eqn:Hx.
    + apply mma_sss_DEC0_inv in H; [| exact Hx]. destruct H as [-> ->].
      pos_inv x; simpl in Hx |- *.
      * try rewrite tc_ctr_0. simpl. rewrite Hx. reflexivity.
      * pos_inv x; simpl in Hx |- *.
        -- try rewrite tc_ctr_1. simpl. rewrite Hx. reflexivity.
        -- invert pos x.
    + apply mma_sss_DEC1_inv with (u := n) in H; [| exact Hx]. destruct H as [-> ->].
      pos_inv x; simpl in Hx |- *.
      * try rewrite tc_ctr_0. simpl. rewrite Hx. reflexivity.
      * pos_inv x; simpl in Hx |- *.
        -- try rewrite tc_ctr_1. simpl. rewrite Hx. reflexivity.
        -- invert pos x.
Qed.

Lemma tc_inst_back : forall (rho : mm_instr (pos 2)) i v j w,
  (j, tc_ofvec w) = tc_exec (tc_conv rho) (i, tc_ofvec v) -> mma_sss rho (i, v) (j, w).
Proof.
  intros rho i v j w H.
  destruct (mma_sss_total_ni rho (i, v)) as [[j' w'] Hs].
  pose proof (tc_inst_forward rho i v j' w' Hs) as H2.
  rewrite <- H in H2.
  pose proof (f_equal fst H2) as E1. pose proof (f_equal snd H2) as E2. simpl in E1, E2. subst j'.
  apply tc_ofvec_inj in E2. subst w'. exact Hs.
Qed.

Definition tc_P (P : list (mm_instr (pos 2))) : list E.minsky := map tc_conv P.

Lemma tc_fetch_conv : forall (P : list (mm_instr (pos 2))) i,
  E.fetch (tc_P P) i = option_map tc_conv (E.fetch P i).
Proof. intros P i. unfold tc_P. apply E.fetch_map. Qed.

Lemma tc_step_iff : forall (P : list (mm_instr (pos 2))) i v j w,
  sss_step (@mma_sss 2) (1, P) (i, v) (j, w) <->
  E.mstep (tc_P P) (i, tc_ofvec v) = Some (j, tc_ofvec w).
Proof.
  intros P i v j w. split.
  - intros (k & l & rho & r & d & HP & Hst & Hs).
    injection HP as Hk HP. subst k. injection Hst as Hi Hd. subst d.
    assert (Hf : E.fetch (tc_P P) i = Some (tc_conv rho)).
    { rewrite tc_fetch_conv. rewrite HP. replace i with (S (length l)) by lia.
      simpl. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    rewrite (tc_mstep_fetch (tc_P P) (i, tc_ofvec v) (tc_conv rho)) by exact Hf.
    f_equal. symmetry. apply tc_inst_forward. exact Hs.
  - intro H. destruct (E.fetch (tc_P P) i) as [m |] eqn:Hf0.
    + pose proof Hf0 as Hf. rewrite tc_fetch_conv in Hf.
      destruct (E.fetch P i) as [rho |] eqn:Hr; [| discriminate].
      simpl in Hf. injection Hf as <-.
      rewrite (tc_mstep_fetch (tc_P P) (i, tc_ofvec v) (tc_conv rho) Hf0) in H.
      injection H as H. symmetry in H. apply tc_inst_back in H.
      destruct i as [| i]; [discriminate Hr |]. simpl in Hr.
      destruct (nth_error_split P i Hr) as [l [rest [-> Hl]]].
      exists 1, l, rho, rest, v. repeat split; [f_equal; lia | exact H].
    + rewrite (tc_mstep_none (tc_P P) (i, tc_ofvec v)) in H; [discriminate | exact Hf0].
Qed.

Inductive tc_steps (M : list E.minsky) : nat -> E.mconf -> E.mconf -> Prop :=
  | tc_steps_0 : forall c, tc_steps M 0 c c
  | tc_steps_S : forall n c c' c'', E.mstep M c = Some c' -> tc_steps M n c' c'' ->
                 tc_steps M (S n) c c''.

Lemma tc_steps_mrun : forall M n c c', tc_steps M n c c' -> E.mrun n M c = c'.
Proof.
  intros M n c c' H. induction H as [c | n c c' c'' Hs _ IH]; simpl; [reflexivity |].
  rewrite Hs. exact IH.
Qed.

Lemma tc_mrun_steps : forall M n c c', E.mrun n M c = c' -> E.mstep M c' = None ->
  exists m, m <= n /\ tc_steps M m c c'.
Proof.
  intros M n. induction n as [| n IH]; intros c c' Hr Hn; simpl in Hr.
  - subst c'. exists 0. split; [lia | apply tc_steps_0].
  - destruct (E.mstep M c) as [y |] eqn:Hs.
    + destruct (IH y c' Hr Hn) as [m [Hm Hst]]. exists (S m). split; [lia |].
      eapply tc_steps_S; eassumption.
    + subst c'. exists 0. split; [lia | apply tc_steps_0].
Qed.

Lemma tc_steps_app : forall M m n c c' c'', tc_steps M m c c' -> tc_steps M n c' c'' -> tc_steps M (m + n) c c''.
Proof.
  intros M m n c c' c'' H. induction H as [c | m c d e Hs _ IH]; intro H2; simpl; [exact H2 |].
  eapply tc_steps_S; [exact Hs | apply IH; exact H2].
Qed.

Lemma tc_steps_fwd : forall (P : list (mm_instr (pos 2))) n st st',
  sss_steps (@mma_sss 2) (1, P) n st st' ->
  tc_steps (tc_P P) n (fst st, tc_ofvec (snd st)) (fst st', tc_ofvec (snd st')).
Proof.
  intros P n st st' H. induction H as [st | n st1 st2 st3 Hs _ IH].
  - apply tc_steps_0.
  - destruct st1 as [i v], st2 as [j w]. apply tc_step_iff in Hs.
    eapply tc_steps_S; [exact Hs | exact IH].
Qed.

Lemma tc_steps_bwd : forall (P : list (mm_instr (pos 2))) n c c',
  tc_steps (tc_P P) n c c' -> forall i v j w,
  c = (i, tc_ofvec v) -> c' = (j, tc_ofvec w) ->
  sss_steps (@mma_sss 2) (1, P) n (i, v) (j, w).
Proof.
  intros P n c c' H. induction H as [c | n c c1 c2 Hs Ht IH]; intros i v j w Hc Hc'.
  - subst c. pose proof (f_equal fst Hc') as E1. pose proof (f_equal snd Hc') as E2. simpl in E1, E2.
    subst j. apply tc_ofvec_inj in E2. subst w. apply in_sss_steps_0.
  - destruct c1 as [j1 [a1 b1]].
    assert (Hs' : sss_step (@mma_sss 2) (1, P) (i, v) (j1, tc_tovec a1 b1)).
    { apply tc_step_iff. rewrite tc_ofvec_tovec. subst c. exact Hs. }
    eapply in_sss_steps_S; [exact Hs' |]. apply (IH j1 (tc_tovec a1 b1) j w); [reflexivity | exact Hc'].
Qed.

Lemma tc_steps_iff : forall (P : list (mm_instr (pos 2))) n i v j w,
  sss_steps (@mma_sss 2) (1, P) n (i, v) (j, w) <->
  tc_steps (tc_P P) n (i, tc_ofvec v) (j, tc_ofvec w).
Proof.
  intros P n i v j w. split.
  - intro H. exact (tc_steps_fwd P n _ _ H).
  - intro H. exact (tc_steps_bwd P n _ _ H i v j w eq_refl eq_refl).
Qed.

Lemma tc_fetch_none_iff : forall (P : list (mm_instr (pos 2))) j,
  E.fetch (tc_P P) j = None <-> out_code j (1, P).
Proof.
  intros P j. rewrite tc_fetch_conv. unfold out_code, code_start, code_end. simpl.
  destruct j as [| j]; simpl.
  - split; intros _; [left; lia | reflexivity].
  - destruct (nth_error P j) as [r |] eqn:Hn; simpl.
    + split; [discriminate |]. intros [H | H]; [lia |]. assert (Hl : nth_error P j <> None) by (rewrite Hn; discriminate). apply nth_error_Some in Hl. lia.
    + apply nth_error_None in Hn. split; [intros _; right; lia | intros _; reflexivity].
Qed.

Lemma tc_output_iff : forall (P : list (mm_instr (pos 2))) i v j w,
  sss_output (@mma_sss 2) (1, P) (i, v) (j, w) <->
  exists n, tc_steps (tc_P P) n (i, tc_ofvec v) (j, tc_ofvec w) /\
            E.mstep (tc_P P) (j, tc_ofvec w) = None.
Proof.
  intros P i v j w. unfold sss_output. split.
  - intros [[n Hn] Hout]. exists n. split.
    + apply tc_steps_iff. exact Hn.
    + apply tc_mstep_none. simpl. apply tc_fetch_none_iff. exact Hout.
  - intros [n [Hn Hst]]. split.
    + exists n. apply tc_steps_iff. exact Hn.
    + apply tc_fetch_none_iff. apply tc_mstep_none_iff in Hst. exact Hst.
Qed.

Lemma tc_terminates_iff : forall (P : list (mm_instr (pos 2))) i v,
  sss_terminates (@mma_sss 2) (1, P) (i, v) <->
  exists n c', tc_steps (tc_P P) n (i, tc_ofvec v) c' /\ E.mstep (tc_P P) c' = None.
Proof.
  intros P i v. unfold sss_terminates. split.
  - intros [[j w] Ho]. apply tc_output_iff in Ho. destruct Ho as [n [Hn Hs]].
    exists n, (j, tc_ofvec w). split; assumption.
  - intros [n [[j [a b]] [Hn Hs]]]. exists (j, tc_tovec a b). apply tc_output_iff.
    exists n. rewrite tc_ofvec_tovec. split; assumption.
Qed.

Lemma tc_nonterm_never_stops : forall (P : list (mm_instr (pos 2))) i v,
  ~ sss_terminates (@mma_sss 2) (1, P) (i, v) ->
  forall n, E.mstep (tc_P P) (E.mrun n (tc_P P) (i, tc_ofvec v)) <> None.
Proof.
  intros P i v Hnt n Hn. apply Hnt. apply tc_terminates_iff.
  destruct (tc_mrun_steps (tc_P P) n _ _ eq_refl Hn) as [m [_ Hm]].
  exists m, (E.mrun n (tc_P P) (i, tc_ofvec v)). split; assumption.
Qed.

Print Assumptions tc_output_iff.
Print Assumptions tc_nonterm_never_stops.
