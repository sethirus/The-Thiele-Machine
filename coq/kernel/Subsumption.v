From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Require Import Kernel.Kernel.
Require Import Kernel.KernelTM.
Require Import Kernel.KernelThiele.

Lemma Forall_nth_error'
  {A : Type} {P : A -> Prop} {l : list A} :
  Forall P l ->
  forall n x,
    nth_error l n = Some x ->
    P x.
Proof.
  intros H.
  induction H as [|y ys Hy Hys IH]; intros n x Hnth; simpl in *.
  - destruct n; inversion Hnth.
  - destruct n as [|n']; simpl in Hnth.
    + inversion Hnth; subst; assumption.
    + apply (IH n' x); assumption.
Qed.

Lemma fetch_turing :
  forall prog st,
    program_is_turing prog ->
    turing_instruction (fetch prog st) = true.
Proof.
  intros prog st Hprog.
  unfold fetch.
  destruct (nth_error prog st.(tm_state)) as [instr|] eqn:Hnth; simpl.
  - pose proof (@Forall_nth_error' instruction (fun instr => turing_instruction instr = true)
                 prog Hprog st.(tm_state) instr Hnth) as Hinst.
    exact Hinst.
  - reflexivity.
Qed.

Lemma step_tm_thiele_agree :
  forall prog st,
    turing_instruction (fetch prog st) = true ->
    step_tm prog st = step_thiele prog st.
Proof.
  intros prog st Hfetch.
  unfold step_tm, step_thiele.
  destruct (fetch prog st); simpl in *; try reflexivity.
  discriminate Hfetch.
Qed.

Theorem thiele_simulates_turing :
  forall fuel prog st,
    program_is_turing prog ->
    run_tm fuel prog st = run_thiele fuel prog st.
Proof.
  induction fuel as [|fuel IH]; intros prog st Hprog; simpl.
  - reflexivity.
  - pose proof (fetch_turing prog st Hprog) as Ht.
    pose proof (step_tm_thiele_agree prog st Ht) as Hstep.
    remember (fetch prog st) as instr eqn:Hfetch.
    destruct instr.
    + reflexivity.
    + simpl in Ht.
      specialize (IH prog (step_thiele prog st) Hprog).
      rewrite Hstep.
      exact IH.
    + simpl in Ht.
      specialize (IH prog (step_thiele prog st) Hprog).
      rewrite Hstep.
      exact IH.
    + simpl in Ht.
      specialize (IH prog (step_thiele prog st) Hprog).
      rewrite Hstep.
      exact IH.
    + simpl in Ht.
      exfalso.
      pose proof Bool.diff_false_true as Hdiff.
      exact (Hdiff Ht).
Qed.

Definition p_impossible : program := [H_ClaimTapeIsZero].

Definition initial_state : state :=
  {| tape := repeat true 3;
     head := 0;
     tm_state := 0;
     mu_cost := 0 |}.

Definition target_state : state :=
  {| tape := repeat false 3;
     head := 0;
     tm_state := 1;
     mu_cost := 1 |}.

Lemma run_tm_p_impossible :
  run_tm 1 p_impossible initial_state =
  {| tape := repeat true 3; head := 0; tm_state := 1; mu_cost := 0 |}.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma run_thiele_p_impossible :
  run_thiele 1 p_impossible initial_state = target_state.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem turing_is_strictly_contained :
  exists (p : program),
    run_tm 1 p initial_state <> target_state /\
    run_thiele 1 p initial_state = target_state.
Proof.
  exists p_impossible.
  split.
  - intro Hcontr.
    rewrite run_tm_p_impossible in Hcontr.
    discriminate Hcontr.
  - apply run_thiele_p_impossible.
Qed.
