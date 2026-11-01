From Coq Require Import List Bool Arith Lia.
From Minimal Require Import EarnedCore.
Import ListNotations.

(* If every observed state is also represented by a horizontally stopped
   state, a deterministic autonomous shadow cannot move. *)
Section General.
  Context {S B I : Type}.
  Variable view : S -> B.
  Variable step : I -> S -> S.
  Variable next : I -> B -> B.
  Hypothesis projects : forall i s, view (step i s) = next i (view s).
  Hypothesis stopped_representative : forall s, exists t,
    view t = view s /\ forall i, step i t = t.

  Theorem stopped_representatives_force_static_shadow : forall i s,
    next i (view s) = view s.
  Proof.
    intros i s; destruct (stopped_representative s) as [t [E Hstop]].
    rewrite <- E, <- projects, Hstop; reflexivity.
  Qed.
End General.

Module Native.
  Definition free (i : instr) := cost i = 0.

  Lemma free_cannot_fire : forall i k, free i -> fires k i = false.
  Proof. intros i k H; destruct i; simpl in H; try discriminate; reflexivity. Qed.

  Lemma trapped_free_step_is_full_identity : forall s i,
    err (core_of s) = true -> free i -> exec s i = s.
  Proof.
    intros [k m r] i Herr Hfree.
    unfold exec; simpl in *.
    unfold cexec; rewrite Herr.
    rewrite (free_cannot_fire i k Hfree), orb_false_r.
    unfold free in Hfree; rewrite Hfree, Nat.add_0_r; reflexivity.
  Qed.

  Definition bad_check (s : state) := CHECK (PGe (S (ca (core_of s)))) CA.

  Lemma chosen_check_fails : forall s,
    check_ok (core_of s) (PGe (S (ca (core_of s)))) CA = false.
  Proof.
    intro s; unfold check_ok, eval, val.
    assert (Nat.leb (S (ca (core_of s))) (ca (core_of s)) = false) as H.
    { apply Nat.leb_gt; lia. }
    rewrite H, andb_false_r; reflexivity.
  Qed.

  Lemma chosen_check_reaches_trap : forall s,
    err (core_of (exec s (bad_check s))) = true.
  Proof.
    intro s; unfold bad_check; rewrite base_blind.
    unfold cexec; destruct (err (core_of s)) eqn:E; [exact E|].
    rewrite chosen_check_fails; reflexivity.
  Qed.

  Section AnyProjection.
    Context {B : Type}.
    Variable view : state -> B.
    Variable next : instr -> B -> B.
    Hypothesis horizontal_projects : forall i s,
      free i -> view (exec s i) = next i (view s).
    Hypothesis checks_silent : forall s p c,
      view (exec s (CHECK p c)) = view s.

    Theorem every_free_shadow_step_is_identity : forall i s,
      free i -> next i (view s) = view s.
    Proof.
      intros i s Hi.
      pose proof (checks_silent s (PGe (S (ca (core_of s)))) CA) as Hsame.
      change (view (exec s (bad_check s)) = view s) in Hsame.
      rewrite <- Hsame, <- (horizontal_projects i (exec s (bad_check s)) Hi).
      rewrite trapped_free_step_is_full_identity;
        [reflexivity|apply chosen_check_reaches_trap|exact Hi].
    Qed.

    Theorem every_free_execution_is_invisible : forall i s,
      free i -> view (exec s i) = view s.
    Proof.
      intros i s Hi; rewrite horizontal_projects by exact Hi.
      apply every_free_shadow_step_is_identity; exact Hi.
    Qed.

    Theorem every_free_program_is_invisible : forall word s,
      Forall free word -> view (run word s) = view s.
    Proof.
      induction word as [|i rest IH]; intros s H; [reflexivity|].
      inversion H; subst; simpl; rewrite IH by assumption.
      apply every_free_execution_is_invisible; assumption.
    Qed.

    Theorem onto_shadow_has_only_identity_free_steps :
      (forall b, exists s, view s = b) ->
      forall i b, free i -> next i b = b.
    Proof.
      intros Honto i b Hi; destruct (Honto b) as [s <-].
      apply every_free_shadow_step_is_identity; assumption.
    Qed.

    Theorem cannot_preserve_a_changing_horizontal_observation :
      ~ exists i s, free i /\ view (exec s i) <> view s.
    Proof.
      intros [i [s [Hi Hchange]]]; apply Hchange.
      apply every_free_execution_is_invisible; assumption.
    Qed.
  End AnyProjection.

  Definition reachable (initial s : state) := exists word, run word initial = s.

  Lemma reachable_after_instruction : forall initial s i,
    reachable initial s -> reachable initial (exec s i).
  Proof.
    intros initial s i [word <-]; exists (word ++ [i]); apply run_snoc.
  Qed.

  Section ReachableProjection.
    Context {B : Type}.
    Variable initial : state.
    Variable view : state -> B.
    Variable next : instr -> B -> B.
    Hypothesis horizontal_projects_reachable : forall i s,
      reachable initial s -> free i -> view (exec s i) = next i (view s).
    Hypothesis checks_silent_reachable : forall s p c,
      reachable initial s -> view (exec s (CHECK p c)) = view s.

    Theorem reachable_free_step_is_invisible : forall i s,
      reachable initial s -> free i -> view (exec s i) = view s.
    Proof.
      intros i s Hr Hi.
      pose proof (checks_silent_reachable s (PGe (S (ca (core_of s)))) CA Hr) as Hsame.
      change (view (exec s (bad_check s)) = view s) in Hsame.
      assert (Ht : reachable initial (exec s (bad_check s)))
        by (apply reachable_after_instruction; exact Hr).
      rewrite (horizontal_projects_reachable i s Hr Hi), <- Hsame,
        <- (horizontal_projects_reachable i (exec s (bad_check s)) Ht Hi).
      rewrite trapped_free_step_is_full_identity;
        [reflexivity|apply chosen_check_reaches_trap|exact Hi].
    Qed.

    Theorem reachable_free_program_is_invisible : forall word s,
      reachable initial s -> Forall free word -> view (run word s) = view s.
    Proof.
      induction word as [|i rest IH]; intros s Hr Hword; [reflexivity|].
      inversion Hword; subst; simpl.
      rewrite IH; [apply reachable_free_step_is_invisible; assumption| |assumption].
      apply reachable_after_instruction; exact Hr.
    Qed.
  End ReachableProjection.

  (* Collapse of computation is not necessarily collapse to a single point:
     the original certificate is a nonconstant, static quotient. *)
  Theorem certificate_is_a_silent_static_quotient :
    (forall s p c, cert (exec s (CHECK p c)) = cert s) /\
    (forall i s, free i -> cert (exec s i) = cert s) /\
    (forall b : bool, exists s, cert s = b).
  Proof.
    split.
    - intros; simpl; apply orb_false_r.
    - split.
      + intros i s Hi; rewrite cert_latch, (free_cannot_fire i (core_of s) Hi).
        apply orb_false_r.
      + intro b; exists (mkst (start_core 0 0) 0 b); reflexivity.
  Qed.

  Theorem certificate_differs_on_reachable_clean_runs :
    cert (run [] (start 0 0)) = false /\
    cert (run earned_run (start 0 0)) = true.
  Proof. vm_compute; split; reflexivity. Qed.
End Native.
