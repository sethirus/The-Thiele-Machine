(** PayFree: what the small machine can bill while its flag stays down.

    The small machine of EarnedCore.v has no PAY. Its only paid
    instructions are CHECK, COMMIT and CERTIFY. Take any run that never
    traps and ends with the flag down. Then no CERTIFY ran (a passing one
    raises the flag, a failing one traps), every CHECK passed and took a
    table entry (at most sixteen), and every COMMIT committed a claim the
    table holds about its counter's current version. So the run bills at
    most 32, plus one for each COMMIT of a claim the run had already
    committed ([pf_bound]). A claim names its counter's version, and a
    version changes at every write, so a repeated COMMIT happens only while
    its counter has gone unwritten since the earlier one.

    - [pf_bound]: total cost <= (16 - table entries at the start) + 16 +
      the number of repeated COMMITs.
    - [pf_bound_start]: from a start, total cost <= 32 + the number of
      repeated COMMITs.
    - [pf_no_repeat_bound]: a run with no repeated COMMIT bills at most 32
      before its flag goes up.

    That is the job PAY does in the universal program U_P: a guest whose
    moves write its counters has to bill each move's price with the flag
    down, and without PAY it runs out after 32. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(** The COMMITs of a run that repeat a claim it already committed. *)
Fixpoint pf_rep (tr : list E.instr) (s : E.state) (seen : list E.fact) : nat :=
  match tr with
  | [] => 0
  | i :: r =>
      match i with
      | E.COMMIT p c =>
          let f := E.claim (E.core_of s) p c in
          (if existsb (E.fact_eqb f) seen then 1 else 0) + pf_rep r (E.exec s i) (f :: seen)
      | _ => pf_rep r (E.exec s i) seen
      end
  end.

Lemma pf_err_latch : forall tr s, E.err (E.core_of s) = true -> E.err (E.core_of (E.run tr s)) = true.
Proof.
  induction tr as [| i tr IH]; intros s H; [exact H |].
  simpl. apply IH. unfold E.exec, E.cexec. simpl. rewrite H. exact H.
Qed.

Lemma pf_cert_latch : forall tr s, E.cert s = true -> E.cert (E.run tr s) = true.
Proof.
  induction tr as [| i tr IH]; intros s H; [exact H |].
  simpl. apply IH. unfold E.exec. simpl. rewrite H. reflexivity.
Qed.

Lemma pf_existsb_in : forall f l, existsb (E.fact_eqb f) l = true <-> In f l.
Proof.
  intros f l. rewrite existsb_exists. split.
  - intros [g [Hg Hfg]]. apply E.fact_eqb_eq in Hfg. subst. exact Hg.
  - intro H. exists f. split; [exact H | apply E.fact_eqb_eq; reflexivity].
Qed.

Lemma pf_step : forall s i, E.err (E.core_of s) = false -> E.err (E.core_of (E.exec s i)) = false ->
  match i with
  | E.CHECK p c => E.facts (E.core_of (E.exec s i)) = E.claim (E.core_of s) p c :: E.facts (E.core_of s) /\
                   length (E.facts (E.core_of s)) < E.fact_cap
  | E.COMMIT p c => E.facts (E.core_of (E.exec s i)) = E.facts (E.core_of s) /\
                    In (E.claim (E.core_of s) p c) (E.facts (E.core_of s))
  | E.CERTIFY => E.cert (E.exec s i) = true
  | _ => E.facts (E.core_of (E.exec s i)) = E.facts (E.core_of s)
  end.
Proof.
  intros s i He He'. unfold E.exec in *. cbn [E.core_of E.cert] in *.
  unfold E.cexec in *. rewrite He in *.
  destruct i as [c | c j | | p c | p c | ].
  - destruct c; reflexivity.
  - destruct (E.val (E.core_of s) c); [reflexivity | destruct c; reflexivity].
  - reflexivity.
  - destruct (E.check_ok (E.core_of s) p c) eqn:Hok; [| discriminate].
    split; [reflexivity |]. unfold E.check_ok in Hok. rewrite He in Hok.
    apply andb_prop in Hok as [_ Hl]. apply Nat.ltb_lt. exact Hl.
  - destruct (E.commit_ok (E.core_of s) p c) eqn:Hok; [| discriminate].
    split; [reflexivity |]. unfold E.commit_ok in Hok. rewrite He in Hok.
    apply pf_existsb_in. exact Hok.
  - unfold E.fires. destruct (E.certify_ok (E.core_of s)) eqn:Hok; [| discriminate].
    rewrite orb_true_r. reflexivity.
Qed.

Lemma pf_err_before : forall tr s, E.err (E.core_of (E.run tr s)) = false -> E.err (E.core_of s) = false.
Proof.
  intros tr s H. destruct (E.err (E.core_of s)) eqn:He; [| reflexivity].
  rewrite (pf_err_latch tr s He) in H. exact H.
Qed.

Lemma pf_rep_same : forall tr s l1 l2, (forall x, In x l1 <-> In x l2) -> pf_rep tr s l1 = pf_rep tr s l2.
Proof.
  induction tr as [| i tr IH]; intros s l1 l2 H; [reflexivity |].
  destruct i; cbn [pf_rep]; try (apply IH; exact H).
  set (f := E.claim (E.core_of s) p c).
  assert (Hb : existsb (E.fact_eqb f) l1 = existsb (E.fact_eqb f) l2).
  { destruct (existsb (E.fact_eqb f) l1) eqn:H1, (existsb (E.fact_eqb f) l2) eqn:H2; try reflexivity.
    - apply pf_existsb_in, H in H1. apply pf_existsb_in in H1. congruence.
    - apply pf_existsb_in, H in H2. apply pf_existsb_in in H2. congruence. }
  rewrite Hb. f_equal. apply IH. intro x. simpl. rewrite H. tauto.
Qed.

Theorem pf_bound : forall tr s seen,
  length (E.facts (E.core_of s)) <= E.fact_cap -> NoDup seen -> incl seen (E.facts (E.core_of s)) ->
  E.err (E.core_of (E.run tr s)) = false -> E.cert (E.run tr s) = false ->
  E.total_cost tr <= (E.fact_cap - length (E.facts (E.core_of s))) + (E.fact_cap - length seen) + pf_rep tr s seen.
Proof.
  induction tr as [| i tr IH]; intros s seen Hlen Hnd Hinc Herr Hcert; [simpl; lia |].
  cbn [E.run] in Herr, Hcert.
  pose proof (pf_err_before tr _ Herr) as He'.
  pose proof (pf_err_before [i] s) as He. cbn [E.run] in He. specialize (He He').
  pose proof (pf_step s i He He') as St.
  assert (Hseen : length seen <= length (E.facts (E.core_of s))) by (apply NoDup_incl_length; assumption).
  destruct i as [c | c j | | p c | p c | ]; cbn [E.total_cost E.cost pf_rep].
  - pose proof (IH _ seen ltac:(rewrite St; exact Hlen) Hnd ltac:(rewrite St; exact Hinc) Herr Hcert) as H.
    rewrite St in H. lia.
  - pose proof (IH _ seen ltac:(rewrite St; exact Hlen) Hnd ltac:(rewrite St; exact Hinc) Herr Hcert) as H.
    rewrite St in H. lia.
  - pose proof (IH _ seen ltac:(rewrite St; exact Hlen) Hnd ltac:(rewrite St; exact Hinc) Herr Hcert) as H.
    rewrite St in H. lia.
  - destruct St as [Hf Hl].
    assert (Hinc' : incl seen (E.facts (E.core_of (E.exec s (E.CHECK p c))))).
    { rewrite Hf. intros x Hx. right. apply Hinc. exact Hx. }
    pose proof (IH _ seen ltac:(rewrite Hf; cbn [length]; lia) Hnd Hinc' Herr Hcert) as H.
    rewrite Hf in H. cbn [length] in H. lia.
  - destruct St as [Hf Hin].
    set (f := E.claim (E.core_of s) p c) in *.
    destruct (existsb (E.fact_eqb f) seen) eqn:Hex.
    + (* a repeat *)
      apply pf_existsb_in in Hex.
      assert (Hinc' : incl (f :: seen) (E.facts (E.core_of (E.exec s (E.COMMIT p c))))).
      { rewrite Hf. intros x [<- | Hx]; [exact Hin | apply Hinc; exact Hx]. }
      (* the repeat leaves the set of committed claims as it was *)
      pose proof (IH _ seen ltac:(rewrite Hf; exact Hlen) Hnd ltac:(rewrite Hf; exact Hinc) Herr Hcert) as H.
      rewrite (pf_rep_same tr _ (f :: seen) seen) by (intro x; simpl; split; [intros [<- | X]; assumption | tauto]).
      rewrite Hf in H. lia.
    + (* a new claim *)
      assert (Hnot : ~ In f seen) by (intro X; apply pf_existsb_in in X; congruence).
      assert (Hinc' : incl (f :: seen) (E.facts (E.core_of (E.exec s (E.COMMIT p c))))).
      { rewrite Hf. intros x [<- | Hx]; [exact Hin | apply Hinc; exact Hx]. }
      assert (Hlen2 : length (f :: seen) <= length (E.facts (E.core_of s))).
      { apply NoDup_incl_length; [constructor; assumption | rewrite <- Hf; exact Hinc']. }
      pose proof (IH _ (f :: seen) ltac:(rewrite Hf; exact Hlen) (NoDup_cons f Hnot Hnd) Hinc' Herr Hcert) as H.
      rewrite Hf in H. cbn [length] in H, Hlen2. lia.
  - exfalso. rewrite (pf_cert_latch tr _ St) in Hcert. discriminate.
Qed.

(** From a start with an empty table and nothing committed. *)
Theorem pf_bound_start : forall tr a b,
  E.err (E.core_of (E.run tr (E.start a b))) = false -> E.cert (E.run tr (E.start a b)) = false ->
  E.total_cost tr <= 2 * E.fact_cap + pf_rep tr (E.start a b) [].
Proof.
  intros tr a b He Hc.
  assert (H0 : length (E.facts (E.core_of (E.start a b))) = 0) by reflexivity.
  pose proof (pf_bound tr (E.start a b) [] ltac:(rewrite H0; unfold E.fact_cap; lia)
    (NoDup_nil _) (fun x H => match H with end) He Hc) as H.
  rewrite H0 in H. cbn [length] in H. lia.
Qed.

(** A run with no repeated COMMIT bills at most 32 while its flag stays
    down. *)
Theorem pf_no_repeat_bound : forall tr a b,
  E.err (E.core_of (E.run tr (E.start a b))) = false -> E.cert (E.run tr (E.start a b)) = false ->
  pf_rep tr (E.start a b) [] = 0 -> E.total_cost tr <= 32.
Proof.
  intros tr a b He Hc H0. pose proof (pf_bound_start tr a b He Hc) as H.
  rewrite H0 in H. unfold E.fact_cap in H. lia.
Qed.

Print Assumptions pf_bound.
Print Assumptions pf_no_repeat_bound.
