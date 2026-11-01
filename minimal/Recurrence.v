(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file proves finite recurrence for an injective step from the step law and the pigeonhole, so a reversible finite machine keeps nothing; it imports only Minimal.StepLaw. *)
(* Reversible finite machines keep nothing: a bijective step on finitely many states brings every
   run back to its start. So any reading such a machine raises comes back down. This is Zermelo's
   recurrence in its finite form, proved from the step law and the pigeonhole. *)
Require Import List Arith Lia.
Require Import Minimal.StepLaw.
Import ListNotations.

Section Rec.
Variable X : Type.
Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.
Variable f : X -> X.
Hypothesis inj : forall a b, f a = f b -> a = b.
Variable all : list X.
Hypothesis all_nodup : NoDup all.
Hypothesis all_in : forall x, In x all.
Variable x0 : X.

Local Notation run := (StepLaw.run X f x0).

Lemma NoDup_snoc : forall (l : list X) a, NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
  induction l; intros b Hnd Hnin; simpl.
  - constructor. auto. constructor.
  - inversion Hnd; subst. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]]. contradiction. apply Hnin. simpl; auto.
    + apply IHl; auto. intro. apply Hnin. simpl; auto.
Qed.

Lemma nodup_or_collision : forall (g : nat -> X) m,
  NoDup (map g (seq 0 m)) \/ exists i j, i < j /\ j < m /\ g j = g i.
Proof.
  intros g m. induction m.
  - left. constructor.
  - rewrite seq_S, map_app. simpl.
    destruct (In_dec eq_dec (g m) (map g (seq 0 m))) as [Hin | Hnin].
    + right. apply in_map_iff in Hin. destruct Hin as [i [Hgi Hi]]. apply in_seq in Hi.
      exists i, m. split; [lia | split; [lia | auto]].
    + destruct IHm as [Hnd | [i [j [Hij [Hj Hg]]]]].
      * left. apply NoDup_snoc; auto.
      * right. exists i, j. split; [auto | split; [lia | auto]].
Qed.

(* the first length(all) + 1 states cannot all be distinct *)
Lemma some_revisit : exists i j, i < j /\ j <= length all /\ run j = run i.
Proof.
  destruct (nodup_or_collision run (S (length all))) as [Hnd | [i [j [Hij [Hj Hg]]]]].
  - exfalso. assert (incl (map run (seq 0 (S (length all)))) all) by (intros z _; apply all_in).
    pose proof (NoDup_incl_length Hnd H). rewrite map_length, seq_length in H0. lia.
  - exists i, j. split; [auto | split; [lia | auto]].
Qed.

(* with an injective step, the earliest revisit returns to the start, and then the run is periodic *)
Theorem returns_to_start : exists p, 0 < p /\ run p = x0.
Proof.
  destruct some_revisit as [i [j [Hij [Hj Heq]]]].
  (* cancel the injective step i times *)
  assert (forall k, k <= i -> run (j - k) = run (i - k)).
  { induction k; intro Hk. rewrite !Nat.sub_0_r. auto.
    assert (run (j - k) = run (i - k)) by (apply IHk; lia).
    replace (j - k) with (S (j - S k)) in H by lia. replace (i - k) with (S (i - S k)) in H by lia.
    simpl in H. apply inj in H. auto. }
  exists (j - i). split; [lia |].
  specialize (H i (le_n i)). rewrite Nat.sub_diag in H. exact H.
Qed.

(* consequence: no reading that is false at the start and never comes down can be raised by a reversible finite step *)
Theorem reversible_keeps_nothing : forall (reading : X -> bool),
  reading x0 = false -> (forall x, reading x = true -> reading (f x) = true) ->
  forall k, reading (run k) = false.
Proof.
  intros reading H0 Hperm k.
  destruct returns_to_start as [p [Hp Hret]].
  destruct (reading (run k)) eqn:E; auto. exfalso.
  (* from k, the reading stays true forever; but run (k + (p - k mod p)) hits a multiple of p, i.e. x0 *)
  assert (Hstay : forall m, reading (run (k + m)) = true).
  { induction m. rewrite Nat.add_0_r. auto. replace (k + S m) with (S (k + m)) by lia. simpl. apply Hperm. auto. }
  assert (Hper : forall q, run (q * p) = x0).
  { induction q. reflexivity. replace (S q * p) with (p + q * p) by lia.
    (* run (p + m) = run m when run p = x0: shift by a period from the start *)
    assert (forall m, run (p + m) = run m).
    { intro m. induction m. rewrite Nat.add_0_r. auto.
      replace (p + S m) with (S (p + m)) by lia. simpl. rewrite IHm. reflexivity. }
    rewrite H. auto. }
  assert (Hkp : k <= k * p) by nia.
  specialize (Hstay (k * p - k)). replace (k + (k * p - k)) with (k * p) in Hstay by lia.
  rewrite Hper in Hstay. congruence.
Qed.
End Rec.
