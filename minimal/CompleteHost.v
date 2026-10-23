(* SCOPE NOTE: standalone proof scope.
   Proves holding and collision bounds for total maps with a supplied observation and permanent held region.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List ListDec Arith Lia Bool.
Import ListNotations.

Fixpoint iter {X : Type} (F : X -> X) (n : nat) (s : X) : X :=
  match n with 0 => s | S k => F (iter F k s) end.

Lemma iter_add {X : Type} (F : X -> X) : forall n m s,
  iter F (n+m) s = iter F n (iter F m s).
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iter_succ_from {X : Type} (F : X -> X) : forall n s,
  iter F (S n) s=iter F n (F s).
Proof.
  induction n; intros s; [reflexivity |].
  change (F (iter F (S n) s)=F (iter F n (F s))).
  f_equal; apply IHn.
Qed.

Lemma nodup_map_on {X Y : Type} (f : X -> Y) : forall l,
  NoDup l ->
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros Hnd Hinj; simpl; [constructor |].
  inversion Hnd as [|? ? Hnot Htail]; subst. constructor.
  - rewrite in_map_iff. intros [b [He Hb]].
    assert (b=a) by (apply Hinj; simpl; auto). subst; contradiction.
  - apply IH; [assumption |]. intros; apply Hinj; simpl; auto.
Qed.

Section Holding.
  Context {X : Type} (F : X -> X) (H : X -> Prop) (entry : X).
  Hypothesis outside : ~ H entry.
  Hypothesis enters : H (F entry).
  Hypothesis closed : forall s, H s -> H (F s).

  Lemma positive_iter_held : forall n, H (iter F (S n) entry).
  Proof. induction n; simpl; [exact enters | apply closed; exact IHn]. Qed.

  Definition retains (L : nat) := forall i j,
    i < L -> j < L ->
    F (iter F i entry) = F (iter F j entry) -> iter F i entry = iter F j entry.

  Theorem held_prefix_distinct : forall L, retains L -> forall i j,
    i <= L -> j <= L -> iter F i entry = iter F j entry -> i=j.
  Proof.
    intros L Hr i; induction i as [|i IH]; intros j Hi Hj E; destruct j as [|j].
    - reflexivity.
    - change (entry = iter F (S j) entry) in E.
      exfalso; apply outside. rewrite E. apply positive_iter_held.
    - change (iter F (S i) entry = entry) in E.
      exfalso; apply outside. rewrite <- E. apply positive_iter_held.
    - f_equal. apply IH; try lia. apply Hr; try lia. exact E.
  Qed.

  Theorem held_prefix_capacity : forall L held,
    retains L -> (forall s, H s -> In s held) -> L <= length held.
  Proof.
    intros L held Hr Hcover.
    set (nodes := map (fun n => iter F (S n) entry) (seq 0 L)).
    assert (Hnd : NoDup nodes).
    { unfold nodes. apply nodup_map_on; [apply seq_NoDup |].
      intros a b Ha Hb E. apply in_seq in Ha. apply in_seq in Hb.
      assert (S a=S b) by (eapply held_prefix_distinct; eauto; lia). lia. }
    assert (Hinc : incl nodes held).
    { intros s Hs. apply in_map_iff in Hs as [n [<- Hn]].
      apply Hcover; apply positive_iter_held. }
    pose proof (NoDup_incl_length Hnd Hinc) as Hlen.
    unfold nodes in Hlen. rewrite map_length, seq_length in Hlen. exact Hlen.
  Qed.

  Theorem injective_host_fresh_forever :
    (forall a b, F a=F b -> a=b) ->
    forall i j, iter F i entry=iter F j entry -> i=j.
  Proof.
    intros Hinj i j E. eapply (held_prefix_distinct (i+j)); try lia; [|exact E].
    unfold retains; intros; apply Hinj; assumption.
  Qed.

  Theorem finite_held_region_not_injective : forall held,
    (forall s, H s -> In s held) -> ~ (forall a b, F a=F b -> a=b).
  Proof.
    intros held Hcover Hinj.
    assert (Hr : retains (S (length held))) by (unfold retains; intros; apply Hinj; assumption).
    pose proof (held_prefix_capacity _ held Hr Hcover). lia.
  Qed.

  (* A constructive collision witness localized to entry plus the held set.
     It need not include entry itself. *)
  Theorem finite_hold_collision
      (eq_dec : forall a b : X, {a=b}+{a<>b}) : forall held,
    NoDup held -> (forall s, In s held <-> H s) ->
    exists a b, In a (entry::held) /\ In b (entry::held) /\ a<>b /\ F a=F b.
  Proof.
    intros held Hnd Hspec.
    set (domain := entry::held).
    set (bad := fun ab : X*X => fst ab <> snd ab /\ F (fst ab)=F (snd ab)).
    assert (Hdec : forall ab, {bad ab}+{~bad ab}).
    { intros [a b]; unfold bad; simpl.
      destruct (eq_dec a b); destruct (eq_dec (F a) (F b)); intuition. }
    destruct (Exists_dec bad (list_prod domain domain) Hdec) as [Hex|Hnone].
    - apply Exists_exists in Hex as [[a b] [Hab Hbad]].
      apply in_prod_iff in Hab. exists a,b. unfold bad in Hbad; simpl in Hbad.
      tauto.
    - assert (Hinj : forall a b, In a domain -> In b domain -> F a=F b -> a=b).
      { intros a b Ha Hb E. destruct (eq_dec a b); [assumption |]. exfalso.
        apply Hnone. apply Exists_exists. exists (a,b). split.
        - apply in_prod_iff; auto.
        - unfold bad; simpl; auto. }
      assert (Hdom : NoDup domain).
      { unfold domain. constructor; [intro He; apply outside; apply Hspec; exact He | assumption]. }
      assert (Hmap : NoDup (map F domain)) by (apply nodup_map_on; assumption).
      assert (Hinc : incl (map F domain) held).
      { intros s Hs. apply in_map_iff in Hs as [x [<- Hx]].
        apply Hspec. destruct Hx as [<-|Hx]; [exact enters |].
        apply closed; apply Hspec; exact Hx. }
      pose proof (NoDup_incl_length Hmap Hinc) as Hlen.
      rewrite map_length in Hlen. unfold domain in Hlen. simpl in Hlen. lia.
  Qed.

  Theorem finite_hold_run_collision
      (eq_dec : forall a b : X, {a=b}+{a<>b}) : forall hs,
    (forall s, H s -> In s hs) ->
    exists a b,
      In a (map (fun n => iter F n entry) (seq 0 (S (length hs)))) /\
      In b (map (fun n => iter F n entry) (seq 0 (S (length hs)))) /\
      a<>b /\ F a=F b.
  Proof.
    intros hs Hcover.
    set (domain := map (fun n => iter F n entry) (seq 0 (S (length hs)))).
    set (bad := fun ab : X*X => fst ab <> snd ab /\ F (fst ab)=F (snd ab)).
    assert (Hdec : forall ab, {bad ab}+{~bad ab}).
    { intros [a b]; unfold bad; simpl.
      destruct (eq_dec a b); destruct (eq_dec (F a) (F b)); intuition. }
    destruct (Exists_dec bad (list_prod domain domain) Hdec) as [Hex|Hnone].
    - apply Exists_exists in Hex as [[a b] [Hab Hbad]]. apply in_prod_iff in Hab.
      exists a,b. unfold bad in Hbad; simpl in Hbad; tauto.
    - assert (Hr : retains (S (length hs))).
      { intros i j Hi Hj E. destruct (eq_dec (iter F i entry) (iter F j entry)); [assumption |].
        exfalso; apply Hnone; apply Exists_exists.
        exists (iter F i entry,iter F j entry); split.
        - apply in_prod_iff; split; unfold domain; apply in_map_iff.
          + exists i; split; [reflexivity | apply in_seq; lia].
          + exists j; split; [reflexivity | apply in_seq; lia].
        - unfold bad; simpl; auto. }
      pose proof (held_prefix_capacity _ hs Hr Hcover); lia.
  Qed.
End Holding.

Theorem preparation_capacity {X : Type} (prepare : X -> X) : forall inputs outputs,
  NoDup inputs ->
  (forall a b, In a inputs -> In b inputs -> prepare a=prepare b -> a=b) ->
  (forall s, In s inputs -> In (prepare s) outputs) -> length inputs <= length outputs.
Proof.
  intros inputs outputs Hnd Hinj Himage.
  assert (Hmap : NoDup (map prepare inputs)) by (apply nodup_map_on; assumption).
  assert (Hincl : incl (map prepare inputs) outputs).
  { intros y Hy; apply in_map_iff in Hy as [s [<- Hs]]; apply Himage; assumption. }
  pose proof (NoDup_incl_length Hmap Hincl) as Hlen. rewrite map_length in Hlen; assumption.
Qed.

Section GuestHost.
  Context {G X : Type}.
  Variable delta : G -> option G.
  Variable trace : nat -> G.
  Variable F : X -> X.
  (* None denotes a host state outside the guest's execution phase. *)
  Variable view : X -> option G.
  Variable start : X.
  Variable k : nat. (* guest halts after T=S k transitions *)
  Hypothesis trace_steps : forall n, n < S k -> delta (trace n)=Some (trace (S n)).
  Hypothesis terminal : delta (trace (S k))=None.
  Hypothesis loaded : view start=Some (trace 0).
  Hypothesis simulates : forall s c d,
    view s=Some c -> delta c=Some d -> view (F s)=Some d.
  Hypothesis holds : forall s, view s=Some (trace (S k)) ->
    view (F s)=Some (trace (S k)).

  Theorem projected_guest_trace : forall n, n <= S k ->
    view (iter F n start)=Some (trace n).
  Proof.
    induction n; intros Hn; simpl; [exact loaded |].
    eapply simulates; [apply IHn; lia | apply trace_steps; lia].
  Qed.

  Lemma guest_not_halted_early : forall n, n < S k -> trace n <> trace (S k).
  Proof.
    intros n Hn E. pose proof (trace_steps n Hn) as H.
    rewrite E, terminal in H. discriminate.
  Qed.

  Definition held (s : X) := view s=Some (trace (S k)).
  Definition last_running := iter F k start.

  Lemma last_running_outside : ~ held last_running.
  Proof.
    unfold held, last_running. rewrite projected_guest_trace by lia.
    intro E; injection E as E. apply (guest_not_halted_early k); [lia|exact E].
  Qed.
  Lemma last_running_enters : held (F last_running).
  Proof. unfold held,last_running. apply (projected_guest_trace (S k)); lia. Qed.
  Lemma held_closed : forall s, held s -> held (F s).
  Proof. exact holds. Qed.

  Theorem completed_trace_stays_visible : forall n,
    view (iter F n (iter F (S k) start))=Some (trace (S k)).
  Proof.
    induction n; simpl.
    - exact (projected_guest_trace (S k) (Nat.le_refl _)).
    - apply holds; assumption.
  Qed.

  Theorem all_time_projection : forall n,
    view (iter F n start)=Some (trace (Nat.min n (S k))).
  Proof.
    intro n; destruct (le_dec n (S k)) as [Hn|Hn].
    - rewrite Nat.min_l by lia; apply projected_guest_trace; assumption.
    - rewrite Nat.min_r by lia.
      replace n with ((n-S k)+S k) at 1 by lia.
      rewrite iter_add; apply completed_trace_stays_visible.
  Qed.

  Theorem prepared_execution_prefix : forall pre,
    view pre=None -> F pre=start ->
    view pre=None /\ forall n, n <= S k ->
      view (iter F (S n) pre)=Some (trace n).
  Proof.
    intros pre Hnone Hprep; split; [assumption |].
    intros n Hn. rewrite iter_succ_from, Hprep. apply projected_guest_trace; assumption.
  Qed.

  Theorem cropped_frame_finite_hold
      (eq_dec : forall a b : X, {a=b}+{a<>b}) : forall hs,
    NoDup hs -> (forall s, In s hs <-> held s) ->
    (forall n, n <= S k -> view (iter F n start)=Some (trace n)) /\
    (exists a b, In a (last_running::hs) /\ In b (last_running::hs) /\ a<>b /\ F a=F b).
  Proof.
    intros hs Hnd Hspec; split; [exact projected_guest_trace |].
    eapply finite_hold_collision; eauto using last_running_outside,last_running_enters,held_closed.
  Qed.

  Theorem cropped_frame_injective_hold :
    (forall a b, F a=F b -> a=b) ->
    forall i j, iter F i last_running=iter F j last_running -> i=j.
  Proof.
    apply injective_host_fresh_forever with (H:=held);
      auto using last_running_outside,last_running_enters,held_closed.
  Qed.

  Theorem cropped_frame_holding_capacity : forall L hs,
    retains F last_running L ->
    (forall s, held s -> In s hs) -> L <= length hs.
  Proof.
    eapply held_prefix_capacity;
      eauto using last_running_outside,last_running_enters,held_closed.
  Qed.

  Theorem complete_host_finite
      (eq_dec : forall a b : X, {a=b}+{a<>b}) : forall pre hs,
    view pre=None -> F pre=start -> NoDup hs -> (forall s, In s hs <-> held s) ->
    (view pre=None /\ forall n, n <= S k -> view (iter F (S n) pre)=Some (trace n)) /\
    (exists a b, In a (last_running::hs) /\ In b (last_running::hs) /\ a<>b /\ F a=F b).
  Proof.
    intros pre hs Hnone Hprep Hnd Hspec; split.
    - apply prepared_execution_prefix; assumption.
    - exact (proj2 (cropped_frame_finite_hold eq_dec hs Hnd Hspec)).
  Qed.

  Theorem completed_view_cannot_decode_time :
    ~ exists decode : option G -> nat, forall n,
      decode (view (iter F n (iter F (S k) start)))=n.
  Proof.
    intros [decode Hd]. pose proof (Hd 0) as H0; pose proof (Hd 1) as H1.
    rewrite completed_trace_stays_visible in H0,H1. congruence.
  Qed.
End GuestHost.

(* Full-state preparation need not collide: its target is not invariant. *)
Inductive Four := Prep | Running | Held1 | Held2.
Definition delayed (s : Four) :=
  match s with Prep => Running | Running => Held1 | Held1 => Held2 | Held2 => Held2 end.
Definition done4 (s : Four) := match s with Held1 | Held2 => true | _ => false end.
Theorem preparation_has_unique_preimage : forall s, delayed s=Running -> s=Prep.
Proof. destruct s; simpl; intros; congruence. Qed.
Theorem first_halt_has_unique_preimage : forall s, delayed s=Held1 -> s=Running.
Proof. destruct s; simpl; intros; congruence. Qed.
Theorem delayed_collision_in_held_region :
  Held1<>Held2 /\ delayed Held1=delayed Held2 /\ done4 Held1=true /\ done4 Held2=true.
Proof. repeat split; discriminate || reflexivity. Qed.
Theorem start_membership_not_permanent : delayed Prep=Running /\ delayed Running<>Running.
Proof. split; discriminate || reflexivity. Qed.

Theorem retaining_program_preserves_injectivity {P C : Type} (g : P -> C -> C) :
  (forall p x y, g p x=g p y -> x=y) ->
  forall a b : P*C, (fst a,g (fst a) (snd a))=(fst b,g (fst b) (snd b)) -> a=b.
Proof.
  intros Hinj [p x] [q y] E; simpl in E. injection E as Ep Ec.
  subst q. f_equal. apply (Hinj p); assumption.
Qed.

Theorem reusable_toggle_is_injective : forall a b, negb a=negb b -> a=b.
Proof. destruct a,b; simpl; intros; congruence. Qed.
Theorem reusable_toggle_returns : forall a, negb (negb a)=a.
Proof. destruct a; reflexivity. Qed.

Theorem constant_view_cannot_recover_full_state {X O : Type}
    (q : X -> O) (a b : X) : a<>b -> q a=q b ->
    ~ exists decode : O -> X, forall s, decode (q s)=s.
Proof. intros Hneq Heq [d Hd]; apply Hneq; rewrite <- (Hd a), <- (Hd b), Heq; reflexivity. Qed.

Print Assumptions cropped_frame_finite_hold.
Print Assumptions cropped_frame_injective_hold.
Print Assumptions cropped_frame_holding_capacity.
Print Assumptions completed_trace_stays_visible.
Print Assumptions finite_hold_collision.
Print Assumptions held_prefix_capacity.
Print Assumptions finite_held_region_not_injective.
Print Assumptions preparation_has_unique_preimage.
Print Assumptions first_halt_has_unique_preimage.
Print Assumptions delayed_collision_in_held_region.
Print Assumptions start_membership_not_permanent.
Print Assumptions retaining_program_preserves_injectivity.
Print Assumptions reusable_toggle_is_injective.
Print Assumptions reusable_toggle_returns.
Print Assumptions constant_view_cannot_recover_full_state.
Print Assumptions preparation_capacity.
Print Assumptions all_time_projection.
Print Assumptions prepared_execution_prefix.
Print Assumptions complete_host_finite.
Print Assumptions completed_view_cannot_decode_time.
Print Assumptions finite_hold_run_collision.
