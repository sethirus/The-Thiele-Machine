(* SCOPE NOTE: standalone proof scope.
   Bounds observed mergers by explicitly supplied collision-covering charges on an arbitrary transition system.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia Bool.
From Minimal Require Import CompleteHost StructuralMeter.
Import ListNotations.

Section Accounting.
  Context {X : Type}.
  Variable eq_dec : forall a b : X, {a=b}+{a<>b}.
  Variable F : X -> X.
  Variable entry : X.
  Variable charge : X -> nat.

  Fixpoint list_charge (xs : list X) : nat :=
    match xs with [] => 0 | x::rest => charge x + list_charge rest end.
  Definition run_charge L := list_charge (sources F entry L).
  Definition collision_covered L := forall a b,
    In a (sources F entry L) -> In b (sources F entry L) ->
    a<>b -> F a=F b -> 0<charge a \/ 0<charge b.
  Definition paid_sources L := filter (fun s => 0 <? charge s) (sources F entry L).

  Lemma positive_filter_count : forall xs,
    length (filter (fun s => 0 <? charge s) xs) <= list_charge xs.
  Proof.
    induction xs as [|x xs IH]; simpl; [lia|].
    destruct (0 <? charge x) eqn:E; simpl; [apply Nat.ltb_lt in E|]; lia.
  Qed.

  Theorem merge_count_bounded_by_charge : forall L,
    collision_covered L -> merges eq_dec F entry L <= run_charge L.
  Proof.
    intros L Hcover.
    assert (Hincl:incl (merge_targets eq_dec F entry L) (map F (paid_sources L))).
    { intros z Hz.
      apply merge_target_exact in Hz as [a [b [Ha [Hb [Hneq [Hfa Hfb]]]]]].
      assert (Hc:0<charge a \/ 0<charge b) by (apply Hcover; auto; congruence).
      destruct Hc as [Hc|Hc]; apply in_map_iff.
      - exists a; split; [exact Hfa|]. unfold paid_sources; apply filter_In.
        split; [exact Ha|apply Nat.ltb_lt; exact Hc].
      - exists b; split; [exact Hfb|]. unfold paid_sources; apply filter_In.
        split; [exact Hb|apply Nat.ltb_lt; exact Hc]. }
    assert (Hnd:NoDup (merge_targets eq_dec F entry L)).
    { unfold merge_targets; apply NoDup_nodup. }
    pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
    rewrite map_length in Hlen.
    pose proof (positive_filter_count (sources F entry L)) as Hpaid.
    unfold merges,run_charge,paid_sources in *; lia.
  Qed.

  Lemma list_charge_app : forall xs ys,
    list_charge (xs++ys)=list_charge xs+list_charge ys.
  Proof. induction xs; intros ys; simpl; [reflexivity|rewrite IHxs; lia]. Qed.
  Lemma run_charge_succ : forall n,
    run_charge (S n)=run_charge n+charge (iter F n entry).
  Proof.
    intro n; unfold run_charge,sources; rewrite seq_S,map_app,list_charge_app.
    simpl; lia.
  Qed.

  Theorem cumulative_ledger_correspondence : forall mu : X -> nat,
    (forall s, mu (F s)=mu s+charge s) -> forall L,
    mu (iter F L entry)=mu entry+run_charge L.
  Proof.
    intros mu Hmu L; induction L; [simpl; unfold run_charge,sources; simpl; lia|].
    change (mu (F (iter F L entry))=mu entry+run_charge (S L)).
    rewrite Hmu,IHL,run_charge_succ; lia.
  Qed.

  Theorem ledger_bounds_observed_merges : forall mu : X -> nat,
    (forall s, mu (F s)=mu s+charge s) -> forall L,
    collision_covered L ->
    mu entry+merges eq_dec F entry L <= mu (iter F L entry).
  Proof.
    intros mu Hmu L Hcover; rewrite cumulative_ledger_correspondence by exact Hmu.
    pose proof (merge_count_bounded_by_charge L Hcover); lia.
  Qed.

  Theorem finite_holding_forces_paid_run : forall (H : X -> Prop) hs L,
    ~H entry -> H (F entry) -> (forall s, H s -> H (F s)) ->
    (forall s, H s -> In s hs) -> length hs<L -> collision_covered L ->
    0<run_charge L.
  Proof.
    intros H hs L Hout Hin Hclosed Hhs Hlen Hcover.
    pose proof (@finite_room_forces_merge X eq_dec F entry H Hout Hin Hclosed
      L hs Hhs Hlen) as Hmerge.
    pose proof (merge_count_bounded_by_charge L Hcover); lia.
  Qed.

  (* Sharpness of the implication: it is sufficient, not necessary, for
     the scalar inequality. The counterexample below pays on an unrelated
     incoming edge while leaving both merging edges free. *)
End Accounting.

Definition cover_failure_step (n : nat) := Nat.min (S n) 2.
Definition unrelated_charge (n : nat) := if Nat.eqb n 0 then 1 else 0.
Theorem aggregate_bound_does_not_imply_local_coverage :
  merges Nat.eq_dec cover_failure_step 0 3 <=
    run_charge cover_failure_step 0 unrelated_charge 3 /\
  ~collision_covered cover_failure_step 0 unrelated_charge 3.
Proof.
  split; [reflexivity|]. intro H.
  specialize (H 1 2); simpl in H.
  assert (Hc:0<0 \/ 0<0) by (apply H; intuition discriminate).
  lia.
Qed.

(* A positive charge on entry and zero on idle IS possible internally;
   the earlier positive-every-tick obstruction does not exclude this. *)
Definition raise (n : nat) := if n =? 0 then 1 else n.
Definition raise_charge (n : nat) := if n =? 0 then 1 else 0.
Definition raise_ledger (n : nat) := if n =? 0 then 0 else 1.
Theorem paid_entry_free_idle :
  (forall n, raise_ledger (raise n)=raise_ledger n+raise_charge n) /\
  collision_covered raise 0 raise_charge 2 /\ raise_charge 1=0.
Proof.
  split; [intro n; destruct n; reflexivity|]. split; [|reflexivity].
  intros a b Ha Hb Hneq Heq.
  cbn in Ha, Hb.
  destruct Ha as [Ha|[Ha|[]]]; destruct Hb as [Hb|[Hb|[]]]; subst;
    try (exfalso; apply Hneq; reflexivity); cbn in *; try congruence; lia.
Qed.

(* Supplying an instruction label is different from erasing it in a
   stored-program/autonomous transition. Each of these opcodes is bijective. *)
Definition op (i s : bool) := if i then negb s else s.
Definition dispatch (s : bool) := negb s.
Definition scheduled (s : bool) := op (dispatch s) s.
Theorem each_opcode_injective : forall i a b, op i a=op i b -> a=b.
Proof. destruct i,a,b; simpl; intros; congruence. Qed.
Theorem scheduling_can_merge : false<>true /\ scheduled false=scheduled true.
Proof. split; discriminate || reflexivity. Qed.
Theorem opcode_injectivity_does_not_price_dispatch :
  ~collision_covered scheduled false (fun _ => 0) 2.
Proof.
  intro H; specialize (H false true); simpl in H.
  assert (Hc:0<0 \/ 0<0) by (apply H; intuition discriminate); lia.
Qed.
