(* SCOPE NOTE: standalone proof scope. A short check written beside the book: it states its own
   machine, prices and conditions as hypotheses and uses only the Coq standard library, so it
   does not import the foundation chain. *)
(* Chapter twenty-one, the two-bit grid: no box with this tabletop does better than 1 + (t+2)(t+3)/2.
   Readings are two bits, (first set?, second set?). The first lever clears the first bit, the second
   lever clears the second; each keeps apart the states reached in fewer than T pulls. Starts: one state
   for each of the four readings. The states reached within t pulls are computed as a list, R t. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.

Section Grid.
  Variable St : Type.
  Hypothesis eq_dec : forall x y : St, {x = y} + {x <> y}.
  Variables F G : St -> St.
  Variable rd : St -> bool * bool.
  Hypothesis F_read : forall x, rd (F x) = (false, snd (rd x)).
  Hypothesis G_read : forall x, rd (G x) = (fst (rd x), false).
  Variables s11 s01 s10 s00 : St.
  Hypothesis r11 : rd s11 = (true, true).
  Hypothesis r01 : rd s01 = (false, true).
  Hypothesis r10 : rd s10 = (true, false).
  Hypothesis r00 : rd s00 = (false, false).
  Variable T : nat.

  Fixpoint R (t : nat) : list St :=
    match t with
    | 0 => [s11; s01; s10; s00]
    | S k => nodup eq_dec (R k ++ map F (R k) ++ map G (R k))
    end.

  Hypothesis F_promise : forall t x y, t < T -> In x (R t) -> In y (R t) -> F x = F y -> x = y.
  Hypothesis G_promise : forall t x y, t < T -> In x (R t) -> In y (R t) -> G x = G y -> x = y.

  Definition is (r : bool * bool) (x : St) : bool :=
    Bool.eqb (fst (rd x)) (fst r) && Bool.eqb (snd (rd x)) (snd r).
  Lemma is_spec : forall r x, is r x = true <-> rd x = r.
  Proof.
    intros [a b] x. unfold is. destruct (rd x) as [c d]. simpl.
    rewrite andb_true_iff, !eqb_true_iff. split; [intros [-> ->]; reflexivity | intro E; inversion E; auto].
  Qed.
  Definition bucket r t := filter (is r) (R t).

  Lemma R_nodup : forall t, NoDup (R t).
  Proof.
    destruct t as [|k]; [|apply NoDup_nodup].
    simpl. repeat constructor; simpl; intros H; repeat destruct H as [H|H]; try contradiction;
      subst; congruence.
  Qed.
  Lemma R_grows : forall t x, In x (R t) -> In x (R (S t)).
  Proof. intros t x H. simpl. apply nodup_In. apply in_or_app. left. exact H. Qed.
  Lemma R_mono : forall t u x, t <= u -> In x (R t) -> In x (R u).
  Proof. intros t u x H. induction H; auto using R_grows. Qed.
  Lemma R_F : forall t x, In x (R t) -> In (F x) (R (S t)).
  Proof. intros t x H. simpl. apply nodup_In. apply in_or_app. right. apply in_or_app. left. apply in_map. exact H. Qed.
  Lemma R_G : forall t x, In x (R t) -> In (G x) (R (S t)).
  Proof. intros t x H. simpl. apply nodup_In. apply in_or_app. right. apply in_or_app. right. apply in_map. exact H. Qed.
  Lemma start_in : forall t, In s11 (R t) /\ In s01 (R t) /\ In s10 (R t) /\ In s00 (R t).
  Proof.
    intro t. repeat split; apply (R_mono 0 t); try lia; simpl; tauto.
  Qed.

  Lemma nodup_map_on : forall (g : St -> St) (l : list St), NoDup l ->
      (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (map g l).
  Proof.
    induction l as [|c l IH]; intros H Inj; simpl; [constructor|].
    inversion H; subst. constructor.
    - intro Hin. apply in_map_iff in Hin as [y [E Hy]].
      assert (c = y) by (apply Inj; [left; reflexivity | right; exact Hy | symmetry; exact E]).
      subst. contradiction.
    - apply IH; auto. intros x y Hx Hy E. apply Inj; [right | right |]; auto.
  Qed.
  Lemma nodup_app : forall (l1 l2 : list St), NoDup l1 -> NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [|c l1 IH]; intros l2 H1 H2 D; simpl; [exact H2|].
    inversion H1; subst. constructor.
    - intro Hin. apply in_app_or in Hin as [Hin | Hin]; [contradiction | apply (D c); [left|]; auto].
    - apply IH; auto. intros x Hx Hy. apply (D x); [right|]; auto.
  Qed.

  Lemma in_bucket : forall r t x, In x (bucket r t) <-> In x (R t) /\ rd x = r.
  Proof. intros. unfold bucket. rewrite filter_In, is_spec. tauto. Qed.
  Lemma bucket_nodup : forall r t, NoDup (bucket r t).
  Proof. intros. apply NoDup_filter, R_nodup. Qed.

  Definition A := (false, true).   (* first bit cleared *)
  Definition B := (true, false).   (* second bit cleared *)
  Definition Z := (false, false).  (* both cleared *)

  (* the first lever sends the both-set start and the first-cleared bucket into the first-cleared bucket *)
  Lemma A_grows : forall t, t < T -> S (length (bucket A t)) <= length (bucket A (S t)).
  Proof.
    intros t Ht.
    assert (ND : NoDup (map F (s11 :: bucket A t))).
    { apply nodup_map_on.
      - constructor; [|apply bucket_nodup]. intro H. apply in_bucket in H as [_ E]. rewrite r11 in E. discriminate.
      - intros x y Hx Hy E. apply (F_promise t); auto;
          [destruct Hx as [<-|Hx]; [apply start_in | apply in_bucket in Hx; tauto]
          |destruct Hy as [<-|Hy]; [apply start_in | apply in_bucket in Hy; tauto]]. }
    assert (Inc : incl (map F (s11 :: bucket A t)) (bucket A (S t))).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply in_bucket. split.
      - apply R_F. destruct Hx as [<-|Hx]; [apply start_in | apply in_bucket in Hx; tauto].
      - rewrite F_read. destruct Hx as [<-|Hx]; [rewrite r11; reflexivity | apply in_bucket in Hx as [_ E]; rewrite E; reflexivity]. }
    pose proof (NoDup_incl_length ND Inc). rewrite map_length in H. simpl in H. exact H.
  Qed.
  Lemma B_grows : forall t, t < T -> S (length (bucket B t)) <= length (bucket B (S t)).
  Proof.
    intros t Ht.
    assert (ND : NoDup (map G (s11 :: bucket B t))).
    { apply nodup_map_on.
      - constructor; [|apply bucket_nodup]. intro H. apply in_bucket in H as [_ E]. rewrite r11 in E. discriminate.
      - intros x y Hx Hy E. apply (G_promise t); auto;
          [destruct Hx as [<-|Hx]; [apply start_in | apply in_bucket in Hx; tauto]
          |destruct Hy as [<-|Hy]; [apply start_in | apply in_bucket in Hy; tauto]]. }
    assert (Inc : incl (map G (s11 :: bucket B t)) (bucket B (S t))).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply in_bucket. split.
      - apply R_G. destruct Hx as [<-|Hx]; [apply start_in | apply in_bucket in Hx; tauto].
      - rewrite G_read. destruct Hx as [<-|Hx]; [rewrite r11; reflexivity | apply in_bucket in Hx as [_ E]; rewrite E; reflexivity]. }
    pose proof (NoDup_incl_length ND Inc). rewrite map_length in H. simpl in H. exact H.
  Qed.

  (* the second lever sends the both-cleared bucket and the first-cleared bucket into the both-cleared bucket *)
  Lemma Z_grows : forall t, t < T -> length (bucket Z t) + length (bucket A t) <= length (bucket Z (S t)).
  Proof.
    intros t Ht.
    assert (ND : NoDup (map G (bucket Z t ++ bucket A t))).
    { apply nodup_map_on.
      - apply nodup_app; [apply bucket_nodup | apply bucket_nodup|].
        intros x H1 H2. apply in_bucket in H1 as [_ E1]. apply in_bucket in H2 as [_ E2]. rewrite E1 in E2. discriminate.
      - intros x y Hx Hy E. apply (G_promise t); auto;
          [apply in_app_or in Hx as [Hx|Hx] | apply in_app_or in Hy as [Hy|Hy]]; apply in_bucket in Hx || apply in_bucket in Hy; tauto. }
    assert (Inc : incl (map G (bucket Z t ++ bucket A t)) (bucket Z (S t))).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]].
      assert (Hr : In x (R t)) by (apply in_app_or in Hx as [Hx|Hx]; apply in_bucket in Hx; tauto).
      apply in_bucket. split; [apply R_G; exact Hr|].
      rewrite G_read. apply in_app_or in Hx as [Hx|Hx]; apply in_bucket in Hx as [_ E]; rewrite E; reflexivity. }
    pose proof (NoDup_incl_length ND Inc). rewrite map_length, app_length in H. exact H.
  Qed.

  Lemma A_at_least : forall t, t <= T -> t + 1 <= length (bucket A t).
  Proof.
    induction t as [|t IH]; intro Ht.
    - assert (In s01 (bucket A 0)) by (apply in_bucket; split; [apply start_in | exact r01]).
      destruct (bucket A 0); [contradiction | simpl; lia].
    - pose proof (A_grows t ltac:(lia)). specialize (IH ltac:(lia)). lia.
  Qed.
  Lemma B_at_least : forall t, t <= T -> t + 1 <= length (bucket B t).
  Proof.
    induction t as [|t IH]; intro Ht.
    - assert (In s10 (bucket B 0)) by (apply in_bucket; split; [apply start_in | exact r10]).
      destruct (bucket B 0); [contradiction | simpl; lia].
    - pose proof (B_grows t ltac:(lia)). specialize (IH ltac:(lia)). lia.
  Qed.
  Lemma Z_at_least : forall t, t <= T -> 2 + t * (t + 1) <= 2 * length (bucket Z t).
  Proof.
    induction t as [|t IH]; intro Ht.
    - assert (In s00 (bucket Z 0)) by (apply in_bucket; split; [apply start_in | exact r00]).
      destruct (bucket Z 0); [contradiction | simpl; lia].
    - pose proof (Z_grows t ltac:(lia)). pose proof (A_at_least t ltac:(lia)). specialize (IH ltac:(lia)). nia.
  Qed.
  Lemma one_both_set : forall t, 1 <= length (bucket (true, true) t).
  Proof.
    intro t. assert (In s11 (bucket (true, true) t)) by (apply in_bucket; split; [apply start_in | exact r11]).
    destruct (bucket (true, true) t); [contradiction | simpl; lia].
  Qed.

  (* the four buckets split every list of states *)
  Lemma exactly_one : forall x,
      (if is (true, true) x then 1 else 0) + (if is A x then 1 else 0) +
      (if is B x then 1 else 0) + (if is Z x then 1 else 0) = 1.
  Proof. intro x. unfold is, A, B, Z. destruct (rd x) as [[|] [|]]; reflexivity. Qed.

  Lemma four_buckets : forall l : list St, length l =
      length (filter (is (true, true)) l) + length (filter (is A) l) + length (filter (is B) l) + length (filter (is Z) l).
  Proof.
    induction l as [|x l IH]; [reflexivity|]. cbn [filter length].
    pose proof (exactly_one x) as One.
    destruct (is (true, true) x), (is A x), (is B x), (is Z x); cbn [length] in *; lia.
  Qed.

  Theorem grid_lower_bound : 2 + (T + 2) * (T + 3) <= 2 * length (R T).
  Proof.
    rewrite (four_buckets (R T)).
    pose proof (A_at_least T (le_n T)). pose proof (B_at_least T (le_n T)).
    pose proof (Z_at_least T (le_n T)). pose proof (one_both_set T).
    unfold bucket in *. nia.
  Qed.
End Grid.

Print Assumptions grid_lower_bound.
