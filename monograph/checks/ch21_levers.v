(* Chapter twenty-one, two levers. Tabletop values 0, 1, 2; the first lever wipes 1 to 0, the second
   wipes 2 to 0. Starts z, a, b read 0, 1, 2. Each lever keeps apart every two states reached in fewer
   than T pulls. Then the box has at least T + 3 states; and in the simple case where the levers commute,
   the second lever holds a still and the first holds b still, at least 2T + 2. *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Section Levers.
  Variable St : Type.
  Hypothesis eq_dec : forall x y : St, {x = y} + {x <> y}.
  Variables F G : St -> St.
  Variable rd : St -> nat.
  Hypothesis F_read : forall x, rd (F x) = if Nat.eqb (rd x) 1 then 0 else rd x.
  Hypothesis G_read : forall x, rd (G x) = if Nat.eqb (rd x) 2 then 0 else rd x.
  Variables z a b : St.
  Hypothesis rz : rd z = 0.
  Hypothesis ra : rd a = 1.
  Hypothesis rb : rd b = 2.
  Variable T : nat.

  Inductive reach : nat -> St -> Prop :=
  | r_z : reach 0 z | r_a : reach 0 a | r_b : reach 0 b
  | r_stay : forall t x, reach t x -> reach (S t) x
  | r_F : forall t x, reach t x -> reach (S t) (F x)
  | r_G : forall t x, reach t x -> reach (S t) (G x).

  Hypothesis F_promise : forall t u x y, t < T -> u < T -> reach t x -> reach u y -> F x = F y -> x = y.
  Hypothesis G_promise : forall t u x y, t < T -> u < T -> reach t x -> reach u y -> G x = G y -> x = y.

  Fixpoint itF (k : nat) (x : St) := match k with 0 => x | S j => F (itF j x) end.
  Fixpoint itG (k : nat) (x : St) := match k with 0 => x | S j => G (itG j x) end.

  Lemma reach_itF : forall k t x, reach t x -> reach (t + k) (itF k x).
  Proof. induction k; intros t x H; simpl; [rewrite Nat.add_0_r; exact H | rewrite Nat.add_succ_r; apply r_F; auto]. Qed.
  Lemma reach_itG : forall k t x, reach t x -> reach (t + k) (itG k x).
  Proof. induction k; intros t x H; simpl; [rewrite Nat.add_0_r; exact H | rewrite Nat.add_succ_r; apply r_G; auto]. Qed.

  Lemma itF_add : forall m n x, itF m (itF n x) = itF (m + n) x.
  Proof. induction m; intros; simpl; [reflexivity | rewrite IHm; reflexivity]. Qed.

  Lemma rd_itF_a : forall k, 0 < k -> rd (itF k a) = 0.
  Proof.
    induction k as [|k IH]; intro H; [lia|]. change (itF (S k) a) with (F (itF k a)). rewrite F_read.
    destruct k as [|k]; [simpl; rewrite ra; reflexivity | rewrite IH by lia; reflexivity].
  Qed.
  Lemma rd_itG_b : forall k, 0 < k -> rd (itG k b) = 0.
  Proof.
    induction k as [|k IH]; intro H; [lia|]. change (itG (S k) b) with (G (itG k b)). rewrite G_read.
    destruct k as [|k]; [simpl; rewrite rb; reflexivity | rewrite IH by lia; reflexivity].
  Qed.

  (* walking back along the first lever *)
  Lemma walkF : forall i j x y t u, reach t x -> reach u y -> t + i <= T -> u + j <= T -> i <= j ->
      itF i x = itF j y -> x = itF (j - i) y.
  Proof.
    induction i as [|i IH]; intros j x y t u Hx Hy Hti Huj Hij E.
    - simpl in E. rewrite Nat.sub_0_r. exact E.
    - destruct j as [|j]; [lia|]. simpl in E.
      apply (F_promise (t + i) (u + j)) in E; try lia; try (apply reach_itF; assumption).
      replace (S j - S i) with (j - i) by lia. apply (IH j x y t u); auto; lia.
  Qed.
  Lemma walkG : forall i j x y t u, reach t x -> reach u y -> t + i <= T -> u + j <= T -> i <= j ->
      itG i x = itG j y -> x = itG (j - i) y.
  Proof.
    induction i as [|i IH]; intros j x y t u Hx Hy Hti Huj Hij E.
    - simpl in E. rewrite Nat.sub_0_r. exact E.
    - destruct j as [|j]; [lia|]. simpl in E.
      apply (G_promise (t + i) (u + j)) in E; try lia; try (apply reach_itG; assumption).
      replace (S j - S i) with (j - i) by lia. apply (IH j x y t u); auto; lia.
  Qed.

  (* the first chain: F^1 a .. F^T a, all different *)
  Lemma chainF_distinct : forall i j, 1 <= i -> i < j -> j <= T -> itF i a <> itF j a.
  Proof.
    intros i j Hi Hij Hj E. apply (walkF i j a a 0 0 r_a r_a) in E; try lia.
    assert (rd a = rd (itF (j - i) a)) by (rewrite <- E; reflexivity).
    rewrite rd_itF_a in H by lia. rewrite ra in H. discriminate.
  Qed.
  Lemma chainG_distinct : forall i j, 1 <= i -> i < j -> j <= T -> itG i b <> itG j b.
  Proof.
    intros i j Hi Hij Hj E. apply (walkG i j b b 0 0 r_b r_b) in E; try lia.
    assert (rd b = rd (itG (j - i) b)) by (rewrite <- E; reflexivity).
    rewrite rd_itG_b in H by lia. rewrite rb in H. discriminate.
  Qed.

  Definition chainF := map (fun k => itF k a) (seq 1 T).
  Definition chainG := map (fun k => itG k b) (seq 1 T).

  Lemma nodup_map_on : forall (A B : Type) (g : A -> B) (l : list A), NoDup l ->
      (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (map g l).
  Proof.
    induction l as [|c l IH]; intros H Inj; simpl; [constructor|].
    inversion H; subst. constructor.
    - intro Hin. apply in_map_iff in Hin as [y [E Hy]].
      assert (c = y) by (apply Inj; [left; reflexivity | right; exact Hy | symmetry; exact E]).
      subst. contradiction.
    - apply IH; auto. intros x y Hx Hy E. apply Inj; [right | right |]; auto.
  Qed.

  Lemma chainF_nodup : NoDup chainF.
  Proof.
    apply nodup_map_on; [apply seq_NoDup|]. intros i j Hi Hj E.
    apply in_seq in Hi. apply in_seq in Hj.
    destruct (lt_eq_lt_dec i j) as [[L|Q]|L]; [exfalso; apply (chainF_distinct i j); auto; lia
      | exact Q | exfalso; apply (chainF_distinct j i); auto; lia].
  Qed.
  Lemma chainG_nodup : NoDup chainG.
  Proof.
    apply nodup_map_on; [apply seq_NoDup|]. intros i j Hi Hj E.
    apply in_seq in Hi. apply in_seq in Hj.
    destruct (lt_eq_lt_dec i j) as [[L|Q]|L]; [exfalso; apply (chainG_distinct i j); auto; lia
      | exact Q | exfalso; apply (chainG_distinct j i); auto; lia].
  Qed.

  Lemma in_chainF : forall x, In x chainF -> exists i, 1 <= i <= T /\ x = itF i a.
  Proof. intros x H. apply in_map_iff in H as [i [E Hi]]. apply in_seq in Hi. exists i. split; [lia | auto]. Qed.
  Lemma in_chainG : forall x, In x chainG -> exists i, 1 <= i <= T /\ x = itG i b.
  Proof. intros x H. apply in_map_iff in H as [i [E Hi]]. apply in_seq in Hi. exists i. split; [lia | auto]. Qed.

  Lemma rd_chainF : forall x, In x chainF -> rd x = 0.
  Proof. intros x H. destruct (in_chainF x H) as [i [Hi ->]]. apply rd_itF_a. lia. Qed.
  Lemma rd_chainG : forall x, In x chainG -> rd x = 0.
  Proof. intros x H. destruct (in_chainG x H) as [i [Hi ->]]. apply rd_itG_b. lia. Qed.

  Lemma nodup_app : forall (A : Type) (l1 l2 : list A), NoDup l1 -> NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [|c l1 IH]; intros l2 H1 H2 D; simpl; [exact H2|].
    inversion H1; subst. constructor.
    - intro Hin. apply in_app_or in Hin as [Hin | Hin]; [contradiction | apply (D c); [left|]; auto].
    - apply IH; auto. intros x Hx Hy. apply (D x); [right|]; auto.
  Qed.

  Lemma neq_by_rd : forall x y, rd x <> rd y -> x <> y.
  Proof. intros x y H E. apply H. rewrite E. reflexivity. Qed.

  (* ---------- T + 3 ---------- *)
  Definition extraF : St := if In_dec eq_dec z chainF then itF T z else z.

  Lemma rd_itF_z : forall k, rd (itF k z) = 0.
  Proof. induction k as [|k IH]; [exact rz | change (itF (S k) z) with (F (itF k z)); rewrite F_read, IH; reflexivity]. Qed.

  Lemma extraF_zero : rd extraF = 0.
  Proof. unfold extraF. destruct (In_dec eq_dec z chainF); [apply rd_itF_z | exact rz]. Qed.

  Lemma extraF_off_chain : ~ In extraF chainF.
  Proof.
    unfold extraF. destruct (In_dec eq_dec z chainF) as [Hz | Hz]; [|exact Hz].
    intro He. destruct (in_chainF _ Hz) as [i [Hi Ei]]. destruct (in_chainF _ He) as [j [Hj Ej]].
    (* itF T z = itF j a with j <= T: walk back j steps *)
    symmetry in Ej. apply (walkF j T a z 0 0 r_a r_z) in Ej; try lia.
    rewrite Ei, itF_add in Ej.
    assert (rd a = rd (itF (T - j + i) a)) by (rewrite <- Ej; reflexivity).
    rewrite rd_itF_a in H by lia. rewrite ra in H. discriminate.
  Qed.

  Theorem levers_need_T_plus_3 : forall all : list St, NoDup all -> (forall x, In x all) -> T + 3 <= length all.
  Proof.
    intros all Hall Hin.
    assert (ND : NoDup (a :: b :: extraF :: chainF)).
    { constructor; [|constructor; [|constructor]].
      - intros [E|[E|E]].
        + exact (neq_by_rd b a ltac:(rewrite ra, rb; discriminate) E).
        + exact (neq_by_rd extraF a ltac:(rewrite extraF_zero, ra; discriminate) E).
        + pose proof (rd_chainF a E) as R. rewrite ra in R. discriminate.
      - intros [E|E].
        + exact (neq_by_rd extraF b ltac:(rewrite extraF_zero, rb; discriminate) E).
        + pose proof (rd_chainF b E) as R. rewrite rb in R. discriminate.
      - exact extraF_off_chain.
      - exact chainF_nodup. }
    pose proof (NoDup_incl_length ND (fun x _ => Hin x)) as L.
    simpl in L. unfold chainF in L. rewrite map_length, seq_length in L. lia.
  Qed.

  (* ---------- 2T + 2, the simple case ---------- *)
  Hypothesis commute : forall x, F (G x) = G (F x).
  Hypothesis G_holds_a : G a = a.
  Hypothesis F_holds_b : F b = b.
  Hypothesis T_pos : 1 <= T.

  Lemma G_holds_chainF : forall k, G (itF k a) = itF k a.
  Proof. induction k; simpl; [exact G_holds_a | rewrite <- commute, IHk; reflexivity]. Qed.
  Lemma F_holds_chainG : forall k, F (itG k b) = itG k b.
  Proof. induction k; simpl; [exact F_holds_b | rewrite commute, IHk; reflexivity]. Qed.

  (* a state where the first lever moves you is not one where it holds you still *)
  Lemma chains_meet_only_at_ends : forall i j, 1 <= i <= T -> 1 <= j <= T ->
      itF i a = itG j b -> i = T /\ j = T.
  Proof.
    intros i j Hi Hj E. split.
    - destruct (Nat.eq_dec i T) as [|N]; [assumption|]. exfalso.
      assert (F (itF i a) = itF i a) by (rewrite E; apply F_holds_chainG).
      apply (chainF_distinct i (S i)); [lia | lia | lia | symmetry; exact H].
    - destruct (Nat.eq_dec j T) as [|N]; [assumption|]. exfalso.
      assert (G (itG j b) = itG j b) by (rewrite <- E; apply G_holds_chainF).
      apply (chainG_distinct j (S j)); [lia | lia | lia | symmetry; exact H].
  Qed.

  Definition shared := itF T a = itG T b.

  Lemma z_off_chainF_when_shared : shared -> ~ In z chainF.
  Proof.
    intros Sh Hz. destruct (in_chainF _ Hz) as [i [Hi Ei]].
    (* from z, T - i more pulls of the first lever reach the shared end c, which the first lever holds *)
    set (c := itF T a).
    assert (Fc : F c = c) by (unfold c; rewrite Sh; apply F_holds_chainG).
    assert (Ec : itF (T - i) z = c) by (unfold c; rewrite Ei, itF_add; f_equal; lia).
    (* itF (T-1) a and c both land on c; both are reached in fewer than T pulls *)
    assert (Land : F (itF (T - 1) a) = F c).
    { rewrite Fc. unfold c. replace T with (S (T - 1)) at 2 by lia. reflexivity. }
    apply (F_promise (0 + (T - 1)) (0 + (T - i))) in Land; try lia;
      [| apply reach_itF; exact r_a | rewrite <- Ec; apply reach_itF; exact r_z].
    destruct (Nat.eq_dec (T - 1) 0) as [Z|NZ].
    - rewrite Z in Land. simpl in Land. assert (rd a = rd c) by (rewrite Land; reflexivity).
      unfold c in H. rewrite rd_itF_a in H by lia. rewrite ra in H. discriminate.
    - apply (chainF_distinct (T - 1) T); [lia | lia | lia | exact Land].
  Qed.

  Lemma itG_add : forall m n x, itG m (itG n x) = itG (m + n) x.
  Proof. induction m; intros; simpl; [reflexivity | rewrite IHm; reflexivity]. Qed.

  Lemma z_off_chainG_when_shared : shared -> ~ In z chainG.
  Proof.
    intros Sh Hz. destruct (in_chainG _ Hz) as [i [Hi Ei]].
    set (c := itG T b).
    assert (Gc : G c = c) by (unfold c; rewrite <- Sh; apply G_holds_chainF).
    assert (Ec : itG (T - i) z = c) by (unfold c; rewrite Ei, itG_add; f_equal; lia).
    assert (Land : G (itG (T - 1) b) = G c).
    { rewrite Gc. unfold c. replace T with (S (T - 1)) at 2 by lia. reflexivity. }
    apply (G_promise (0 + (T - 1)) (0 + (T - i))) in Land; try lia;
      [| apply reach_itG; exact r_b | rewrite <- Ec; apply reach_itG; exact r_z].
    destruct (Nat.eq_dec (T - 1) 0) as [Z|NZ].
    - rewrite Z in Land. simpl in Land. assert (rd b = rd c) by (rewrite Land; reflexivity).
      unfold c in H. rewrite rd_itG_b in H by lia. rewrite rb in H. discriminate.
    - apply (chainG_distinct (T - 1) T); [lia | lia | lia | exact Land].
  Qed.

  Definition chainG_short := map (fun k => itG k b) (seq 1 (T - 1)).

  Lemma chainG_short_sub : forall x, In x chainG_short -> exists j, 1 <= j < T /\ x = itG j b.
  Proof. intros x H. apply in_map_iff in H as [j [E Hj]]. apply in_seq in Hj. exists j. split; [lia | auto]. Qed.

  Lemma chainG_short_nodup : NoDup chainG_short.
  Proof.
    apply nodup_map_on; [apply seq_NoDup|]. intros i j Hi Hj E.
    apply in_seq in Hi. apply in_seq in Hj.
    destruct (lt_eq_lt_dec i j) as [[L|Q]|L]; [exfalso; apply (chainG_distinct i j); auto; lia
      | exact Q | exfalso; apply (chainG_distinct j i); auto; lia].
  Qed.

  Lemma not_zero_not_a_b : forall x, rd x = 0 -> x <> a /\ x <> b.
  Proof. intros x H; split; intro E; subst; [rewrite ra in H | rewrite rb in H]; discriminate. Qed.

  Theorem commuting_levers_need_2T_plus_2 : forall all : list St, NoDup all -> (forall x, In x all) ->
      2 * T + 2 <= length all.
  Proof.
    intros all Hall Hin.
    destruct (eq_dec (itF T a) (itG T b)) as [Sh | NSh].
    - (* the chains share their end: the zero start is a third state off both *)
      assert (ND : NoDup (a :: b :: z :: chainF ++ chainG_short)).
      { assert (Zoff1 := z_off_chainF_when_shared Sh).
        assert (Zoff2 : ~ In z chainG_short).
        { intro H. apply (z_off_chainG_when_shared Sh). destruct (chainG_short_sub z H) as [j [Hj ->]].
          apply in_map_iff. exists j. split; [reflexivity | apply in_seq; lia]. }
        constructor; [|constructor; [|constructor]].
        - intros [E|[E|E]].
          + exact (neq_by_rd b a ltac:(rewrite ra, rb; discriminate) E).
          + exact (neq_by_rd z a ltac:(rewrite ra, rz; discriminate) E).
          + apply in_app_or in E as [E|E].
            * pose proof (rd_chainF a E) as R. rewrite ra in R. discriminate.
            * destruct (chainG_short_sub a E) as [j [Hj Ej]].
              assert (R : rd a = 0) by (rewrite Ej; apply rd_itG_b; lia). rewrite ra in R. discriminate.
        - intros [E|E].
          + exact (neq_by_rd z b ltac:(rewrite rb, rz; discriminate) E).
          + apply in_app_or in E as [E|E].
            * pose proof (rd_chainF b E) as R. rewrite rb in R. discriminate.
            * destruct (chainG_short_sub b E) as [j [Hj Ej]].
              assert (R : rd b = 0) by (rewrite Ej; apply rd_itG_b; lia). rewrite rb in R. discriminate.
        - intro E. apply in_app_or in E as [E|E]; [exact (Zoff1 E) | exact (Zoff2 E)].
        - apply nodup_app; [exact chainF_nodup | exact chainG_short_nodup|].
          intros x H1 H2. destruct (in_chainF x H1) as [i [Hi ->]]. destruct (chainG_short_sub _ H2) as [j [Hj Ej]].
          destruct (chains_meet_only_at_ends i j) as [_ JT]; [lia | lia | exact Ej | lia]. }
      pose proof (NoDup_incl_length ND (fun x _ => Hin x)) as L.
      simpl in L. rewrite app_length in L. unfold chainF, chainG_short in L.
      rewrite !map_length, !seq_length in L. lia.
    - (* the chains don't meet at all *)
      assert (ND : NoDup (a :: b :: chainF ++ chainG)).
      { constructor; [|constructor].
        - intros [E|E].
          + exact (neq_by_rd b a ltac:(rewrite ra, rb; discriminate) E).
          + apply in_app_or in E as [E|E]; [pose proof (rd_chainF a E) as R | pose proof (rd_chainG a E) as R];
              rewrite ra in R; discriminate.
        - intro E. apply in_app_or in E as [E|E]; [pose proof (rd_chainF b E) as R | pose proof (rd_chainG b E) as R];
            rewrite rb in R; discriminate.
        - apply nodup_app; [exact chainF_nodup | exact chainG_nodup|].
          intros x H1 H2. destruct (in_chainF x H1) as [i [Hi ->]]. destruct (in_chainG _ H2) as [j [Hj Ej]].
          destruct (chains_meet_only_at_ends i j) as [IT JT]; [lia | lia | exact Ej |].
          subst i j. apply NSh. exact Ej. }
      pose proof (NoDup_incl_length ND (fun x _ => Hin x)) as L.
      simpl in L. rewrite app_length in L. unfold chainF, chainG in L.
      rewrite !map_length, !seq_length in L. lia.
  Qed.
End Levers.

Print Assumptions levers_need_T_plus_3.
Print Assumptions commuting_levers_need_2T_plus_2.
