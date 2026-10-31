(* SCOPE NOTE: standalone proof scope. A short check written beside the book: it states its own
   machine, prices and conditions as hypotheses and uses only the Coq standard library, so it
   does not import the foundation chain. *)
(* Chapter twenty-one, two levers that keep states apart everywhere, forever. Tabletop values 0, 1, 2;
   the first lever wipes 1 to 0, the second wipes 2 to 0. Starts z, a, b read 0, 1, 2. Each lever is
   one-to-one on every state. In the simple case where the levers commute, the second lever holds a
   still and the first holds b still, there are 2T + 3 different states each reached within T pulls.
   Without commuting, a box with one line of zero states that both levers walk keeps everything apart
   forever with T + 3 (see the Python check). *)
From Coq Require Import List Arith Lia.
Import ListNotations.

Section Forever.
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

  Hypothesis F_inj : forall x y, F x = F y -> x = y.
  Hypothesis G_inj : forall x y, G x = G y -> x = y.
  Hypothesis commute : forall x, F (G x) = G (F x).
  Hypothesis G_holds_a : G a = a.
  Hypothesis F_holds_b : F b = b.

  Inductive reach : nat -> St -> Prop :=
  | r_z : reach 0 z | r_a : reach 0 a | r_b : reach 0 b
  | r_stay : forall t x, reach t x -> reach (S t) x
  | r_F : forall t x, reach t x -> reach (S t) (F x)
  | r_G : forall t x, reach t x -> reach (S t) (G x).

  Fixpoint itF (k : nat) (x : St) := match k with 0 => x | S j => F (itF j x) end.
  Fixpoint itG (k : nat) (x : St) := match k with 0 => x | S j => G (itG j x) end.

  Lemma reach_mono : forall t u x, t <= u -> reach t x -> reach u x.
  Proof. intros t u x H. induction H; auto using r_stay. Qed.
  Lemma reach_itF : forall k t x, reach t x -> reach (t + k) (itF k x).
  Proof. induction k; intros t x H; simpl; [rewrite Nat.add_0_r; exact H | rewrite Nat.add_succ_r; apply r_F; auto]. Qed.
  Lemma reach_itG : forall k t x, reach t x -> reach (t + k) (itG k x).
  Proof. induction k; intros t x H; simpl; [rewrite Nat.add_0_r; exact H | rewrite Nat.add_succ_r; apply r_G; auto]. Qed.

  Lemma itF_add : forall m n x, itF m (itF n x) = itF (m + n) x.
  Proof. induction m; intros; simpl; [reflexivity | rewrite IHm; reflexivity]. Qed.
  Lemma itG_add : forall m n x, itG m (itG n x) = itG (m + n) x.
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
  Lemma rd_itF_z : forall k, rd (itF k z) = 0.
  Proof. induction k as [|k IH]; [exact rz | change (itF (S k) z) with (F (itF k z)); rewrite F_read, IH; reflexivity]. Qed.
  Lemma rd_itG_z : forall k, rd (itG k z) = 0.
  Proof. induction k as [|k IH]; [exact rz | change (itG (S k) z) with (G (itG k z)); rewrite G_read, IH; reflexivity]. Qed.

  (* walking back, now everywhere: the levers are one-to-one on every state *)
  Lemma backF : forall i j x y, i <= j -> itF i x = itF j y -> x = itF (j - i) y.
  Proof.
    induction i as [|i IH]; intros j x y Hij E; [rewrite Nat.sub_0_r; exact E|].
    destruct j as [|j]; [lia|]. simpl in E. apply F_inj in E.
    replace (S j - S i) with (j - i) by lia. apply IH; [lia | exact E].
  Qed.
  Lemma backG : forall i j x y, i <= j -> itG i x = itG j y -> x = itG (j - i) y.
  Proof.
    induction i as [|i IH]; intros j x y Hij E; [rewrite Nat.sub_0_r; exact E|].
    destruct j as [|j]; [lia|]. simpl in E. apply G_inj in E.
    replace (S j - S i) with (j - i) by lia. apply IH; [lia | exact E].
  Qed.

  (* each chain walks on forever without repeating *)
  Lemma chainF_distinct : forall i j, i < j -> itF i a <> itF j a.
  Proof.
    intros i j Hij E. apply backF in E; [|lia].
    assert (rd a = rd (itF (j - i) a)) by (rewrite <- E; reflexivity).
    rewrite rd_itF_a in H by lia. rewrite ra in H. discriminate.
  Qed.
  Lemma chainG_distinct : forall i j, i < j -> itG i b <> itG j b.
  Proof.
    intros i j Hij E. apply backG in E; [|lia].
    assert (rd b = rd (itG (j - i) b)) by (rewrite <- E; reflexivity).
    rewrite rd_itG_b in H by lia. rewrite rb in H. discriminate.
  Qed.

  Lemma G_holds_chainF : forall k, G (itF k a) = itF k a.
  Proof. induction k; simpl; [exact G_holds_a | rewrite <- commute, IHk; reflexivity]. Qed.
  Lemma F_holds_chainG : forall k, F (itG k b) = itG k b.
  Proof. induction k; simpl; [exact F_holds_b | rewrite commute, IHk; reflexivity]. Qed.

  (* the chains share nothing, not even an end: the first lever moves one and holds the other *)
  Lemma chains_disjoint : forall i j, itF i a <> itG j b.
  Proof.
    intros i j E. apply (chainF_distinct i (S i)); [lia|].
    change (itF (S i) a) with (F (itF i a)). rewrite E, F_holds_chainG. reflexivity.
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
  Lemma nodup_app : forall (A : Type) (l1 l2 : list A), NoDup l1 -> NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [|c l1 IH]; intros l2 H1 H2 D; simpl; [exact H2|].
    inversion H1; subst. constructor.
    - intro Hin. apply in_app_or in Hin as [Hin | Hin]; [contradiction | apply (D c); [left|]; auto].
    - apply IH; auto. intros x Hx Hy. apply (D x); [right|]; auto.
  Qed.

  Lemma chainF_nodup : NoDup chainF.
  Proof.
    apply nodup_map_on; [apply seq_NoDup|]. intros i j _ _ E.
    destruct (lt_eq_lt_dec i j) as [[L|Q]|L]; [exfalso; exact (chainF_distinct i j L E)
      | exact Q | exfalso; exact (chainF_distinct j i L (eq_sym E))].
  Qed.
  Lemma chainG_nodup : NoDup chainG.
  Proof.
    apply nodup_map_on; [apply seq_NoDup|]. intros i j _ _ E.
    destruct (lt_eq_lt_dec i j) as [[L|Q]|L]; [exfalso; exact (chainG_distinct i j L E)
      | exact Q | exfalso; exact (chainG_distinct j i L (eq_sym E))].
  Qed.

  Lemma in_chainF : forall x, In x chainF -> exists i, 1 <= i <= T /\ x = itF i a.
  Proof. intros x H. apply in_map_iff in H as [i [E Hi]]. apply in_seq in Hi. exists i. split; [lia | auto]. Qed.
  Lemma in_chainG : forall x, In x chainG -> exists i, 1 <= i <= T /\ x = itG i b.
  Proof. intros x H. apply in_map_iff in H as [i [E Hi]]. apply in_seq in Hi. exists i. split; [lia | auto]. Qed.

  (* the zero start makes one more: itself if it's on neither chain, or the state T pulls past it *)
  Definition extra : St :=
    if In_dec eq_dec z chainF then itF T z else if In_dec eq_dec z chainG then itG T z else z.

  Lemma extra_zero : rd extra = 0.
  Proof.
    unfold extra. destruct (In_dec eq_dec z chainF); [apply rd_itF_z|].
    destruct (In_dec eq_dec z chainG); [apply rd_itG_z | exact rz].
  Qed.

  Lemma extra_reached : reach T extra.
  Proof.
    unfold extra. destruct (In_dec eq_dec z chainF).
    - replace T with (0 + T) by lia. apply reach_itF, r_z.
    - destruct (In_dec eq_dec z chainG); [replace T with (0 + T) by lia; apply reach_itG, r_z|].
      apply (reach_mono 0); [lia | exact r_z].
  Qed.

  Lemma extra_off_chains : ~ In extra chainF /\ ~ In extra chainG.
  Proof.
    unfold extra. destruct (In_dec eq_dec z chainF) as [Hz | Hz].
    - destruct (in_chainF _ Hz) as [k [Hk Ek]]. rewrite Ek, itF_add. split.
      + intro H. destruct (in_chainF _ H) as [i [Hi Ei]]. exact (chainF_distinct i (T + k) ltac:(lia) (eq_sym Ei)).
      + intro H. destruct (in_chainG _ H) as [i [Hi Ei]]. exact (chains_disjoint (T + k) i Ei).
    - destruct (In_dec eq_dec z chainG) as [Hz' | Hz'].
      + destruct (in_chainG _ Hz') as [k [Hk Ek]]. rewrite Ek, itG_add. split.
        * intro H. destruct (in_chainF _ H) as [i [Hi Ei]]. exact (chains_disjoint i (T + k) (eq_sym Ei)).
        * intro H. destruct (in_chainG _ H) as [i [Hi Ei]]. exact (chainG_distinct i (T + k) ltac:(lia) (eq_sym Ei)).
      + split; assumption.
  Qed.

  Lemma neq_by_rd : forall x y, rd x <> rd y -> x <> y.
  Proof. intros x y H E. apply H. rewrite E. reflexivity. Qed.

  Theorem commuting_forever_levers_need_2T_plus_3 :
    exists l, NoDup l /\ length l = 2 * T + 3 /\ forall x, In x l -> reach T x.
  Proof.
    exists (a :: b :: extra :: chainF ++ chainG). split; [|split].
    - destruct extra_off_chains as [OF OG].
      constructor; [|constructor; [|constructor]].
      + intros [E|[E|E]].
        * exact (neq_by_rd b a ltac:(rewrite ra, rb; discriminate) E).
        * exact (neq_by_rd extra a ltac:(rewrite extra_zero, ra; discriminate) E).
        * apply in_app_or in E as [E|E];
            [destruct (in_chainF _ E) as [i [Hi Ei]] | destruct (in_chainG _ E) as [i [Hi Ei]]];
            [pose proof (rd_itF_a i ltac:(lia)) as R | pose proof (rd_itG_b i ltac:(lia)) as R];
            rewrite <- Ei, ra in R; discriminate.
      + intros [E|E].
        * exact (neq_by_rd extra b ltac:(rewrite extra_zero, rb; discriminate) E).
        * apply in_app_or in E as [E|E];
            [destruct (in_chainF _ E) as [i [Hi Ei]] | destruct (in_chainG _ E) as [i [Hi Ei]]];
            [pose proof (rd_itF_a i ltac:(lia)) as R | pose proof (rd_itG_b i ltac:(lia)) as R];
            rewrite <- Ei, rb in R; discriminate.
      + intro E. apply in_app_or in E as [E|E]; contradiction.
      + apply nodup_app; [exact chainF_nodup | exact chainG_nodup |].
        intros x H1 H2. destruct (in_chainF _ H1) as [i [_ Ei]]. destruct (in_chainG _ H2) as [j [_ Ej]].
        rewrite Ei in Ej. exact (chains_disjoint i j Ej).
    - simpl. rewrite app_length. unfold chainF, chainG. rewrite !map_length, !seq_length. lia.
    - intros x [E|[E|[E|E]]]; subst.
      + apply (reach_mono 0); [lia | exact r_a].
      + apply (reach_mono 0); [lia | exact r_b].
      + exact extra_reached.
      + apply in_app_or in E as [E|E].
        * destruct (in_chainF _ E) as [i [Hi ->]]. apply (reach_mono (0 + i)); [lia | apply reach_itF, r_a].
        * destruct (in_chainG _ E) as [i [Hi ->]]. apply (reach_mono (0 + i)); [lia | apply reach_itG, r_b].
  Qed.
End Forever.

Print Assumptions commuting_forever_levers_need_2T_plus_3.
