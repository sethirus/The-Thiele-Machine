(** CzProdTC: the interleaved product of two Thiele-complete axis machines is
    Thiele-complete.

    The interface of the product reads a move of the left machine as the
    left machine's own kind of move, a move of the right machine as the
    right machine's, and carries the claims, checks, meanings, "unchanged"
    relations, clean starts and ledgers along:

      claims          the disjoint union of the two claim types;
      meaning         a left claim is about the left component, a right
                      claim about the right one;
      unchanged       a left claim is unchanged between two product states
                      when it is unchanged between their left components, so
                      a move of the right machine never disturbs it;
      clean starts    both components clean;
      load a b        both components loaded with (a, b);
      floor           the pair of the two floors;
      point of claim  the point of a left claim in the left coordinate and the
                      right floor in the right one, and symmetrically;
      ledger          the sum of the two ledgers;
      universal base  the left machine's: the product runs every counter
                      program on its left window (the right window is a
                      second, independent one; see [cmpz_prod_runs_two]).

    The theorem [cmpz_prod_tc] says that all four clauses (universal base,
    earned record, exact toll, non-vacuity) hold for the product when they
    hold for the parts.  The earned clause is the one that needs work: the
    chain CHECK, COMMIT, CERTIFY in front of a move that leaves the
    down-set of the product is found in the projection of the run onto the
    component that moved, and lifts back to the interleaved run because a
    decomposition of a projection is a decomposition of the whole trace
    ([cmpz_lefts_split], [cmpz_rights_split]).  The other component's moves
    sit anywhere inside the chain and cannot disturb it.

    Consequences, all closed:

      cmpz_prod_thiele_complete        the product is Thiele-complete;
      cmpz_or_thiele_complete          the book's one-bit reading of the
                                       product ("some part has certified")
                                       is Thiele-complete in the book's
                                       sense;
      cmpz_prod_ledger_counts          the ledger of the product counts the
                                       record moves of both parts;
      cmpz_prod_joint_certificate      reaching a point that is above a
                                       point of each part, neither below
                                       its floor, costs at least 6, and 6
                                       is attained;
      cmpz_and_not_complete            the one-bit reading "both parts have
                                       certified" is not Thiele-complete
                                       with this interface: its certificate
                                       costs 6, and the definition asks for
                                       the three-move chain;
      cmpz_prod_runs_two               the product runs two counter
                                       programs at once, one on each
                                       window, with halting matched. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Kernel Require Import AxTwoPoint.
From Kernel Require Import CzProd.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(** * Kinds *)

Definition cmpz_mapk {C D : Type} (f : C -> D) (k : T.kind C) : T.kind D :=
  match k with
  | T.KBase => T.KBase
  | T.KCheck c => T.KCheck (f c)
  | T.KCommit c => T.KCommit (f c)
  | T.KCertify => T.KCertify
  end.

Lemma cmpz_mapk_base_iff : forall {C D} (f : C -> D) k,
  cmpz_mapk f k = T.KBase <-> k = T.KBase.
Proof. intros C D f k. destruct k; simpl; split; intro H; try discriminate; reflexivity. Qed.

(** * Least upper bounds in the product *)

Lemma cmpz_lub_left : forall {A B} (P : BPre A) (Q : BPre B) a1 p a2 b f,
  ax_is_lub P a1 p a2 -> bp_le Q f b ->
  ax_is_lub (cmpz_pair_pre P Q) (a1, b) (p, f) (a2, b).
Proof.
  intros A B P Q a1 p a2 b f [H1 [H2 H3]] Hf. unfold ax_is_lub.
  split; [| split].
  - apply cmpz_pair_le; simpl; split; [exact H1 | apply bp_le_refl].
  - apply cmpz_pair_le; simpl; split; [exact H2 | exact Hf].
  - intros [w1 w2] Hw1 Hw2. apply cmpz_pair_le in Hw1. apply cmpz_pair_le in Hw2. simpl in *.
    apply cmpz_pair_le; simpl; split; [apply H3; tauto | tauto].
Qed.

Lemma cmpz_lub_right : forall {A B} (P : BPre A) (Q : BPre B) b1 p b2 a f,
  ax_is_lub Q b1 p b2 -> bp_le P f a ->
  ax_is_lub (cmpz_pair_pre P Q) (a, b1) (f, p) (a, b2).
Proof.
  intros A B P Q b1 p b2 a f [H1 [H2 H3]] Hf. unfold ax_is_lub.
  split; [| split].
  - apply cmpz_pair_le; simpl; split; [apply bp_le_refl | exact H1].
  - apply cmpz_pair_le; simpl; split; [exact Hf | exact H2].
  - intros [w1 w2] Hw1 Hw2. apply cmpz_pair_le in Hw1. apply cmpz_pair_le in Hw2. simpl in *.
    apply cmpz_pair_le; simpl; split; [tauto | apply H3; tauto].
Qed.

Section ProdTC.

Context {A B : Type} {P : BPre A} {Q : BPre B} {M : amachine A P} {N : amachine B Q}.
Variable I1 : ax_interface M.
Variable I2 : ax_interface N.

(** * The interface of the product *)

Definition cmpz_base : T.universal_base (am_bare (cmpz_prod M N)) :=
  T.mk_ub (am_bare (cmpz_prod M N))
    (fun s => T.ub_window (axi_base I1) (fst s))
    (fun s => T.ub_live (axi_base I1) (fst s))
    (fun i => inl (T.ub_compile (axi_base I1) i))
    (fun a b => (T.ub_load (axi_base I1) a b, T.ub_load (axi_base I2) a b))
    (fun a b => T.ub_load_window (axi_base I1) a b)
    (fun a b => T.ub_load_live (axi_base I1) a b)
    (fun s i H => T.ub_sim (axi_base I1) (fst s) i H).

Definition cmpz_iface : ax_interface (cmpz_prod M N) :=
  mk_axi (A * B) (cmpz_pair_pre P Q) (cmpz_prod M N) cmpz_base
    (axi_claim I1 + axi_claim I2)
    (fun m => match m with
              | inl x => cmpz_mapk inl (axi_kind I1 x)
              | inr y => cmpz_mapk inr (axi_kind I2 y)
              end)
    (fun c s => match c with
                | inl c1 => axi_meaning I1 c1 (fst s)
                | inr c2 => axi_meaning I2 c2 (snd s)
                end)
    (fun s c => match c with
                | inl c1 => axi_check I1 (fst s) c1
                | inr c2 => axi_check I2 (snd s) c2
                end)
    (fun c s s' => match c with
                   | inl c1 => axi_same I1 c1 (fst s) (fst s')
                   | inr c2 => axi_same I2 c2 (snd s) (snd s')
                   end)
    (fun s => axi_clean I1 (fst s) /\ axi_clean I2 (snd s))
    (fun s => axi_ledger I1 (fst s) + axi_ledger I2 (snd s))
    (axi_floor I1, axi_floor I2)
    (fun c => match c with
              | inl c1 => (axi_point I1 c1, axi_floor I2)
              | inr c2 => (axi_floor I1, axi_point I2 c2)
              end).

Lemma cmpz_load : forall a b,
  ax_load cmpz_iface a b = (ax_load I1 a b, ax_load I2 a b).
Proof. reflexivity. Qed.

Lemma cmpz_record_move_inl : forall x,
  ax_record_move cmpz_iface (inl x) = ax_record_move I1 x.
Proof.
  intro x. unfold ax_record_move. simpl. destruct (axi_kind I1 x); reflexivity.
Qed.

Lemma cmpz_record_move_inr : forall y,
  ax_record_move cmpz_iface (inr y) = ax_record_move I2 y.
Proof.
  intro y. unfold ax_record_move. simpl. destruct (axi_kind I2 y); reflexivity.
Qed.

Hypothesis H1 : ax_tc_with I1.
Hypothesis H2 : ax_tc_with I2.

Local Ltac unpack :=
  destruct H1 as [[Hk1 [Hcl1 [Hb1 Hg1]]] [[Hfl1 [Hex1 [Hs1 Hr1]]] [[Hco1 Hle1] Hnv1]]];
  destruct H2 as [[Hk2 [Hcl2 [Hb2 Hg2]]] [[Hfl2 [Hex2 [Hs2 Hr2]]] [[Hco2 Hle2] Hnv2]]].

(** * The earned clause: a chain lifts through the projection *)

Lemma cmpz_earned_left : forall s0 tr x,
  axi_clean cmpz_iface s0 ->
  ax_exit_step (am_run (cmpz_prod M N) tr s0) (inl x) ->
  axc_earned_exit cmpz_iface s0 tr (inl x).
Proof.
  intros s0 tr x [Hc1 Hc2] Hex.
  pose proof H1 as HH1. pose proof H2 as HH2.
  unpack.
  assert (Hexit : ax_exit_step (am_run M (cmpz_lefts tr) (fst s0)) x).
  { unfold ax_exit_step in *. intro Hle. apply Hex.
    rewrite cmpz_run_prod. cbn. apply cmpz_pair_le. cbn. split; [exact Hle | apply bp_le_refl]. }
  destruct (Hex1 (fst s0) (cmpz_lefts tr) x Hc1 Hexit)
    as [pre [c [chk [mid1 [cmt [mid2 [Htr [Kc [Km [Kx [Hck [Hsame Hlub]]]]]]]]]]]].
  destruct (cmpz_lefts_split tr pre chk (mid1 ++ cmt :: mid2) Htr) as [T1 [T2 [E1 [L1 L2]]]].
  destruct (cmpz_lefts_split T2 mid1 cmt mid2 L2) as [T21 [T22 [E2 [L21 L22]]]].
  assert (Etr : (T1 ++ inl chk :: T21 ++ inl cmt :: T22 : list (am_move (cmpz_prod M N))) = tr).
  { rewrite E1, E2. reflexivity. }
  exists T1, (inl c), (inl chk), T21, (inl cmt), T22.
  split; [symmetry; exact Etr |].
  split; [cbn; rewrite Kc; reflexivity |].
  split; [cbn; rewrite Km; reflexivity |].
  split; [cbn; rewrite Kx; reflexivity |].
  split.
  - cbn. rewrite cmpz_run_prod_fst, L1. exact Hck.
  - split.
    + intros t1 t2 Hm. cbn. rewrite !cmpz_run_prod_fst.
      rewrite (cmpz_lefts_app (X := am_move M) (Y := am_move N)). cbn.
      rewrite L1. apply (Hsame (cmpz_lefts t1) (cmpz_lefts t2)).
      rewrite <- L21, Hm. exact (cmpz_lefts_app (X := am_move M) (Y := am_move N) t1 t2).
    + rewrite cmpz_run_prod. cbn.
      assert (Hge : bp_le Q (axi_floor I2) (am_rec N (am_run N (cmpz_rights tr) (snd s0)))).
      { rewrite <- (Hfl2 _ Hc2). apply (ax_run_grows I2 HH2). }
      exact (cmpz_lub_left P Q _ _ _ _ _ Hlub Hge).
Qed.

Lemma cmpz_earned_right : forall s0 tr y,
  axi_clean cmpz_iface s0 ->
  ax_exit_step (am_run (cmpz_prod M N) tr s0) (inr y) ->
  axc_earned_exit cmpz_iface s0 tr (inr y).
Proof.
  intros s0 tr y [Hc1 Hc2] Hex.
  pose proof H1 as HH1. pose proof H2 as HH2.
  unpack.
  assert (Hexit : ax_exit_step (am_run N (cmpz_rights tr) (snd s0)) y).
  { unfold ax_exit_step in *. intro Hle. apply Hex.
    rewrite cmpz_run_prod. cbn. apply cmpz_pair_le. cbn. split; [apply bp_le_refl | exact Hle]. }
  destruct (Hex2 (snd s0) (cmpz_rights tr) y Hc2 Hexit)
    as [pre [c [chk [mid1 [cmt [mid2 [Htr [Kc [Km [Kx [Hck [Hsame Hlub]]]]]]]]]]]].
  destruct (cmpz_rights_split tr pre chk (mid1 ++ cmt :: mid2) Htr) as [T1 [T2 [E1 [L1 L2]]]].
  destruct (cmpz_rights_split T2 mid1 cmt mid2 L2) as [T21 [T22 [E2 [L21 L22]]]].
  assert (Etr : (T1 ++ inr chk :: T21 ++ inr cmt :: T22 : list (am_move (cmpz_prod M N))) = tr).
  { rewrite E1, E2. reflexivity. }
  exists T1, (inr c), (inr chk), T21, (inr cmt), T22.
  split; [symmetry; exact Etr |].
  split; [cbn; rewrite Kc; reflexivity |].
  split; [cbn; rewrite Km; reflexivity |].
  split; [cbn; rewrite Kx; reflexivity |].
  split.
  - cbn. rewrite cmpz_run_prod_snd, L1. exact Hck.
  - split.
    + intros t1 t2 Hm. cbn. rewrite !cmpz_run_prod_snd.
      rewrite (cmpz_rights_app (X := am_move M) (Y := am_move N)). cbn.
      rewrite L1. apply (Hsame (cmpz_rights t1) (cmpz_rights t2)).
      rewrite <- L21, Hm. exact (cmpz_rights_app (X := am_move M) (Y := am_move N) t1 t2).
    + rewrite cmpz_run_prod. cbn.
      assert (Hge : bp_le P (axi_floor I1) (am_rec M (am_run M (cmpz_lefts tr) (fst s0)))).
      { rewrite <- (Hfl1 _ Hc1). apply (ax_run_grows I1 HH1). }
      exact (cmpz_lub_right P Q _ _ _ _ _ Hlub Hge).
Qed.

(** * The theorem *)

Theorem cmpz_prod_tc : ax_tc_with cmpz_iface.
Proof.
  pose proof H1 as HH1. pose proof H2 as HH2.
  unpack.
  split; [| split; [| split]].
  - (* universal base *)
    split; [| split; [| split]].
    + intro i. cbn. rewrite (Hk1 i). reflexivity.
    + intros a b. cbn. split; [apply Hcl1 | apply Hcl2].
    + intros s [x | y] Hkm.
      * cbn in Hkm. apply cmpz_mapk_base_iff in Hkm. cbn. rewrite (Hb1 _ _ Hkm). reflexivity.
      * cbn in Hkm. apply cmpz_mapk_base_iff in Hkm. cbn. rewrite (Hb2 _ _ Hkm). reflexivity.
    + intros s [x | y]; cbn; apply cmpz_pair_le; cbn.
      * split; [apply Hg1 | apply bp_le_refl].
      * split; [apply bp_le_refl | apply Hg2].
  - (* earned record *)
    split; [| split; [| split]].
    + intros s [Hc1 Hc2]. cbn. rewrite (Hfl1 _ Hc1), (Hfl2 _ Hc2). reflexivity.
    + intros s0 tr [x | y] Hcl Hex.
      * exact (cmpz_earned_left s0 tr x Hcl Hex).
      * exact (cmpz_earned_right s0 tr y Hcl Hex).
    + intros s [c | c] Hc; cbn in *.
      * exact (Hs1 _ _ Hc).
      * exact (Hs2 _ _ Hc).
    + intros [c | c] s s' Hs Hm; cbn in *.
      * exact (Hr1 _ _ _ Hs Hm).
      * exact (Hr2 _ _ _ Hs Hm).
  - (* exact toll *)
    split.
    + intros [x | y]; cbn.
      * rewrite (Hco1 x), cmpz_record_move_inl. reflexivity.
      * rewrite (Hco2 y), cmpz_record_move_inr. reflexivity.
    + intros s [x | y]; cbn.
      * rewrite (Hle1 (fst s) x). lia.
      * rewrite (Hle2 (snd s) y). lia.
  - (* non-vacuity *)
    destruct Hnv1 as [c [chk [cmt [crt [Kc [Km [Kx [Hiff [Hyes Hno]]]]]]]]].
    exists (inl c), (inl chk), (inl cmt), (inl crt).
    split; [cbn; rewrite Kc; reflexivity |].
    split; [cbn; rewrite Km; reflexivity |].
    split; [cbn; rewrite Kx; reflexivity |].
    split.
    + intros a b. rewrite cmpz_load. rewrite cmpz_run_prod. cbn.
      rewrite cmpz_pair_le. cbn.
      assert (Hf : am_rec N (ax_load I2 a b) = axi_floor I2) by (apply Hfl2; apply Hcl2).
      rewrite Hf. rewrite (Hiff a b). split.
      * intros [H _]. exact H.
      * intro H. split; [exact H | apply bp_le_refl].
    + split.
      * destruct Hyes as [a [b Hm]]. exists a, b. cbn. exact Hm.
      * destruct Hno as [a [b Hm]]. exists a, b. cbn. exact Hm.
Qed.

(** The ledger of the product counts the record moves of both parts. *)
Theorem cmpz_prod_ledger_counts : forall tr s,
  axi_ledger cmpz_iface (am_run (cmpz_prod M N) tr s)
    = axi_ledger cmpz_iface s + ax_record_moves cmpz_iface tr.
Proof. intros tr s. exact (ax_tc_ledger_counts cmpz_iface cmpz_prod_tc tr s). Qed.

Lemma cmpz_record_moves_prod : forall tr,
  ax_record_moves cmpz_iface tr
    = ax_record_moves I1 (cmpz_lefts tr) + ax_record_moves I2 (cmpz_rights tr).
Proof.
  induction tr as [| [x | y] tr IH]; [reflexivity | |].
  - cbn. rewrite cmpz_record_move_inl, IH. lia.
  - cbn. rewrite cmpz_record_move_inr, IH. lia.
Qed.

(** A joint certificate: the record has got to a point above a point p of the
    left floor-escaping part and a point q of the right one.  It costs
    the sum. *)
Theorem cmpz_prod_joint_certificate : forall p q s0 tr,
  axi_clean cmpz_iface s0 ->
  ~ bp_le P p (axi_floor I1) -> ~ bp_le Q q (axi_floor I2) ->
  bp_le (cmpz_pair_pre P Q) (p, q) (am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr s0)) ->
  ax_record_moves cmpz_iface tr >= 6 /\
  axi_ledger cmpz_iface (am_run (cmpz_prod M N) tr s0) >= axi_ledger cmpz_iface s0 + 6.
Proof.
  intros p q s0 tr [Hc1 Hc2] Hp Hq Hle.
  rewrite cmpz_run_prod in Hle. cbn in Hle. apply cmpz_pair_le in Hle. cbn in Hle.
  destruct Hle as [Hl Hr].
  destruct (ax_tc_every_point_priced I1 H1 p Hp (fst s0) (cmpz_lefts tr) Hc1 Hl) as [Ha _].
  destruct (ax_tc_every_point_priced I2 H2 q Hq (snd s0) (cmpz_rights tr) Hc2 Hr) as [Hb _].
  pose proof (cmpz_record_moves_prod tr) as E.
  split; [lia |].
  rewrite cmpz_prod_ledger_counts. lia.
Qed.

(** And six is attained: a certificate of each part, one after the other. *)
Theorem cmpz_prod_joint_certificate_tight : forall a1 b1 a2 b2 c1 chk1 cmt1 crt1 c2 chk2 cmt2 crt2,
  axi_kind I1 chk1 = T.KCheck c1 -> axi_kind I1 cmt1 = T.KCommit c1 -> axi_kind I1 crt1 = T.KCertify ->
  axi_kind I2 chk2 = T.KCheck c2 -> axi_kind I2 cmt2 = T.KCommit c2 -> axi_kind I2 crt2 = T.KCertify ->
  (forall a b, bp_le P (axi_point I1 c1) (am_rec M (am_run M [chk1; cmt1; crt1] (ax_load I1 a b)))
               <-> axi_meaning I1 c1 (ax_load I1 a b)) ->
  (forall a b, bp_le Q (axi_point I2 c2) (am_rec N (am_run N [chk2; cmt2; crt2] (ax_load I2 a b)))
               <-> axi_meaning I2 c2 (ax_load I2 a b)) ->
  axi_meaning I1 c1 (ax_load I1 a1 b1) -> axi_meaning I2 c2 (ax_load I2 a2 b2) ->
  let s0 := (ax_load I1 a1 b1, ax_load I2 a2 b2) in
  let tr := [inl chk1; inl cmt1; inl crt1; inr chk2; inr cmt2; inr crt2] in
  axi_clean cmpz_iface s0 /\
  ax_record_moves cmpz_iface tr = 6 /\
  bp_le (cmpz_pair_pre P Q) (axi_point I1 c1, axi_point I2 c2)
        (am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr s0)).
Proof.
  intros a1 b1 a2 b2 c1 chk1 cmt1 crt1 c2 chk2 cmt2 crt2 K1 K2 K3 K4 K5 K6 Hi1 Hi2 Hm1 Hm2 s0 tr.
  unpack.
  split; [cbn; split; apply (Hcl1 a1 b1) || apply (Hcl2 a2 b2) |].
  split.
  - rewrite cmpz_record_moves_prod. cbn. unfold ax_record_move. rewrite K1, K2, K3, K4, K5, K6. reflexivity.
  - rewrite cmpz_run_prod. cbn. apply cmpz_pair_le. cbn. split.
    + apply Hi1. exact Hm1.
    + apply Hi2. exact Hm2.
Qed.

End ProdTC.

Corollary cmpz_prod_thiele_complete : forall {A B P Q} (M : amachine A P) (N : amachine B Q),
  ax_thiele_complete M -> ax_thiele_complete N -> ax_thiele_complete (cmpz_prod M N).
Proof.
  intros A B P Q M N [I1 H1] [I2 H2]. exists (cmpz_iface I1 I2). exact (cmpz_prod_tc I1 I2 H1 H2).
Qed.

(** * The one-bit readings of the product *)

Section OneBit.

Context {A B : Type} {P : BPre A} {Q : BPre B} {M : amachine A P} {N : amachine B Q}.
Variable I1 : ax_interface M.
Variable I2 : ax_interface N.
Hypothesis H1 : ax_tc_with I1.
Hypothesis H2 : ax_tc_with I2.

(** "Some part has left its floor." *)
Definition cmpz_or_bit (s : am_state (cmpz_prod M N)) : bool :=
  orb (ax_flag_fn I1 (fst s)) (ax_flag_fn I2 (snd s)).

Lemma cmpz_or_bit_iff : forall s,
  cmpz_or_bit s = true <-> ~ bp_le (cmpz_pair_pre P Q) (am_rec (cmpz_prod M N) s) (axi_floor (cmpz_iface I1 I2)).
Proof.
  intro s. unfold cmpz_or_bit, ax_flag_fn. unfold bp_le. cbn.
  destruct (bp_leb A P (am_rec M (fst s)) (axi_floor I1)),
           (bp_leb B Q (am_rec N (snd s)) (axi_floor I2)); cbn;
    split; intro H; try reflexivity; try (intro H'; discriminate);
    try (exfalso; apply H; reflexivity); try discriminate.
Qed.

(** Certification of the product, read as one bit that is up when either part
    has certified, is Thiele-complete in the book's sense, with the product
    interface. *)
Theorem cmpz_or_view_complete :
  T.thiele_complete_with (ax_ti_pt (cmpz_iface I1 I2) cmpz_or_bit).
Proof.
  apply (ax_pt_view_complete (cmpz_iface I1 I2) (cmpz_prod_tc I1 I2 H1 H2)).
  exact cmpz_or_bit_iff.
Qed.

(** "Every part has left its floor." *)
Definition cmpz_and_bit (s : am_state (cmpz_prod M N)) : bool :=
  andb (ax_flag_fn I1 (fst s)) (ax_flag_fn I2 (snd s)).

Lemma cmpz_record_moves_le_length : forall {A' P'} {X : amachine A' P'} (I : ax_interface X) tr,
  ax_record_moves I tr <= length tr.
Proof.
  intros A' P' X I tr. induction tr as [| m tr IH]; simpl; [lia |].
  unfold ax_record_move. destruct (axi_kind I m); simpl; lia.
Qed.

(** Every run that raises "both parts have certified" from a clean start has
    at least 6 record moves. *)
Theorem cmpz_and_costs_six : forall (tr : list (am_move (cmpz_prod M N))) s0,
  axi_clean (cmpz_iface I1 I2) s0 ->
  cmpz_and_bit (am_run (cmpz_prod M N) tr s0) = true ->
  ax_record_moves (cmpz_iface I1 I2) tr >= 6.
Proof.
  intros tr s0 [Hc1 Hc2] Hup.
  unfold cmpz_and_bit in Hup. apply andb_true_iff in Hup. destruct Hup as [F1 F2].
  rewrite cmpz_run_prod_fst in F1. rewrite cmpz_run_prod_snd in F2.
  apply (flag_fn_Hr I1) in F1. apply (flag_fn_Hr I2) in F2.
  destruct (ax_tc_certificate_three I1 H1 _ _ Hc1 F1) as [R1 _].
  destruct (ax_tc_certificate_three I2 H2 _ _ Hc2 F2) as [R2 _].
  pose proof (cmpz_record_moves_prod I1 I2 tr) as E. lia.
Qed.

(** The one-bit reading "both parts have certified" cannot be Thiele-complete
    with this interface: every run that raises it from a clean start has at
    least 6 record moves, and the definition asks for a certificate of three
    moves. *)
Theorem cmpz_and_not_complete :
  ~ T.non_vacuity_clause (ax_ti_pt (cmpz_iface I1 I2) cmpz_and_bit).
Proof.
  intros [c [chk [cmt [crt [_ [_ [_ [Hiff [[a [b Hyes]] _]]]]]]]]].
  pose proof (proj2 (Hiff a b) Hyes) as Hup.
  change (cmpz_and_bit (T.run (am_pt (cmpz_prod M N) cmpz_and_bit) [chk; cmt; crt]
            (ax_load (cmpz_iface I1 I2) a b)) = true) in Hup.
  rewrite run_pt in Hup.
  assert (Hcl : axi_clean (cmpz_iface I1 I2) (ax_load (cmpz_iface I1 I2) a b)).
  { split; [apply (proj1 (proj2 (proj1 H1))) | apply (proj1 (proj2 (proj1 H2)))]. }
  pose proof (cmpz_and_costs_six [chk; cmt; crt] _ Hcl Hup) as H6.
  pose proof (cmpz_record_moves_le_length (cmpz_iface I1 I2) [chk; cmt; crt]) as Hl.
  cbn [length] in Hl. lia.
Qed.

End OneBit.

(** * Two programs at once *)

Lemma cmpz_prog_trace : forall {A' P'} {X : amachine A' P'} (U : T.universal_base (am_bare X)) n Pg s,
  exists tr : list (am_move X), am_run X tr s = T.prog_run U n Pg s.
Proof.
  intros A' P' X U n. induction n as [| n IH]; intros Pg s.
  - exists []. reflexivity.
  - cbn. destruct (T.cm_fetch Pg (fst (T.ub_window U s))) as [i |].
    + destruct (IH Pg (T.m_step (am_bare X) s (T.ub_compile U i))) as [tr Htr].
      exists ((T.ub_compile U i : am_move X) :: tr). rewrite am_run_cons. exact Htr.
    + exists []. reflexivity.
Qed.

Section TwoPrograms.

Context {A B : Type} {P : BPre A} {Q : BPre B} (M : amachine A P) (N : amachine B Q).

Lemma cmpz_lefts_map_inl : forall {X Y} (l : list X), cmpz_lefts (map (@inl X Y) l) = l.
Proof. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.
Lemma cmpz_rights_map_inl : forall {X Y} (l : list X), cmpz_rights (map (@inl X Y) l) = [].
Proof. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.
Lemma cmpz_lefts_map_inr : forall {X Y} (l : list Y), cmpz_lefts (map (@inr X Y) l) = [].
Proof. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.
Lemma cmpz_rights_map_inr : forall {X Y} (l : list Y), cmpz_rights (map (@inr X Y) l) = l.
Proof. induction l; simpl; [reflexivity | rewrite IHl; reflexivity]. Qed.

(** The product, started with the two components loaded with (a, b) and
    (c, d), runs a counter program on each window at once.  Any interleaving
    of the two compiled traces gives the same pair, because the components
    do not touch each other. *)
Theorem cmpz_prod_runs_two :
  forall (u1 : T.universal_base (am_bare M)) (u2 : T.universal_base (am_bare N))
         P1 P2 n1 n2 a b c d,
  exists tr : list (am_move (cmpz_prod M N)),
    T.ub_window u1 (fst (am_run (cmpz_prod M N) tr (T.ub_load u1 a b, T.ub_load u2 c d)))
      = T.cm_run n1 P1 (1, (a, b)) /\
    T.ub_window u2 (snd (am_run (cmpz_prod M N) tr (T.ub_load u1 a b, T.ub_load u2 c d)))
      = T.cm_run n2 P2 (1, (c, d)) /\
    T.ub_live u1 (fst (am_run (cmpz_prod M N) tr (T.ub_load u1 a b, T.ub_load u2 c d))) /\
    T.ub_live u2 (snd (am_run (cmpz_prod M N) tr (T.ub_load u1 a b, T.ub_load u2 c d))).
Proof.
  intros u1 u2 P1 P2 n1 n2 a b c d.
  destruct (cmpz_prog_trace u1 n1 P1 (T.ub_load u1 a b)) as [tr1 H1].
  destruct (cmpz_prog_trace u2 n2 P2 (T.ub_load u2 c d)) as [tr2 H2].
  exists (map inl tr1 ++ map inr tr2).
  rewrite cmpz_run_prod. cbn [fst snd].
  rewrite cmpz_lefts_app, cmpz_rights_app, cmpz_lefts_map_inl, cmpz_rights_map_inl,
          cmpz_lefts_map_inr, cmpz_rights_map_inr.
  rewrite app_nil_r, app_nil_l. rewrite H1, H2.
  pose proof (T.base_runs_every_program (am_bare M) u1 n1 P1 (T.ub_load u1 a b)
                (T.ub_load_live u1 a b)) as [W1 L1].
  pose proof (T.base_runs_every_program (am_bare N) u2 n2 P2 (T.ub_load u2 c d)
                (T.ub_load_live u2 c d)) as [W2 L2].
  rewrite (T.ub_load_window u1) in W1. rewrite (T.ub_load_window u2) in W2.
  auto.
Qed.

End TwoPrograms.

(** * The book's machines: the one-bit product *)

Definition cmpz_or (M0 N0 : T.machine) : T.machine :=
  T.mk_machine (T.m_state M0 * T.m_state N0) (T.m_move M0 + T.m_move N0)
    (fun s m => match m with
                | inl x => (T.m_step M0 (fst s) x, snd s)
                | inr y => (fst s, T.m_step N0 (snd s) y)
                end)
    (fun m => match m with inl x => T.m_cost M0 x | inr y => T.m_cost N0 y end)
    (fun s => orb (T.m_record M0 (fst s)) (T.m_record N0 (snd s))).

Theorem cmpz_or_thiele_complete : forall M0 N0 : T.machine,
  T.thiele_complete M0 -> T.thiele_complete N0 -> T.thiele_complete (cmpz_or M0 N0).
Proof.
  intros M0 N0 [J1 HJ1] [J2 HJ2].
  pose proof (proj1 (ax_tc_two_point_iff M0 J1) HJ1) as H1.
  pose proof (proj1 (ax_tc_two_point_iff N0 J2) HJ2) as H2.
  pose proof (cmpz_prod_tc (lift_ai J1) (lift_ai J2) H1 H2) as Hp.
  assert (Hr : forall s : am_state (cmpz_prod (lift_am M0) (lift_am N0)),
    orb (T.m_record M0 (fst s)) (T.m_record N0 (snd s)) = true <->
    ~ bp_le (cmpz_pair_pre two_pre two_pre) (am_rec (cmpz_prod (lift_am M0) (lift_am N0)) s)
        (axi_floor (cmpz_iface (lift_ai J1) (lift_ai J2)))).
  { intros [s1 s2]. unfold bp_le. cbn.
    destruct (T.m_record M0 s1), (T.m_record N0 s2); cbn;
      split; intro H; try reflexivity; try (intro H'; discriminate);
      try (exfalso; apply H; reflexivity); try discriminate. }
  exists (ax_ti_pt (cmpz_iface (lift_ai J1) (lift_ai J2))
            (fun s => orb (T.m_record M0 (fst s)) (T.m_record N0 (snd s)))).
  exact (ax_pt_view_complete (cmpz_iface (lift_ai J1) (lift_ai J2)) Hp _ Hr).
Qed.

Print Assumptions cmpz_prod_tc.
Print Assumptions cmpz_prod_thiele_complete.
Print Assumptions cmpz_or_view_complete.
Print Assumptions cmpz_prod_ledger_counts.
Print Assumptions cmpz_prod_joint_certificate.
Print Assumptions cmpz_prod_joint_certificate_tight.
Print Assumptions cmpz_and_costs_six.
Print Assumptions cmpz_and_not_complete.
Print Assumptions cmpz_prod_runs_two.
Print Assumptions cmpz_or_thiele_complete.
