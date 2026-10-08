(** Proved outcomes for the monotone multi-valued record targets of
    [GrowingRecordCore]. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import StructuralCore StructuralCoreAnyBase GrowingRecordCore.

Theorem growing_record_decomposes_holds : growing_record_decomposes.
Proof.
  intros M B C A P rec [Hdriven [Hgrows [Hpriced Hwrite]]].
  destruct Hdriven as [f Hf].
  exists (fun a b x => andb (negb (gr_leq P a x)) (gr_leq P a (f b x))).
  split; [| exact Hpriced].
  intros m a. rewrite Hf.
  specialize (Hgrows m).
  destruct (gr_leq P a (rec m)) eqn:Hbefore;
    destruct (gr_leq P a (f (base_state M B C m) (rec m))) eqn:Hafter;
    simpl; try reflexivity.
  exfalso.
  rewrite Hf in Hgrows.
  pose proof (@gr_leq_trans A P a (rec m)
    (f (base_state M B C m) (rec m)) Hbefore Hgrows).
  congruence.
Qed.

Theorem thresholds_determine_record_holds : thresholds_determine_record.
Proof.
  intros A P x y H.
  apply (@gr_leq_antisym A P x y).
  - rewrite <- (H x). apply (@gr_leq_refl A P).
  - rewrite (H y). apply (@gr_leq_refl A P).
Qed.

Theorem record_price_iff_threshold_price_holds : record_price_iff_threshold_price.
Proof.
  intros M A P rec Hgrows. split.
  - intros [Hledger Hprice]. split; [exact Hledger |].
    intros m a Hbefore Hafter. apply Hprice.
    intro Heq. rewrite Heq in Hbefore. congruence.
  - intros [Hledger Hprice]. split; [exact Hledger |].
    intros m Hneq.
    apply (Hprice m (rec (rc_next M m))).
    + destruct (gr_leq P (rec (rc_next M m)) (rec m)) eqn:Hback;
        [| reflexivity].
      exfalso. apply Hneq.
      apply (@gr_leq_antisym A P); [apply Hgrows | exact Hback].
    + apply (@gr_leq_refl A P).
Qed.

(** A fully priced three-value growing record over a one-state base. *)
Inductive Three : Type := three0 | three1 | three2.

Definition three_leq (x y : Three) : bool :=
  match x, y with
  | three0, _ => true
  | three1, three0 => false
  | three1, _ => true
  | three2, three2 => true
  | three2, _ => false
  end.

Definition ThreeOrder : BoolPartialOrder Three.
Proof.
  refine {| gr_leq := three_leq |}.
  - intros []; reflexivity.
  - intros [] []; simpl; intros; try discriminate; reflexivity.
  - intros [] [] []; simpl; intros; try discriminate; reflexivity.
Defined.

Definition three_next (x : Three) : Three :=
  match x with three0 => three1 | three1 => three2 | three2 => three2 end.

Definition three_rank (x : Three) : nat :=
  match x with three0 => 0 | three1 => 1 | three2 => 2 end.

Definition ThreeMachine : RCM := {|
  rc_state := Three;
  rc_next := three_next;
  rc_init := fun x => x = three0;
  rc_cert := fun _ => false;
  rc_mu := three_rank;
  rc_halted := fun _ => False
|}.

Definition OneBase : BaseMachine := {|
  b_state := unit;
  b_next := fun _ => tt;
  b_init := fun _ => True;
  b_halted := fun _ => False
|}.

Definition ThreeCover : BaseCover ThreeMachine OneBase.
Proof.
  refine (@Build_BaseCover ThreeMachine OneBase (fun _ => tt) _ _ _ _).
  - intros; exact I.
  - intros [] _. exists three0. split; reflexivity.
  - intros []; reflexivity.
  - intros []; split; contradiction.
Defined.

Lemma three_honest :
  HonestGrowingExtension ThreeMachine OneBase ThreeCover ThreeOrder (fun x => x).
Proof.
  split.
  - exists (fun _ x => three_next x). intros []; reflexivity.
  - split.
    + intros []; reflexivity.
    + split.
      * split.
        -- intros []; simpl; lia.
        -- intros [] Hneq; unfold step_cost; simpl in *; try contradiction; lia.
      * exists three0, 0. split; [reflexivity | discriminate].
Qed.

Theorem one_latch_refuted : ~ one_latch_suffices.
Proof.
  intro Hall.
  specialize (Hall ThreeMachine OneBase ThreeCover Three ThreeOrder
    (fun x => x) three_honest).
  destruct Hall as [h [latch [decode [_ Hdecode]]]].
  specialize (Hdecode three0) as H0.
  specialize (Hdecode three1) as H1.
  specialize (Hdecode three2) as H2.
  simpl in H0, H1, H2.
  destruct (latch three0), (latch three1), (latch three2); congruence.
Qed.

(** Boolean-vector rank lemmas for the finite lower bound. *)
Definition bit_count (u : list bool) : nat := count_occ Bool.bool_dec u true.

Lemma bits_le_trans : forall u v w,
  bits_le u v -> bits_le v w -> bits_le u w.
Proof.
  intros u v w [HuvL Huv] [HvwL Hvw]. split; [lia |].
  intros n Hn. apply Hvw, Huv, Hn.
Qed.

Lemma bits_le_tails : forall a u b v,
  bits_le (a :: u) (b :: v) -> bits_le u v.
Proof.
  intros a u b v [Hlen Hbits]. split; [simpl in Hlen; lia |].
  intros n Hn. apply (Hbits (S n)). exact Hn.
Qed.

Lemma bits_le_count_le : forall u v,
  bits_le u v -> bit_count u <= bit_count v.
Proof.
  induction u as [|a u IH]; intros v Hle.
  - destruct Hle as [Hlen _]. destruct v; simpl in *; [lia | discriminate].
  - destruct v as [|b v]; [destruct Hle as [Hlen _]; discriminate |].
    pose proof (bits_le_tails a u b v Hle) as Htail.
    specialize (IH v Htail).
    destruct Hle as [_ Hbits].
    unfold bit_count in *. simpl.
    destruct a, b; simpl in *; try lia.
    exfalso. specialize (Hbits 0 eq_refl). discriminate.
Qed.

Lemma bits_le_count_eq : forall u v,
  bits_le u v -> bit_count u = bit_count v -> u = v.
Proof.
  induction u as [|a u IH]; intros v Hle Hcount.
  - destruct Hle as [Hlen _]. destruct v; [reflexivity | discriminate].
  - destruct v as [|b v]; [destruct Hle as [Hlen _]; discriminate |].
    destruct a, b.
    + change (S (bit_count u) = S (bit_count v)) in Hcount.
      pose proof (bits_le_tails true u true v Hle) as Htail.
      assert (Htail_count : bit_count u = bit_count v) by lia.
      assert (Hu : u = v).
      { apply IH; assumption. }
      now subst.
    + destruct Hle as [_ Hbits].
      exfalso. specialize (Hbits 0 eq_refl). discriminate.
    + change (bit_count u = S (bit_count v)) in Hcount.
      pose proof (bits_le_tails false u true v Hle) as Htail.
      pose proof (bits_le_count_le u v Htail) as Htail_count.
      exfalso. lia.
    + change (bit_count u = bit_count v) in Hcount.
      pose proof (bits_le_tails false u false v Hle) as Htail.
      assert (Hu : u = v) by (apply IH; assumption).
      now subst.
Qed.

Lemma bits_chain_head : forall u rest v,
  bits_chain (u :: rest) -> In v rest -> bits_le u v.
Proof.
  intros u rest. revert u.
  induction rest as [|x rest IH]; intros u v Hchain Hin; [contradiction |].
  simpl in Hchain. destruct rest as [|y rest'].
  - simpl in Hin. destruct Hin as [<- | []]. exact (proj1 Hchain).
  - destruct Hchain as [Hux Htail].
    simpl in Hin. destruct Hin as [<- | Hin]; [exact Hux |].
    eapply bits_le_trans; [exact Hux |].
    apply (IH x v); [exact Htail | exact Hin].
Qed.

Lemma bits_chain_tail : forall u rest,
  bits_chain (u :: rest) -> bits_chain rest.
Proof.
  intros u [|v rest] Hchain; [exact I |].
  destruct rest; simpl in *; tauto.
Qed.

Lemma bits_chain_counts_nodup : forall vs,
  bits_chain vs -> NoDup vs -> NoDup (map bit_count vs).
Proof.
  induction vs as [|u rest IH]; intros Hchain Hnodup; simpl; [constructor |].
  inversion Hnodup as [|? ? Hnotin Hrest]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin.
    destruct Hin as [v [Hcount Hin]].
    apply Hnotin.
    assert (Heq : u = v).
    { apply (bits_le_count_eq u v).
      - apply (bits_chain_head u rest v Hchain Hin).
      - symmetry. exact Hcount. }
    now subst.
  - exact (IH (bits_chain_tail u rest Hchain) Hrest).
Qed.

Lemma bit_count_le_length : forall u, bit_count u <= length u.
Proof.
  induction u as [|a u IH].
  - unfold bit_count. simpl. lia.
  - unfold bit_count in *. simpl. destruct a; simpl; lia.
Qed.

Theorem chain_needs_bits_holds : chain_needs_bits.
Proof.
  intros k vs Hlengths Hchain Hnodup.
  assert (Hcounts : NoDup (map bit_count vs)).
  { apply bits_chain_counts_nodup; assumption. }
  assert (Hincl : incl (map bit_count vs) (seq 0 (S k))).
  { intros n Hin. apply in_map_iff in Hin.
    destruct Hin as [u [<- Hin]].
    apply in_seq. split; [lia |].
    apply Nat.lt_succ_r.
    assert (Hu : length u = k).
    { rewrite Forall_forall in Hlengths. apply Hlengths. exact Hin. }
    rewrite <- Hu.
    apply bit_count_le_length. }
  rewrite <- (map_length bit_count vs), <- (seq_length (S k) 0).
  apply NoDup_incl_length; [exact Hcounts | exact Hincl].
Qed.

Print Assumptions growing_record_decomposes_holds.
Print Assumptions thresholds_determine_record_holds.
Print Assumptions record_price_iff_threshold_price_holds.
Print Assumptions one_latch_refuted.
Print Assumptions chain_needs_bits_holds.
