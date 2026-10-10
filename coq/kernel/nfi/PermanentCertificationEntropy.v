(** PermanentCertificationEntropy: the permanent-certificate bound in bits.

    [PermanentRecordPricing] counts states: on a finite machine whose
    certificate no step revokes, a step that switches [k] states on beside
    [m] certified ones squeezes [m + k] states into at most [m]. This file
    says the same thing in Shannon entropy.

    Put any probability distribution on the states that are certified or
    about to flip. The step sends all of them into the [m] certified states,
    so the distribution after the step has entropy at most [log2 m]. The
    drop in entropy is at least [H(p) - log2 m]. For the uniform
    distribution on those [m + k] states the drop is at least
    [log2 ((m + k) / m)] bits, the same number the counting bound gives.

    Landauer's principle is the physical premise, named here and not
    proved: a step that lowers the entropy of the machine's state by [dH]
    bits dissipates at least [kT ln 2 * dH] of heat. Under that premise a
    permanent flip of [k] states dissipates at least [kT ln ((m + k) / m)],
    which is strictly positive when [k >= 1] and the temperature is
    positive.

    Landauer's principle prices the entropy removed from the actual
    distribution, not a merge as such. So the file also says exactly when
    a step removes entropy. The drop is a sum of one nonnegative term per
    state, and it is positive when two states of positive probability land
    in the same place. For any distribution that gives every certified state
    and the flipping state positive probability, a permanent flip removes
    entropy and, under the premise, dissipates positive heat. And a state
    known in advance loses nothing: the step removes no entropy and the
    premise forces no heat. The heat comes from uncertainty about which
    state the machine is in. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Reals Lra Permutation.
From Coq Require FinFun.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.

Open Scope R_scope.

(** * Finite sums *)

Definition rsum {A : Type} (l : list A) (g : A -> R) : R :=
  fold_right (fun a acc => g a + acc) 0 l.

Lemma rsum_nil : forall {A} (g : A -> R), rsum [] g = 0.
Proof. reflexivity. Qed.

Lemma rsum_cons : forall {A} (a : A) l g, rsum (a :: l) g = g a + rsum l g.
Proof. reflexivity. Qed.

Lemma rsum_ext_in :
  forall {A} (l : list A) g h,
    (forall a, In a l -> g a = h a) -> rsum l g = rsum l h.
Proof.
  intros A l g h H. induction l as [| a l IH]; [reflexivity |].
  rewrite !rsum_cons, (H a (or_introl eq_refl)), IH; [reflexivity |].
  intros b Hb. apply H. right. exact Hb.
Qed.

Lemma rsum_le :
  forall {A} (l : list A) g h,
    (forall a, In a l -> g a <= h a) -> rsum l g <= rsum l h.
Proof.
  intros A l g h H. induction l as [| a l IH]; [simpl; lra |].
  rewrite !rsum_cons.
  assert (H1 := H a (or_introl eq_refl)).
  assert (H2 : rsum l g <= rsum l h) by (apply IH; intros b Hb; apply H; right; exact Hb).
  lra.
Qed.

Lemma rsum_nonneg :
  forall {A} (l : list A) g, (forall a, 0 <= g a) -> 0 <= rsum l g.
Proof.
  intros A l g H. induction l as [| a l IH]; simpl; [lra |].
  specialize (H a). lra.
Qed.

Lemma rsum_plus :
  forall {A} (l : list A) g h,
    rsum l (fun a => g a + h a) = rsum l g + rsum l h.
Proof. intros A l g h. induction l as [| a l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma rsum_minus :
  forall {A} (l : list A) g h,
    rsum l (fun a => g a - h a) = rsum l g - rsum l h.
Proof. intros A l g h. induction l as [| a l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma rsum_scal :
  forall {A} (l : list A) c g,
    rsum l (fun a => c * g a) = c * rsum l g.
Proof. intros A l c g. induction l as [| a l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma rsum_zero :
  forall {A} (l : list A) g, (forall a, In a l -> g a = 0) -> rsum l g = 0.
Proof.
  intros A l g H. rewrite (rsum_ext_in l g (fun _ => 0) H).
  induction l as [| a l IH]; simpl; [lra |]. rewrite IH; [lra |].
  intros b Hb. apply H. right. exact Hb.
Qed.

(** A sum of a constant over the members that pass a test. *)
Lemma rsum_indicator :
  forall {A} (l : list A) (P : A -> bool) c,
    rsum l (fun a => if P a then c else 0) = INR (length (filter P l)) * c.
Proof.
  intros A l P c. induction l as [| a l IH]; simpl; [lra |].
  rewrite IH. destruct (P a); simpl length; [rewrite S_INR |]; lra.
Qed.

Lemma rsum_swap :
  forall {A B} (la : list A) (lb : list B) (g : A -> B -> R),
    rsum la (fun a => rsum lb (fun b => g a b)) =
    rsum lb (fun b => rsum la (fun a => g a b)).
Proof.
  intros A B la lb g. induction la as [| a la IH]; simpl.
  - symmetry. apply rsum_zero. intros. reflexivity.
  - rewrite IH, <- rsum_plus. reflexivity.
Qed.

(** * Logarithm and entropy *)

Definition log2 (t : R) : R := ln t / ln 2.

Lemma ln2_pos : 0 < ln 2.
Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

Lemma ln_le_minus_one : forall y, 0 < y -> ln y <= y - 1.
Proof.
  intros y Hy. assert (H := exp_ineq1_le (ln y)). rewrite exp_ln in H by exact Hy. lra.
Qed.

(** The contribution of one state to Shannon entropy, in bits, with the
    usual convention that a state of probability zero contributes nothing. *)
Definition surprisal_term (t : R) : R :=
  if Rlt_dec 0 t then - (t * log2 t) else 0.

Definition entropy {A} (l : list A) (r : A -> R) : R :=
  rsum l (fun a => surprisal_term (r a)).

Definition distribution {A} (l : list A) (r : A -> R) : Prop :=
  (forall a, 0 <= r a) /\ rsum l r = 1.

Definition positive_b (t : R) : bool := if Rlt_dec 0 t then true else false.

(** Entropy is at most the logarithm of the size of any list that covers
    the support. *)
Theorem entropy_le_log_support :
  forall {A} (l Sup : list A) (r : A -> R),
    NoDup l ->
    distribution l r ->
    (forall a, In a l -> 0 < r a -> In a Sup) ->
    (0 < length Sup)%nat ->
    entropy l r <= log2 (INR (length Sup)).
Proof.
  intros A l Sup r Hnd [Hnn Hsum] Hsupp HSup.
  set (M := INR (length Sup)).
  assert (HM : 0 < M) by (apply lt_0_INR; exact HSup).
  set (g := fun a => (if positive_b (r a) then / M else 0) - r a).
  assert (Hpt : forall a, surprisal_term (r a) - log2 M * r a <= g a / ln 2).
  { intro a. unfold surprisal_term, g, positive_b, log2.
    pose proof ln2_pos as Hl2.
    destruct (Rlt_dec 0 (r a)) as [Hpos | Hnpos].
    - assert (Hy : 0 < / (M * r a)) by (apply Rinv_0_lt_compat; nra).
      assert (Hln := ln_le_minus_one (/ (M * r a)) Hy).
      rewrite ln_Rinv in Hln by nra.
      rewrite ln_mult in Hln by lra.
      assert (Hstep : r a * (- (ln M + ln (r a))) <= / M - r a).
      { replace (/ M - r a) with (r a * (/ (M * r a) - 1)) by (field; split; lra).
        apply Rmult_le_compat_l; lra. }
      assert (Hil : 0 < / ln 2) by (apply Rinv_0_lt_compat; exact Hl2).
      cbv iota beta.
      replace (- (r a * (ln (r a) / ln 2)) - ln M / ln 2 * r a)
        with (r a * (- (ln M + ln (r a))) * / ln 2) by (field; lra).
      unfold Rdiv. apply Rmult_le_compat_r; lra.
    - assert (Hz : r a = 0) by (specialize (Hnn a); lra).
      cbv iota beta. rewrite Hz. unfold Rdiv. lra. }
  assert (Hsumle : rsum l (fun a => surprisal_term (r a) - log2 M * r a)
                   <= rsum l (fun a => g a / ln 2))
    by (apply rsum_le; intros a _; apply Hpt).
  rewrite rsum_minus, rsum_scal, Hsum in Hsumle.
  unfold Rdiv in Hsumle. rewrite (rsum_ext_in l (fun a => g a * / ln 2)
                                    (fun a => / ln 2 * g a)) in Hsumle
    by (intros; lra).
  rewrite rsum_scal in Hsumle.
  unfold g in Hsumle. rewrite rsum_minus, Hsum, rsum_indicator in Hsumle.
  assert (Hcount : (length (filter (fun a => positive_b (r a)) l) <= length Sup)%nat).
  { apply NoDup_incl_length; [apply NoDup_filter; exact Hnd |].
    intros a Ha. apply filter_In in Ha as [Hal Hpa].
    apply Hsupp; [exact Hal |].
    unfold positive_b in Hpa. destruct (Rlt_dec 0 (r a)); [assumption | discriminate]. }
  apply le_INR in Hcount. fold M in Hcount.
  assert (Hfrac : INR (length (filter (fun a => positive_b (r a)) l)) * / M - 1 <= 0).
  { apply Rmult_le_compat_r with (r := / M) in Hcount;
      [| left; apply Rinv_0_lt_compat; exact HM].
    rewrite Rinv_r in Hcount by lra. lra. }
  assert (Hneg : / ln 2 * (INR (length (filter (fun a => positive_b (r a)) l)) * / M - 1) <= 0).
  { assert (Hil : 0 < / ln 2) by (apply Rinv_0_lt_compat, ln2_pos). nra. }
  unfold entropy. lra.
Qed.

(** * Uniform distributions and pushforwards *)

Section Distributions.

Context {A : Type}.
Variable eq_dec : forall a b : A, {a = b} + {a <> b}.

Definition in_b (U : list A) (a : A) : bool :=
  if in_dec eq_dec a U then true else false.

(** Uniform on the members of [U], zero elsewhere. *)
Definition uniform_on (U : list A) (a : A) : R :=
  if in_b U a then / INR (length U) else 0.

Lemma filter_in_b_length :
  forall (l U : list A),
    NoDup l -> NoDup U -> (forall a, In a U -> In a l) ->
    length (filter (in_b U) l) = length U.
Proof.
  intros l U Hl HU Hsub. apply Nat.le_antisymm.
  - apply NoDup_incl_length; [apply NoDup_filter; exact Hl |].
    intros a Ha. apply filter_In in Ha as [_ Hin].
    unfold in_b in Hin. destruct (in_dec eq_dec a U); [assumption | discriminate].
  - apply NoDup_incl_length; [exact HU |].
    intros a Ha. apply filter_In. split; [apply Hsub; exact Ha |].
    unfold in_b. destruct (in_dec eq_dec a U); [reflexivity | contradiction].
Qed.

Theorem uniform_on_distribution :
  forall (l U : list A),
    NoDup l -> NoDup U -> (forall a, In a U -> In a l) ->
    (0 < length U)%nat ->
    distribution l (uniform_on U).
Proof.
  intros l U Hl HU Hsub Hpos.
  assert (Hn : 0 < INR (length U)) by (apply lt_0_INR; exact Hpos).
  split.
  - intro a. unfold uniform_on. destruct (in_b U a);
      [left; apply Rinv_0_lt_compat; exact Hn | lra].
  - unfold uniform_on. rewrite rsum_indicator, filter_in_b_length by assumption.
    field. lra.
Qed.

(** The uniform distribution on [n] states carries [log2 n] bits. *)
Theorem uniform_on_entropy :
  forall (l U : list A),
    NoDup l -> NoDup U -> (forall a, In a U -> In a l) ->
    (0 < length U)%nat ->
    entropy l (uniform_on U) = log2 (INR (length U)).
Proof.
  intros l U Hl HU Hsub Hpos.
  assert (Hn : 0 < INR (length U)) by (apply lt_0_INR; exact Hpos).
  set (c := / INR (length U)).
  assert (Hc : 0 < c) by (apply Rinv_0_lt_compat; exact Hn).
  unfold entropy.
  rewrite (rsum_ext_in l (fun a => surprisal_term (uniform_on U a))
             (fun a => if in_b U a then - (c * log2 c) else 0)).
  - rewrite rsum_indicator, filter_in_b_length by assumption.
    unfold c, log2. rewrite ln_Rinv by exact Hn.
    field. split; [apply Rgt_not_eq, ln2_pos | lra].
  - intros a _. unfold uniform_on, surprisal_term. fold c.
    destruct (in_b U a).
    + destruct (Rlt_dec 0 c); [reflexivity | lra].
    + destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

(** The distribution after a deterministic step. *)
Definition push (all : list A) (f : A -> A) (p : A -> R) (y : A) : R :=
  rsum all (fun x => if eq_dec (f x) y then p x else 0).

Lemma filter_eq_length_one :
  forall (l : list A) b,
    NoDup l -> In b l ->
    length (filter (fun y => if eq_dec b y then true else false) l) = 1%nat.
Proof.
  intros l b Hnd Hin. induction l as [| a l IH]; [destruct Hin |].
  inversion Hnd as [| a' l' Hnot Hnd' ]; subst.
  simpl. destruct (eq_dec b a) as [<- | Hne].
  - simpl. f_equal.
    assert (Hnil : filter (fun y => if eq_dec b y then true else false) l = []).
    { clear IH Hin Hnd Hnd'.
      induction l as [| c l IHl]; [reflexivity |].
      simpl. destruct (eq_dec b c) as [<- | _].
      - exfalso. apply Hnot. left. reflexivity.
      - apply IHl. intro H. apply Hnot. right. exact H. }
    rewrite Hnil. reflexivity.
  - apply IH; [exact Hnd' |].
    destruct Hin as [-> | H]; [contradiction | exact H].
Qed.

Theorem push_distribution :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) ->
    distribution all p ->
    distribution all (push all f p).
Proof.
  intros all f p Hnd Hall [Hnn Hsum]. split.
  - intro y. unfold push. apply rsum_nonneg. intro x.
    destruct (eq_dec (f x) y); [apply Hnn | lra].
  - unfold push.
    rewrite (rsum_swap all all (fun y x => if eq_dec (f x) y then p x else 0)).
    rewrite <- Hsum. apply rsum_ext_in. intros x _.
    rewrite (rsum_ext_in all (fun y => if eq_dec (f x) y then p x else 0)
               (fun y => if (fun y => if eq_dec (f x) y then true else false) y
                         then p x else 0))
      by (intros y _; destruct (eq_dec (f x) y); reflexivity).
    rewrite rsum_indicator, filter_eq_length_one by auto.
    simpl. lra.
Qed.

(** If every state that the step can reach from the support of [p] lies in
    [C], the pushforward is supported in [C]. *)
Lemma push_support :
  forall (all C Sup : list A) (f : A -> A) (p : A -> R),
    (forall a, 0 <= p a) ->
    (forall x, In x all -> 0 < p x -> In x Sup) ->
    (forall x, In x Sup -> In (f x) C) ->
    forall y, In y all -> 0 < push all f p y -> In y C.
Proof.
  intros all C Sup f p Hnn Hsupp Hmap y _ Hpos.
  destruct (in_dec eq_dec y C) as [HyC | HyC]; [exact HyC |].
  exfalso.
  assert (Hzero : push all f p y = 0).
  { unfold push. apply rsum_zero. intros x Hx.
    destruct (eq_dec (f x) y) as [Hfx | _]; [| reflexivity].
    destruct (Rlt_dec 0 (p x)) as [Hp | Hp].
    - exfalso. apply HyC. rewrite <- Hfx. apply Hmap. apply Hsupp; assumption.
    - specialize (Hnn x). lra. }
  lra.
Qed.

Lemma rsum_permutation :
  forall (l l' : list A) g, Permutation l l' -> rsum l g = rsum l' g.
Proof.
  intros l l' g Hp. induction Hp; simpl; [reflexivity | rewrite IHHp; reflexivity | lra | congruence].
Qed.

Lemma rsum_map :
  forall (l : list A) (f : A -> A) g, rsum (map f l) g = rsum l (fun x => g (f x)).
Proof. intros l f g. induction l as [| a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** A step that forgets nothing moves the probability of each state to its
    image and leaves it whole. *)
Lemma push_injective_at :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) ->
    (forall x y, f x = f y -> x = y) ->
    forall x, push all f p (f x) = p x.
Proof.
  intros all f p Hnd Hall Hinj x. unfold push.
  rewrite (rsum_ext_in all (fun z => if eq_dec (f z) (f x) then p z else 0)
             (fun z => if (fun z => if eq_dec x z then true else false) z then p x else 0)).
  - rewrite rsum_indicator, filter_eq_length_one by auto. simpl. lra.
  - intros z _. destruct (eq_dec (f z) (f x)) as [Hfz | Hfz];
      destruct (eq_dec x z) as [Hxz | Hxz].
    + subst. reflexivity.
    + exfalso. apply Hxz. symmetry. exact (Hinj z x Hfz).
    + subst. contradiction.
    + reflexivity.
Qed.

(** Entropy is invariant under an injective step: a step that forgets
    nothing removes no bits. This is Bennett's side of the ledger. The
    reversible [FNext] of [FiniteCertMachine] is such a step, and an
    entropy price may leave it free. *)
Theorem step_entropy_invariant_if_injective :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) ->
    (forall x y, f x = f y -> x = y) ->
    entropy all (push all f p) = entropy all p.
Proof.
  intros all f p Hnd Hall Hinj. unfold entropy.
  assert (Hperm : Permutation all (map f all)).
  { apply NoDup_Permutation; [exact Hnd | |].
    - apply FinFun.Injective_map_NoDup; [exact Hinj | exact Hnd].
    - intro y. split; intros _; [| apply Hall].
      assert (Hlen : length (map f all) = length all) by apply map_length.
      destruct (in_dec eq_dec y (map f all)) as [Hin | Hout]; [exact Hin |].
      exfalso.
      assert (Hle : (length (y :: map f all) <= length all)%nat).
      { apply NoDup_incl_length.
        - constructor; [exact Hout |].
          apply FinFun.Injective_map_NoDup; [exact Hinj | exact Hnd].
        - intros z _. apply Hall. }
      simpl in Hle. lia. }
  rewrite (rsum_permutation all (map f all) _ Hperm), rsum_map.
  apply rsum_ext_in. intros x _. rewrite push_injective_at by assumption.
  reflexivity.
Qed.

(** * Entropy drop for any distribution

    Landauer's principle, in its modern form, prices the entropy the step
    removes from the actual distribution of states, not a merge as such. A
    merge of two states that are not both possible removes nothing. The
    results below say exactly when a deterministic step removes entropy: the
    drop is a sum of one term per state, each term is nonnegative, and a term
    is positive when another state of positive probability lands in the same
    place. A state that is known in advance loses nothing. *)

Lemma rsum_select :
  forall (l : list A) b (g : A -> R),
    NoDup l -> In b l ->
    rsum l (fun y => if eq_dec b y then g y else 0) = g b.
Proof.
  intros l b g Hnd Hin. induction l as [| a l IH]; [destruct Hin |].
  inversion Hnd as [| a' l' Hnot Hnd']; subst.
  rewrite rsum_cons. cbv beta. destruct (eq_dec b a) as [Heq | Hne].
  - subst a. rewrite rsum_zero; [lra |].
    intros y Hy. destruct (eq_dec b y) as [Hby | _]; [subst y; contradiction | reflexivity].
  - destruct Hin as [Hab | Hin]; [subst a; exfalso; apply Hne; reflexivity |].
    rewrite IH by assumption. lra.
Qed.

Lemma rsum_nonneg_in :
  forall (l : list A) g, (forall a, In a l -> 0 <= g a) -> 0 <= rsum l g.
Proof.
  intros l g H. rewrite <- (rsum_zero l (fun _ => 0)) by (intros; reflexivity).
  apply rsum_le. exact H.
Qed.

Lemma rsum_pos_witness :
  forall (l : list A) g,
    (forall a, In a l -> 0 <= g a) ->
    (exists a, In a l /\ 0 < g a) ->
    0 < rsum l g.
Proof.
  intros l g Hnn [a0 [Hin Hpos]]. induction l as [| a l IH]; [destruct Hin |].
  rewrite rsum_cons.
  assert (Hrest : 0 <= rsum l g)
    by (apply rsum_nonneg_in; intros b Hb; apply Hnn; right; exact Hb).
  assert (Ha : 0 <= g a) by (apply Hnn; left; reflexivity).
  destruct Hin as [<- | Hin]; [lra |].
  assert (Hl : 0 < rsum l g).
  { apply IH; [intros b Hb; apply Hnn; right; exact Hb | exact Hin]. }
  lra.
Qed.

Lemma ln_le_mono : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt | Heq].
  - left. apply ln_increasing; assumption.
  - subst y. lra.
Qed.

(** A state's probability never exceeds the probability of its image. *)
Lemma push_ge_point :
  forall (all : list A) (f : A -> A) (p : A -> R) x,
    NoDup all -> In x all -> (forall a, 0 <= p a) ->
    p x <= push all f p (f x).
Proof.
  intros all f p x Hnd Hin Hnn. unfold push.
  rewrite <- (rsum_select all x p Hnd Hin) at 1.
  apply rsum_le. intros z _.
  destruct (eq_dec x z) as [Hxz | Hne].
  - subst z. destruct (eq_dec (f x) (f x)) as [_ | Hc]; [lra | exfalso; apply Hc; reflexivity].
  - destruct (eq_dec (f z) (f x)); [apply Hnn | lra].
Qed.

(** Two distinct states with the same image both count toward it. *)
Lemma push_ge_two :
  forall (all : list A) (f : A -> A) (p : A -> R) x x',
    NoDup all -> In x all -> In x' all -> x <> x' -> f x = f x' ->
    (forall a, 0 <= p a) ->
    p x + p x' <= push all f p (f x).
Proof.
  intros all f p x x' Hnd Hin Hin' Hne Hff Hnn. unfold push.
  rewrite <- (rsum_select all x p Hnd Hin) at 1.
  rewrite <- (rsum_select all x' p Hnd Hin') at 1.
  rewrite <- rsum_plus. apply rsum_le. intros z _.
  destruct (eq_dec x z) as [Hxz | H1]; destruct (eq_dec x' z) as [Hx'z | H2].
  - exfalso. apply Hne. congruence.
  - subst z. destruct (eq_dec (f x) (f x)) as [_ | Hc]; [lra | exfalso; apply Hc; reflexivity].
  - subst z. rewrite Hff. destruct (eq_dec (f x') (f x')) as [_ | Hc];
      [lra | exfalso; apply Hc; reflexivity].
  - destruct (eq_dec (f z) (f x)); [specialize (Hnn z); lra | lra].
Qed.

(** The entropy after the step, written as a sum over the states before it. *)
Lemma push_entropy_as_point_sum :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    entropy all (push all f p) =
    rsum all (fun x => if Rlt_dec 0 (p x)
                       then - (p x * log2 (push all f p (f x))) else 0).
Proof.
  intros all f p Hnd Hall Hnn. unfold entropy.
  transitivity
    (rsum all (fun y => rsum all (fun x =>
       if eq_dec (f x) y
       then (if Rlt_dec 0 (p x) then - (p x * log2 (push all f p y)) else 0)
       else 0))).
  - apply rsum_ext_in. intros y _. unfold surprisal_term.
    destruct (Rlt_dec 0 (push all f p y)) as [Hq | Hq].
    + assert (Hdef : push all f p y = rsum all (fun x => if eq_dec (f x) y then p x else 0))
        by reflexivity.
      transitivity (rsum all (fun x => - log2 (push all f p y) * (if eq_dec (f x) y then p x else 0))).
      * rewrite rsum_scal. rewrite <- Hdef. ring.
      * apply rsum_ext_in. intros x _. destruct (eq_dec (f x) y); [| ring].
        destruct (Rlt_dec 0 (p x)); [ring |].
        assert (Hz : p x = 0) by (specialize (Hnn x); lra). rewrite Hz. ring.
    + symmetry. apply rsum_zero. intros x Hx.
      destruct (eq_dec (f x) y) as [Hfx | _]; [| reflexivity].
      destruct (Rlt_dec 0 (p x)) as [Hp | _]; [| reflexivity].
      exfalso. apply Hq. subst y.
      pose proof (push_ge_point all f p x Hnd Hx Hnn). lra.
  - pose proof (rsum_swap all all (fun y x =>
      if eq_dec (f x) y
      then (if Rlt_dec 0 (p x) then - (p x * log2 (push all f p y)) else 0)
      else 0)) as Hs.
    cbv beta in Hs. rewrite Hs.
    apply rsum_ext_in. intros x Hx.
    exact (rsum_select all (f x)
             (fun y => if Rlt_dec 0 (p x) then - (p x * log2 (push all f p y)) else 0)
             Hnd (Hall (f x))).
Qed.

(** The entropy a step removes, as one term per state. *)
Theorem entropy_drop_as_point_sum :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    entropy all p - entropy all (push all f p) =
    rsum all (fun x => if Rlt_dec 0 (p x)
                       then p x * (log2 (push all f p (f x)) - log2 (p x)) else 0).
Proof.
  intros all f p Hnd Hall Hnn.
  rewrite push_entropy_as_point_sum by assumption. unfold entropy.
  rewrite <- rsum_minus. apply rsum_ext_in. intros x _. unfold surprisal_term.
  destruct (Rlt_dec 0 (p x)); ring.
Qed.

Lemma entropy_drop_term_nonneg :
  forall (all : list A) (f : A -> A) (p : A -> R) x,
    NoDup all -> In x all -> (forall a, 0 <= p a) ->
    0 <= (if Rlt_dec 0 (p x)
          then p x * (log2 (push all f p (f x)) - log2 (p x)) else 0).
Proof.
  intros all f p x Hnd Hin Hnn.
  destruct (Rlt_dec 0 (p x)) as [Hp | _]; [| lra].
  pose proof (push_ge_point all f p x Hnd Hin Hnn) as Hq.
  assert (Hln : ln (p x) <= ln (push all f p (f x))) by (apply ln_le_mono; lra).
  unfold log2.
  replace (ln (push all f p (f x)) / ln 2 - ln (p x) / ln 2)
    with ((ln (push all f p (f x)) - ln (p x)) * / ln 2)
    by (field; apply Rgt_not_eq, ln2_pos).
  apply Rmult_le_pos; [lra |].
  apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat, ln2_pos].
Qed.

(** A deterministic step never raises entropy. *)
Theorem entropy_drop_nonneg :
  forall (all : list A) (f : A -> A) (p : A -> R),
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    entropy all p - entropy all (push all f p) >= 0.
Proof.
  intros all f p Hnd Hall Hnn.
  rewrite entropy_drop_as_point_sum by assumption.
  apply Rle_ge, rsum_nonneg_in. intros x Hx.
  apply entropy_drop_term_nonneg; assumption.
Qed.

(** The step removes entropy when two states of positive probability land
    in the same place. *)
Theorem entropy_drop_pos_of_support_merge :
  forall (all : list A) (f : A -> A) (p : A -> R) x x',
    NoDup all -> (forall a, In a all) -> (forall a, 0 <= p a) ->
    x <> x' -> f x = f x' -> 0 < p x -> 0 < p x' ->
    entropy all p - entropy all (push all f p) > 0.
Proof.
  intros all f p x x' Hnd Hall Hnn Hne Hff Hp Hp'.
  rewrite entropy_drop_as_point_sum by assumption.
  apply rsum_pos_witness.
  - intros z Hz. apply entropy_drop_term_nonneg; assumption.
  - exists x. split; [apply Hall |].
    destruct (Rlt_dec 0 (p x)) as [_ | Hc]; [| lra].
    pose proof (push_ge_two all f p x x' Hnd (Hall x) (Hall x') Hne Hff Hnn) as Hq.
    assert (Hln : ln (p x) < ln (push all f p (f x))) by (apply ln_increasing; lra).
    unfold log2.
    replace (ln (push all f p (f x)) / ln 2 - ln (p x) / ln 2)
      with ((ln (push all f p (f x)) - ln (p x)) * / ln 2)
      by (field; apply Rgt_not_eq, ln2_pos).
    apply Rmult_lt_0_compat; [exact Hp |].
    apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat, ln2_pos].
Qed.

(** A state known in advance: all probability on one state. *)
Definition point_mass (s0 : A) (a : A) : R := if eq_dec s0 a then 1 else 0.

(** A step from a known state removes no entropy, whatever it merges. *)
Theorem known_state_step_removes_no_entropy :
  forall (all : list A) (f : A -> A) (s0 : A),
    NoDup all -> (forall a, In a all) ->
    entropy all (point_mass s0) - entropy all (push all f (point_mass s0)) = 0.
Proof.
  intros all f s0 Hnd Hall.
  assert (Hnn : forall a, 0 <= point_mass s0 a)
    by (intro a; unfold point_mass; destruct (eq_dec s0 a); lra).
  rewrite entropy_drop_as_point_sum by assumption.
  apply rsum_zero. intros x _.
  unfold point_mass at 1 2 3.
  destruct (eq_dec s0 x) as [Hsx | Hne].
  - subst x. destruct (Rlt_dec 0 1) as [_ | Hc]; [| lra].
    assert (Hq : push all f (point_mass s0) (f s0) = 1).
    { unfold push.
      rewrite (rsum_ext_in all
                 (fun z => if eq_dec (f z) (f s0) then point_mass s0 z else 0)
                 (fun z => if eq_dec s0 z then (fun _ => 1) z else 0)).
      - exact (rsum_select all s0 (fun _ => 1) Hnd (Hall s0)).
      - intros z _. unfold point_mass. destruct (eq_dec s0 z) as [Hz | Hz].
        + subst z. destruct (eq_dec (f s0) (f s0)); [reflexivity | contradiction].
        + destruct (eq_dec (f z) (f s0)); reflexivity. }
    rewrite Hq. unfold log2, point_mass.
    destruct (eq_dec s0 s0) as [_ | Hc]; [| exfalso; apply Hc; reflexivity].
    rewrite ln_1. unfold Rdiv. ring.
  - destruct (Rlt_dec 0 0); [lra | reflexivity].
Qed.

Lemma not_nodup_map_witness :
  forall (f : A -> A) (l : list A),
    NoDup l -> ~ NoDup (map f l) ->
    exists x x', In x l /\ In x' l /\ x <> x' /\ f x = f x'.
Proof.
  intros f l Hnd Hmap. induction l as [| a l IH].
  - exfalso. apply Hmap. constructor.
  - inversion Hnd as [| a' l' Hnot Hnd']; subst.
    destruct (in_dec eq_dec (f a) (map f l)) as [Hin | Hout].
    + apply in_map_iff in Hin as [x' [Hfx' Hx']].
      exists a, x'. split; [left; reflexivity |]. split; [right; exact Hx' |].
      split; [intro Heq; subst x'; contradiction | symmetry; exact Hfx'].
    + assert (Hl : ~ NoDup (map f l)).
      { intro Hl. apply Hmap. simpl. constructor; assumption. }
      destruct (IH Hnd' Hl) as [x [x' [Hx [Hx' [Hne Hff]]]]].
      exists x, x'. repeat split; try (right; assumption); assumption.
Qed.

Lemma map_nodup_injective_on :
  forall (f : A -> A) (l : list A) a b,
    NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  intros f l. induction l as [| x xs IH]; intros a b Hnd Ha Hb E; [destruct Ha |].
  simpl in Hnd. inversion Hnd as [| ? ? Hx Hxs]; subst.
  destruct Ha as [<- | Ha]; destruct Hb as [<- | Hb].
  - reflexivity.
  - exfalso. apply Hx. rewrite E. apply in_map. exact Hb.
  - exfalso. apply Hx. rewrite <- E. apply in_map. exact Ha.
  - apply IH; assumption.
Qed.

(** The worst case of a merge. Put half the chance on each of two states
    that a move sends to one place, and the move removes at least a full
    bit, however many other states there are. *)
Theorem merge_pair_removes_a_bit :
  forall (all : list A) (f : A -> A) x x',
    NoDup all -> (forall a, In a all) -> x <> x' -> f x = f x' ->
    entropy all (uniform_on [x; x']) - entropy all (push all f (uniform_on [x; x'])) >= 1.
Proof.
  intros all f x x' Hnd Hall Hne Hff.
  assert (HU : NoDup [x; x']).
  { constructor; [intros [H | []]; congruence | constructor; [intros [] | constructor]]. }
  assert (Hsub : forall a, In a [x; x'] -> In a all) by (intros; apply Hall).
  assert (Hlen : (0 < length [x; x'])%nat) by (simpl; lia).
  assert (Hdist : distribution all (uniform_on [x; x']))
    by (apply uniform_on_distribution; assumption).
  rewrite (uniform_on_entropy all [x; x'] Hnd HU Hsub Hlen).
  assert (Hq : entropy all (push all f (uniform_on [x; x'])) <= log2 (INR (length [f x]))).
  { apply entropy_le_log_support; [exact Hnd | apply push_distribution; assumption | | simpl; lia].
    intros y Hy Hpos.
    apply (push_support all [f x] [x; x'] f (uniform_on [x; x']) (proj1 Hdist)) with (y := y);
      [| | exact Hy | exact Hpos].
    - intros z _ Hz. unfold uniform_on, in_b in Hz.
      destruct (in_dec eq_dec z [x; x']); [assumption | lra].
    - intros z [<- | [<- | []]]; [left; reflexivity | left; exact Hff]. }
  simpl length in Hq |- *.
  unfold log2 in *. simpl INR in Hq |- *. rewrite ln_1 in Hq.
  replace (1 + 1) with 2 by ring.
  assert (Hl : ln 2 / ln 2 = 1) by (field; apply Rgt_not_eq, ln2_pos).
  rewrite Hl. unfold Rdiv in Hq. rewrite Rmult_0_l in Hq. lra.
Qed.

End Distributions.

(** * A permanent flip in bits *)

Section PermanentEntropy.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.
Variable eq_dec : forall a b : S, {a = b} + {a <> b}.

(** [F] lists distinct states that instruction [i] switches on. *)
Definition flip_list (i : I) (F : list S) : Prop :=
  NoDup F /\ forall t, In t F -> cert t = false /\ cert (step t i) = true.

Lemma certified_and_flips_nodup :
  forall all i F,
    finite_states all -> flip_list i F ->
    NoDup (certified_states S cert all ++ F).
Proof.
  intros all i F Hfin [HndF HF].
  apply nodup_app_disjoint; [apply certified_states_nodup; exact Hfin | exact HndF |].
  intros a Ha HaF.
  apply (certified_states_spec S cert all Hfin) in Ha.
  destruct (HF a HaF) as [Hoff _]. congruence.
Qed.

Lemma certified_and_flips_land_certified :
  forall all i F,
    finite_states all -> permanent step cert -> flip_list i F ->
    forall x, In x (certified_states S cert all ++ F) ->
              In (step x i) (certified_states S cert all).
Proof.
  intros all i F Hfin Hperm [_ HF] x Hx.
  apply (certified_states_spec S cert all Hfin).
  apply in_app_or in Hx as [HxC | HxF].
  - apply (certified_states_spec S cert all Hfin) in HxC.
    exact (Hperm x i HxC).
  - exact (proj2 (HF x HxF)).
Qed.

(** After a permanent step, a distribution that lives on the certified
    states and the flipping ones has at most [log2 m] bits left. *)
Theorem permanent_step_entropy_ceiling :
  forall all i F p,
    finite_states all ->
    permanent step cert ->
    flip_list i F ->
    (0 < length F)%nat ->
    distribution all p ->
    (forall x, In x all -> 0 < p x -> In x (certified_states S cert all ++ F)) ->
    entropy all (push eq_dec all (fun s => step s i) p)
      <= log2 (INR (length (certified_states S cert all))).
Proof.
  intros all i F p Hfin Hperm HFl HFpos Hp Hsupp.
  pose proof Hfin as [Hnd Hall].
  apply entropy_le_log_support.
  - exact Hnd.
  - apply push_distribution; assumption.
  - apply (push_support eq_dec all (certified_states S cert all)
             (certified_states S cert all ++ F)
             (fun s => step s i) p (proj1 Hp) Hsupp).
    apply certified_and_flips_land_certified; assumption.
  - destruct F as [| t F']; [simpl in HFpos; lia |].
    destruct HFl as [_ HF]. destruct (HF t (or_introl eq_refl)) as [_ Hon].
    eapply flip_gives_certified_state; [exact Hfin | exact Hon].
Qed.

(** The entropy drop is at least [H(p) - log2 m]. *)
Theorem permanent_step_entropy_drop :
  forall all i F p,
    finite_states all ->
    permanent step cert ->
    flip_list i F ->
    (0 < length F)%nat ->
    distribution all p ->
    (forall x, In x all -> 0 < p x -> In x (certified_states S cert all ++ F)) ->
    entropy all p - entropy all (push eq_dec all (fun s => step s i) p)
      >= entropy all p - log2 (INR (length (certified_states S cert all))).
Proof.
  intros all i F p Hfin Hperm HFl HFpos Hp Hsupp.
  pose proof (permanent_step_entropy_ceiling all i F p Hfin Hperm HFl HFpos Hp Hsupp).
  lra.
Qed.

(** For the uniform distribution on the [m + k] states in play the drop is
    at least [log2 ((m + k) / m)] bits: the counting bound, in entropy. *)
Theorem permanent_flip_uniform_entropy_drop :
  forall all i F,
    finite_states all ->
    permanent step cert ->
    flip_list i F ->
    (0 < length F)%nat ->
    let C := certified_states S cert all in
    let p := uniform_on eq_dec (C ++ F) in
    entropy all p - entropy all (push eq_dec all (fun s => step s i) p)
      >= log2 (INR (length C + length F) / INR (length C)).
Proof.
  intros all i F Hfin Hperm HFl HFpos C p.
  assert (HndCF : NoDup (C ++ F)) by (eapply certified_and_flips_nodup; eassumption).
  assert (HsubCF : forall a, In a (C ++ F) -> In a all) by (intros; apply (proj2 Hfin)).
  assert (HlenCF : (0 < length (C ++ F))%nat) by (rewrite app_length; lia).
  assert (Hm : (0 < length C)%nat).
  { destruct F as [| t F']; [simpl in HFpos; lia |].
    destruct HFl as [_ HF]. destruct (HF t (or_introl eq_refl)) as [_ Hon].
    eapply flip_gives_certified_state; [exact Hfin | exact Hon]. }
  assert (Hdist : distribution all p)
    by (apply uniform_on_distribution; [apply (proj1 Hfin) | exact HndCF | exact HsubCF | exact HlenCF]).
  assert (Hsupp : forall x, In x all -> 0 < p x -> In x (C ++ F)).
  { intros x _ Hpx. unfold p, uniform_on, in_b in Hpx.
    destruct (in_dec eq_dec x (C ++ F)); [assumption | lra]. }
  pose proof (permanent_step_entropy_drop all i F p Hfin Hperm HFl HFpos Hdist Hsupp) as Hd.
  fold C in Hd.
  unfold p in Hd |- *.
  rewrite (uniform_on_entropy eq_dec all (C ++ F) (proj1 Hfin) HndCF HsubCF HlenCF) in Hd |- *.
  rewrite app_length in Hd |- *.
  assert (HmR : 0 < INR (length C)) by (apply lt_0_INR; exact Hm).
  assert (HmkR : 0 < INR (length C + length F)) by (apply lt_0_INR; lia).
  assert (Hq : ln (INR (length C + length F) / INR (length C))
               = ln (INR (length C + length F)) - ln (INR (length C))).
  { unfold Rdiv. rewrite ln_mult, ln_Rinv;
      [lra | exact HmR | exact HmkR | apply Rinv_0_lt_compat; exact HmR]. }
  unfold log2 in *. rewrite Hq.
  assert (Hl2 := ln2_pos).
  replace ((ln (INR (length C + length F)) - ln (INR (length C))) / ln 2)
    with (ln (INR (length C + length F)) / ln 2 - ln (INR (length C)) / ln 2)
    by (field; lra).
  exact Hd.
Qed.

(** A step that lowers entropy is priced, in whole units, by the bits it
    removes from some distribution on the states in play. *)
Definition entropy_priced (all : list S) (cost : I -> nat) : Prop :=
  forall i p,
    distribution all p ->
    INR (cost i) >= entropy all p - entropy all (push eq_dec all (fun s => step s i) p).

(** A2 follows from entropy pricing and permanence: one flip removes a
    positive number of bits from the uniform distribution on the states in
    play, and a whole-unit price above a positive number is at least one. *)
Theorem a2_from_entropy_price_and_permanence :
  forall all cost,
    finite_states all ->
    permanent step cert ->
    entropy_priced all cost ->
    a2_holds step cert cost.
Proof.
  intros all cost Hfin Hperm Hprice s i Hoff Hon.
  assert (HFl : flip_list i [s]).
  { split; [repeat constructor; intros [] | intros t [<- | []]; split; assumption]. }
  assert (HFpos : (0 < length [s])%nat) by (simpl; lia).
  pose proof (permanent_flip_uniform_entropy_drop all i [s] Hfin Hperm HFl HFpos) as Hd.
  simpl in Hd.
  set (C := certified_states S cert all) in *.
  assert (Hm : (0 < length C)%nat) by (eapply flip_gives_certified_state; eassumption).
  assert (HmR : 0 < INR (length C)) by (apply lt_0_INR; exact Hm).
  assert (Hdist : distribution all (uniform_on eq_dec (C ++ [s]))).
  { apply uniform_on_distribution.
    - apply (proj1 Hfin).
    - eapply certified_and_flips_nodup; eassumption.
    - intros; apply (proj2 Hfin).
    - rewrite app_length; simpl; lia. }
  pose proof (Hprice i _ Hdist) as Hc.
  assert (Hpos : 0 < log2 (INR (length C + 1) / INR (length C))).
  { unfold log2. apply Rdiv_lt_0_compat; [| exact ln2_pos].
    rewrite <- ln_1. apply ln_increasing; [lra |].
    rewrite plus_INR. simpl INR.
    apply Rmult_lt_reg_r with (r := INR (length C)); [exact HmR |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (HcR : 0 < INR (cost i)) by lra.
  destruct (cost i) as [| n]; [simpl in HcR; lra | unfold ge; apply le_n_S, Nat.le_0_l].
Qed.

(** The physical premise, named and not proved: Landauer's principle. A
    step that lowers the entropy of the machine's state by [dH] bits
    dissipates at least [kT ln 2 * dH]. *)
Definition landauer_heat (kT heat dH : R) : Prop :=
  heat >= kT * ln 2 * dH.

(** Under Landauer's principle, switching [k] states on beside [m]
    certified ones, when the state is uniform on those [m + k], dissipates
    at least [kT ln ((m + k) / m)]. *)
Theorem permanent_flip_heat_floor :
  forall all i F kT heat,
    finite_states all ->
    permanent step cert ->
    flip_list i F ->
    (0 < length F)%nat ->
    0 <= kT ->
    let C := certified_states S cert all in
    let p := uniform_on eq_dec (C ++ F) in
    landauer_heat kT heat
      (entropy all p - entropy all (push eq_dec all (fun s => step s i) p)) ->
    heat >= kT * ln (INR (length C + length F) / INR (length C)).
Proof.
  intros all i F kT heat Hfin Hperm HFl HFpos HkT C p Hheat.
  pose proof (permanent_flip_uniform_entropy_drop all i F Hfin Hperm HFl HFpos) as Hd.
  cbv zeta in Hd. fold C in Hd. fold p in Hd. unfold landauer_heat in Hheat.
  assert (Hl2 := ln2_pos).
  assert (Hkl : 0 <= kT * ln 2) by nra.
  assert (Hmono : kT * ln 2 * log2 (INR (length C + length F) / INR (length C))
                  <= kT * ln 2 * (entropy all p - entropy all (push eq_dec all (fun s => step s i) p)))
    by (apply Rmult_le_compat_l; [exact Hkl | lra]).
  replace (kT * ln 2 * log2 (INR (length C + length F) / INR (length C)))
    with (kT * ln (INR (length C + length F) / INR (length C))) in Hmono
    by (unfold log2; field; lra).
  lra.
Qed.

(** And that heat is strictly positive whenever at least one state flips
    and the temperature is positive. *)
Theorem permanent_flip_heat_positive :
  forall all i F kT heat,
    finite_states all ->
    permanent step cert ->
    flip_list i F ->
    (0 < length F)%nat ->
    0 < kT ->
    let C := certified_states S cert all in
    let p := uniform_on eq_dec (C ++ F) in
    landauer_heat kT heat
      (entropy all p - entropy all (push eq_dec all (fun s => step s i) p)) ->
    heat > 0.
Proof.
  intros all i F kT heat Hfin Hperm HFl HFpos HkT C p Hheat.
  pose proof (permanent_flip_heat_floor all i F kT heat Hfin Hperm HFl HFpos
                (Rlt_le _ _ HkT) Hheat) as Hh.
  fold C in Hh.
  assert (Hm : (0 < length C)%nat).
  { destruct F as [| t F']; [simpl in HFpos; lia |].
    destruct HFl as [_ HF]. destruct (HF t (or_introl eq_refl)) as [_ Hon].
    eapply flip_gives_certified_state; [exact Hfin | exact Hon]. }
  assert (HmR : 0 < INR (length C)) by (apply lt_0_INR; exact Hm).
  assert (HkR : 0 < INR (length F)) by (apply lt_0_INR; exact HFpos).
  assert (Hln : 0 < ln (INR (length C + length F) / INR (length C))).
  { rewrite <- ln_1. apply ln_increasing; [lra |].
    rewrite plus_INR.
    apply Rmult_lt_reg_r with (r := INR (length C)); [exact HmR |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  nra.
Qed.

(** For any distribution that gives every state in play positive
    probability, not only the uniform one, a permanent flip removes entropy:
    the step squeezes the certified states and the flipping one into the
    certified states, so two states of positive probability land together. *)
Theorem permanent_flip_full_support_entropy_drop_positive :
  forall all i s p,
    finite_states all ->
    permanent step cert ->
    cert s = false -> cert (step s i) = true ->
    distribution all p ->
    (forall x, In x (certified_states S cert all ++ [s]) -> 0 < p x) ->
    entropy all p - entropy all (push eq_dec all (fun t => step t i) p) > 0.
Proof.
  intros all i s p Hfin Hperm Hoff Hon [Hnn Hsum] Hsupp.
  set (C := certified_states S cert all).
  assert (HFl : flip_list i [s]).
  { split; [repeat constructor; intros [] | intros t [<- | []]; split; assumption]. }
  assert (Hnd : NoDup (C ++ [s])) by (eapply certified_and_flips_nodup; eassumption).
  assert (Hland : forall x, In x (C ++ [s]) -> In (step x i) C)
    by (apply certified_and_flips_land_certified; assumption).
  assert (Hmerge : ~ NoDup (map (fun t => step t i) (C ++ [s]))).
  { intro Hmap.
    assert (Hle : (length (map (fun t => step t i) (C ++ [s])) <= length C)%nat).
    { apply NoDup_incl_length; [exact Hmap |].
      intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. apply Hland. exact Hx. }
    rewrite map_length, app_length in Hle. simpl in Hle. lia. }
  destruct (not_nodup_map_witness eq_dec (fun t => step t i) (C ++ [s]) Hnd Hmerge)
    as [x [x' [Hx [Hx' [Hne Hff]]]]].
  apply (entropy_drop_pos_of_support_merge eq_dec all (fun t => step t i) p x x');
    try assumption.
  - apply (proj1 Hfin).
  - apply (proj2 Hfin).
  - apply Hsupp. exact Hx.
  - apply Hsupp. exact Hx'.
Qed.

(** Under Landauer's principle, that flip dissipates positive heat. *)
Theorem permanent_flip_full_support_heat_positive :
  forall all i s p kT heat,
    finite_states all ->
    permanent step cert ->
    cert s = false -> cert (step s i) = true ->
    distribution all p ->
    (forall x, In x (certified_states S cert all ++ [s]) -> 0 < p x) ->
    0 < kT ->
    landauer_heat kT heat
      (entropy all p - entropy all (push eq_dec all (fun t => step t i) p)) ->
    heat > 0.
Proof.
  intros all i s p kT heat Hfin Hperm Hoff Hon Hp Hsupp HkT Hheat.
  pose proof (permanent_flip_full_support_entropy_drop_positive
                all i s p Hfin Hperm Hoff Hon Hp Hsupp) as Hd.
  unfold landauer_heat in Hheat.
  assert (Hprod : 0 < kT * ln 2 *
            (entropy all p - entropy all (push eq_dec all (fun t => step t i) p))).
  { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [exact HkT | exact ln2_pos] | lra]. }
  lra.
Qed.

(** The boundary. If the state is known before the step, the step removes
    no entropy, so Landauer's principle forces no heat at all: the premise
    reduces to heat >= 0. The heat a permanent flip must dissipate comes
    from uncertainty about which state the machine is in. *)
Theorem known_state_flip_forces_no_heat :
  forall all i s kT heat,
    finite_states all ->
    landauer_heat kT heat
      (entropy all (point_mass eq_dec s)
       - entropy all (push eq_dec all (fun t => step t i) (point_mass eq_dec s)))
    <-> heat >= 0.
Proof.
  intros all i s kT heat [Hnd Hall]. unfold landauer_heat.
  rewrite (known_state_step_removes_no_entropy eq_dec all (fun t => step t i) s Hnd Hall).
  rewrite Rmult_0_r. tauto.
Qed.

(** Read in the worst case over what the machine might be holding, a
    permanent flip removes a full bit, whatever the number of yes-states:
    it merges two states (a permanent flip merges), and the spread with half
    its chance on each loses at least one bit. *)
Theorem permanent_flip_spread_loses_a_bit :
  forall all s i,
    finite_states all -> permanent step cert ->
    cert s = false -> cert (step s i) = true ->
    exists x x', x <> x' /\ step x i = step x' i /\
      entropy all (uniform_on eq_dec [x; x'])
      - entropy all (push eq_dec all (fun t => step t i) (uniform_on eq_dec [x; x'])) >= 1.
Proof.
  intros all s i Hfin Hperm Hs Hflip.
  assert (Hni : ~ step_injective step i) by (eapply permanent_flip_is_not_injective; eauto).
  destruct Hfin as [Hnd Hall].
  assert (Hmap : ~ NoDup (map (fun t => step t i) all)).
  { intro Hn. apply Hni. intros a b Hab.
    exact (map_nodup_injective_on (fun t => step t i) all a b Hn (Hall a) (Hall b) Hab). }
  destruct (not_nodup_map_witness eq_dec (fun t => step t i) all Hnd Hmap)
    as [x [x' [_ [_ [Hne Hff]]]]].
  exists x, x'. split; [exact Hne | split; [exact Hff |]].
  apply merge_pair_removes_a_bit; assumption.
Qed.

End PermanentEntropy.

Arguments flip_list {S I}.
Arguments entropy_priced {S I}.

(** The entropy-priced machine is a certification system, so the universal
    trace floor applies to it. *)
Definition certification_system_from_entropy_price
    (S I : Type) (step : S -> I -> S) (cert : S -> bool) (cost : I -> nat)
    (eq_dec : forall a b : S, {a = b} + {a <> b})
    (all : list S)
    (Hfin : finite_states all)
    (Hperm : permanent step cert)
    (Hprice : entropy_priced step eq_dec all cost) : CertificationSystem :=
  {| cs_state := S;
     cs_instr := I;
     cs_step := step;
     cs_cost := cost;
     cs_cert := cert;
     cs_cert_costs :=
       a2_from_entropy_price_and_permanence S I step cert eq_dec all cost
         Hfin Hperm Hprice |}.

Theorem entropy_priced_trace_floor :
  forall (S I : Type) (step : S -> I -> S) (cert : S -> bool) (cost : I -> nat)
         (eq_dec : forall a b : S, {a = b} + {a <> b})
         (all : list S)
         (Hfin : finite_states all)
         (Hperm : permanent step cert)
         (Hprice : entropy_priced step eq_dec all cost)
         (trace : list I) (s0 : S),
    cert s0 = false ->
    cert (cs_run (certification_system_from_entropy_price
                    S I step cert cost eq_dec all Hfin Hperm Hprice) trace s0) = true ->
    (cs_total_cost (certification_system_from_entropy_price
                      S I step cert cost eq_dec all Hfin Hperm Hprice) trace >= 1)%nat.
Proof.
  intros S I step cert cost eq_dec all Hfin Hperm Hprice trace s0 H0 H1.
  exact (universal_nfi_any_substrate
           (certification_system_from_entropy_price
              S I step cert cost eq_dec all Hfin Hperm Hprice) trace s0 H0 H1).
Qed.

Print Assumptions merge_pair_removes_a_bit.
Print Assumptions permanent_flip_spread_loses_a_bit.
