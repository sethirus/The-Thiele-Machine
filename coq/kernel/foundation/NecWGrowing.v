(** NecWGrowing: growing records and probabilistic records, pushed to
    their limits.

    - A driven, growing record is a family of threshold latches; the price
      and the reachable write are not needed for that. Growing is
      necessary: every threshold factorization grows. Being driven is
      necessary: the clock, read as a two-valued growing record, has no
      threshold factorization. A threshold factorization makes the next
      value depend only on the base state and the current value.
    - Three values are the fewest that need more than one latch: every
      honest two-valued growing record is carried by one latch.
    - The chain bound is attained: for every k there is a chain of k + 1
      distinct k-bit words.
    - Pricing changes and pricing thresholds agree only on growing records:
      a record that drops, uncharged, meets the threshold price and not the
      change price.
    - A deterministic latch describes an honest probabilistic record
      exactly when the record does not branch from off. The schedule does
      not fix the probabilities even in the normalized sense (one half
      against two thirds), and it does fix them when nothing branches. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase.
From Kernel Require Import StructuralRecordAxis GrowingRecordCore GrowingRecord.
From Kernel Require Import ProbabilisticRecordCore ProbabilisticRecord.

(* ================================================================= *)
(** * 1. Threshold latches                                            *)
(* ================================================================= *)

Theorem nec_w_growing_from_driven_grows :
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B)
         (A : Type) (P : BoolPartialOrder A) (rec : rc_state M -> A),
    record_driven M B C rec -> record_grows M P rec ->
    exists h, threshold_latch_factorization M B C P rec h.
Proof.
  intros M B C A P rec [f Hf] Hgrows.
  exists (fun a b x => andb (negb (gr_leq P a x)) (gr_leq P a (f b x))).
  intros m a. rewrite Hf.
  specialize (Hgrows m).
  destruct (gr_leq P a (rec m)) eqn:Hbefore;
    destruct (gr_leq P a (f (base_state M B C m) (rec m))) eqn:Hafter;
    simpl; try reflexivity.
  exfalso. rewrite Hf in Hgrows.
  pose proof (@gr_leq_trans A P a (rec m)
    (f (base_state M B C m) (rec m)) Hbefore Hgrows).
  congruence.
Qed.

Theorem nec_w_threshold_factor_implies_grows :
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B)
         (A : Type) (P : BoolPartialOrder A) (rec : rc_state M -> A) h,
    threshold_latch_factorization M B C P rec h -> record_grows M P rec.
Proof.
  intros M B C A P rec h H m.
  rewrite (H m (rec m)), (@gr_leq_refl A P). reflexivity.
Qed.

(** The relational form of being driven follows from a threshold
    factorization: two states with the same base state and the same value
    step to the same value. *)
Theorem nec_w_threshold_factor_relationally_driven :
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B)
         (A : Type) (P : BoolPartialOrder A) (rec : rc_state M -> A) h,
    threshold_latch_factorization M B C P rec h ->
    forall m1 m2, base_state M B C m1 = base_state M B C m2 -> rec m1 = rec m2 ->
      rec (rc_next M m1) = rec (rc_next M m2).
Proof.
  intros M B C A P rec h H m1 m2 Eb Er.
  apply (thresholds_determine_record_holds A P). intro a.
  rewrite (H m1 a), (H m2 a), Eb, Er. reflexivity.
Qed.

(** The Boolean order: false below true. *)
Definition nec_w_bool_order : BoolPartialOrder bool.
Proof.
  refine {| gr_leq := implb |}.
  - intros []; reflexivity.
  - intros [] []; simpl; intros; try discriminate; reflexivity.
  - intros [] [] []; simpl; intros; try discriminate; reflexivity.
Defined.

Definition nec_w_clock_rec (x : rc_state ClockCore) : bool := rc_cert ClockCore x.

(** Being driven is necessary: the clock's record grows, every change is
    priced, it is written, and no threshold factorization exists. *)
Theorem nec_w_clock_no_threshold_factorization :
  record_grows ClockCore nec_w_bool_order nec_w_clock_rec /\
  record_schedule_priced ClockCore nec_w_clock_rec /\
  reachable_strict_record_write ClockCore nec_w_clock_rec /\
  ~ exists h, threshold_latch_factorization ClockCore counter_base clock_cover
                nec_w_bool_order nec_w_clock_rec h.
Proof.
  split; [| split; [| split]].
  - intros [[b k] r]. destruct r; reflexivity.
  - split; [intros [[b k] r]; cbn; lia |].
    intros [[b k] r] _. unfold step_cost. cbn -[Nat.sub]. lia.
  - exists (0, 0, false), 5. split; [exact I | discriminate].
  - intros [h H]. apply clock_record_not_driven.
    exists (fun b r => orb r (h true b r)). intro m.
    pose proof (H m true) as Hm. exact Hm.
Qed.

(** Three values are the fewest that need more than one latch: every
    honest two-valued growing record is carried by one latch. *)
Theorem nec_w_two_valued_one_latch :
  forall (M : RCM) (B : BaseMachine) (C : BaseCover M B) (rec : rc_state M -> bool),
    HonestGrowingExtension M B C nec_w_bool_order rec ->
    single_latch_carries M B C rec.
Proof.
  intros M B C rec [[f Hf] [Hgrows _]].
  exists (fun b => f b false), rec, (fun _ l => l). split; [| reflexivity].
  intro m. specialize (Hgrows m). simpl in Hgrows.
  destruct (rec m) eqn:E.
  - simpl in Hgrows. exact Hgrows.
  - simpl. rewrite Hf, E. reflexivity.
Qed.

(** Pricing changes and pricing thresholds agree only on growing records. *)
Definition nec_w_drop : RCM := {|
  rc_state := bool;
  rc_next := fun _ => false;
  rc_init := fun _ => True;
  rc_cert := fun b => b;
  rc_mu := fun _ => 0;
  rc_halted := fun _ => False
|}.

Theorem nec_w_price_iff_needs_grows :
  threshold_schedule_priced nec_w_drop nec_w_bool_order (fun b => b) /\
  ~ record_schedule_priced nec_w_drop (fun b => b) /\
  ~ record_grows nec_w_drop nec_w_bool_order (fun b => b).
Proof.
  split; [| split].
  - split; [intros s; cbn; lia |].
    intros m a H0 H1. destruct a, m; cbn in H0, H1; discriminate.
  - intros [_ H]. specialize (H true ltac:(discriminate)). unfold step_cost in H. cbn in H. lia.
  - intros H. specialize (H true). discriminate.
Qed.

(* ================================================================= *)
(** * 2. The chain bound is attained                                  *)
(* ================================================================= *)

Definition nec_w_word (k j : nat) : list bool := repeat true j ++ repeat false (k - j).

Fixpoint nec_w_up (k j d : nat) : list (list bool) :=
  match d with
  | 0 => [nec_w_word k j]
  | S d' => nec_w_word k j :: nec_w_up k (S j) d'
  end.

Lemma nec_w_word_nth : forall j m n,
  nth n (repeat true j ++ repeat false m) false = Nat.ltb n j.
Proof.
  induction j as [| j IH]; intros m n.
  - simpl. rewrite nth_repeat. destruct n; reflexivity.
  - destruct n as [| n]; [reflexivity |]. simpl. rewrite IH. reflexivity.
Qed.

Lemma nec_w_word_length : forall k j, j <= k -> length (nec_w_word k j) = k.
Proof.
  intros k j H. unfold nec_w_word. rewrite app_length, !repeat_length. lia.
Qed.

Lemma nec_w_up_head : forall k j d, exists rest, nec_w_up k j d = nec_w_word k j :: rest.
Proof. intros k j [| d]; eexists; reflexivity. Qed.

Lemma nec_w_up_in : forall k d j u,
  In u (nec_w_up k j d) -> exists j', j <= j' <= j + d /\ u = nec_w_word k j'.
Proof.
  intros k d. induction d as [| d IH]; intros j u H; simpl in H.
  - destruct H as [<- | []]. exists j. split; [lia | reflexivity].
  - destruct H as [<- | H]; [exists j; split; [lia | reflexivity] |].
    destruct (IH (S j) u H) as [j' [Hj' ->]]. exists j'. split; [lia | reflexivity].
Qed.

Lemma nec_w_up_length : forall k d j, length (nec_w_up k j d) = S d.
Proof. intros k d. induction d as [| d IH]; intros j; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma nec_w_word_inj : forall k j j', j < j' -> j' <= k -> nec_w_word k j <> nec_w_word k j'.
Proof.
  intros k j j' Hlt Hle E.
  assert (H : nth j (nec_w_word k j) false = nth j (nec_w_word k j') false) by (rewrite E; reflexivity).
  unfold nec_w_word in H. rewrite !nec_w_word_nth in H.
  rewrite (proj2 (Nat.ltb_ge j j)) in H by lia.
  rewrite (proj2 (Nat.ltb_lt j j')) in H by lia. discriminate.
Qed.

Theorem nec_w_chain_attained : forall k,
  exists vs : list (list bool),
    Forall (fun v => length v = k) vs /\ bits_chain vs /\ NoDup vs /\ length vs = S k.
Proof.
  intros k. exists (nec_w_up k 0 k).
  assert (Hgen : forall d j, j + d <= k ->
    Forall (fun v => length v = k) (nec_w_up k j d) /\
    bits_chain (nec_w_up k j d) /\ NoDup (nec_w_up k j d)).
  { induction d as [| d IH]; intros j Hjd.
    - simpl. split; [constructor; [apply nec_w_word_length; lia | constructor] |].
      split; [exact I | repeat constructor; simpl; tauto].
    - destruct (IH (S j) ltac:(lia)) as [Hl [Hc Hn]].
      split; [| split].
      + constructor; [apply nec_w_word_length; lia | exact Hl].
      + change (bits_chain (nec_w_word k j :: nec_w_up k (S j) d)).
        destruct (nec_w_up_head k (S j) d) as [rest Hrest].
        rewrite Hrest in Hc |- *. split; [| exact Hc].
        split; [rewrite !nec_w_word_length by lia; reflexivity |].
        intros n Hn'. unfold nec_w_word in *. rewrite nec_w_word_nth in Hn' |- *.
        apply Nat.ltb_lt in Hn'. apply Nat.ltb_lt. lia.
      + constructor; [| exact Hn].
        intro Hin. destruct (nec_w_up_in k d (S j) _ Hin) as [j' [Hj' E]].
        exact (nec_w_word_inj k j j' ltac:(lia) ltac:(lia) E). }
  destruct (Hgen k 0 ltac:(lia)) as [Hl [Hc Hn]].
  split; [exact Hl | split; [exact Hc | split; [exact Hn | apply nec_w_up_length]]].
Qed.

(** With the repository's bound: the largest chain has exactly k + 1
    members. *)
Corollary nec_w_chain_bound_tight : forall k,
  (forall vs, Forall (fun v => length v = k) vs -> bits_chain vs -> NoDup vs ->
     length vs <= S k) /\
  exists vs, Forall (fun v => length v = k) vs /\ bits_chain vs /\ NoDup vs /\ length vs = S k.
Proof.
  intros k. split; [intros vs; apply chain_needs_bits_holds | apply nec_w_chain_attained].
Qed.

(* ================================================================= *)
(** * 3. Probabilistic records                                        *)
(* ================================================================= *)

(** A deterministic latch describes an honest probabilistic record exactly
    when the record does not branch from off. *)
Theorem nec_w_det_latch_iff_no_branching :
  forall (k : weighted_kernel) (c : branch_charge),
    honest_probabilistic_record k c ->
    (exists h : bool -> bool, forall b w b', In (w, b') (k b) -> b' = orb b (h b)) <->
    (forall w1 b1 w2 b2, In (w1, b1) (k false) -> In (w2, b2) (k false) -> b1 = b2).
Proof.
  intros k c [_ [Htot [Hmono _]]]. split.
  - intros [h Hh] w1 b1 w2 b2 H1 H2.
    rewrite (Hh false w1 b1 H1), (Hh false w2 b2 H2). reflexivity.
  - intros Hnb. destruct (k false) as [| [w0 b0] rest] eqn:E.
    + exfalso. exact (Htot false E).
    + exists (fun _ => b0). intros [] w b' Hin.
      * rewrite (Hmono w b' Hin). reflexivity.
      * simpl. rewrite <- E in Hnb. apply (Hnb w b' w0 b0 Hin). rewrite E. left. reflexivity.
Qed.

Fixpoint nec_w_weight (l : list (nat * bool)) (o : bool) : nat :=
  match l with
  | [] => 0
  | (w, b) :: rest => (if Bool.eqb b o then w else 0) + nec_w_weight rest o
  end.

Fixpoint nec_w_total (l : list (nat * bool)) : nat :=
  match l with
  | [] => 0
  | (w, _) :: rest => w + nec_w_total rest
  end.

(** Same in probability: the normalized weights agree, cross-multiplied so
    that no division is needed. *)
Definition nec_w_same_probability (k1 k2 : weighted_kernel) : Prop :=
  forall b o, nec_w_weight (k1 b) o * nec_w_total (k2 b) =
              nec_w_weight (k2 b) o * nec_w_total (k1 b).

(** The schedule does not fix the probabilities even after normalizing:
    from off, the fair record writes with probability one half and the
    biased one with two thirds. *)
Theorem nec_w_schedule_not_normalized_probability :
  honest_probabilistic_record fair_branch_kernel branch_write_charge /\
  honest_probabilistic_record biased_branch_kernel branch_write_charge /\
  same_probabilistic_schedule fair_branch_kernel biased_branch_kernel
    branch_write_charge branch_write_charge /\
  ~ nec_w_same_probability fair_branch_kernel biased_branch_kernel.
Proof.
  split; [exact fair_branch_honest |].
  split; [exact biased_branch_honest |].
  split; [split; [exact branch_kernels_same_support | reflexivity] |].
  intros H. specialize (H false true). simpl in H. discriminate.
Qed.

(** A kernel that does not branch: from each state every branch has one
    outcome. *)
Definition nec_w_no_branching (k : weighted_kernel) : Prop :=
  forall b w1 b1 w2 b2, In (w1, b1) (k b) -> In (w2, b2) (k b) -> b1 = b2.

Lemma nec_w_weight_single : forall l o0,
  (forall w b, In (w, b) l -> b = o0) ->
  forall o, nec_w_weight l o = if Bool.eqb o0 o then nec_w_total l else 0.
Proof.
  induction l as [| [w b] l IH]; intros o0 Hl o; simpl.
  - destruct (Bool.eqb o0 o); reflexivity.
  - rewrite (Hl w b (or_introl eq_refl)).
    rewrite (IH o0 (fun w' b' H => Hl w' b' (or_intror H)) o).
    destruct (Bool.eqb o0 o); lia.
Qed.

(** Without branching the schedule does fix the probabilities: branching
    is what the counterexample needs. *)
Theorem nec_w_no_branching_schedule_fixes_probability :
  forall k1 k2 c1 c2,
    total_kernel k1 -> total_kernel k2 ->
    nec_w_no_branching k1 -> nec_w_no_branching k2 ->
    same_probabilistic_schedule k1 k2 c1 c2 ->
    nec_w_same_probability k1 k2.
Proof.
  intros k1 k2 c1 c2 Ht1 Ht2 Hn1 Hn2 [Hsupp _] b o.
  destruct (k1 b) as [| [w1 o1] r1] eqn:E1; [exfalso; exact (Ht1 b E1) |].
  assert (Hall1 : forall w b', In (w, b') (k1 b) -> b' = o1).
  { intros w b' H. apply (Hn1 b w b' w1 o1 H). rewrite E1. left. reflexivity. }
  assert (Hin2 : kernel_support k2 b o1).
  { apply Hsupp. exists w1. rewrite E1. left. reflexivity. }
  destruct Hin2 as [w2 Hw2].
  assert (Hall2 : forall w b', In (w, b') (k2 b) -> b' = o1).
  { intros w b' H. exact (Hn2 b w b' w2 o1 H Hw2). }
  rewrite <- E1.
  rewrite (nec_w_weight_single (k1 b) o1 Hall1 o), (nec_w_weight_single (k2 b) o1 Hall2 o).
  destruct (Bool.eqb o1 o); lia.
Qed.

Print Assumptions nec_w_growing_from_driven_grows.
Print Assumptions nec_w_threshold_factor_implies_grows.
Print Assumptions nec_w_threshold_factor_relationally_driven.
Print Assumptions nec_w_clock_no_threshold_factorization.
Print Assumptions nec_w_two_valued_one_latch.
Print Assumptions nec_w_price_iff_needs_grows.
Print Assumptions nec_w_chain_attained.
Print Assumptions nec_w_chain_bound_tight.
Print Assumptions nec_w_det_latch_iff_no_branching.
Print Assumptions nec_w_schedule_not_normalized_probability.
Print Assumptions nec_w_no_branching_schedule_fixes_probability.
