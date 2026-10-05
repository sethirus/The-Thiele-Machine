(** EntitlementMore2.v: the observation-partition reduction, the weighted
    bound, and the observational variant.

    EntitlementSmall.v states structural entitlement for any Thiele-complete
    machine, with a covering by fibres (ent_reduction) as the hypothesis that
    ties the size of a narrowing to a decision tree. Three more statements
    sit around it:

      1. The observation-partition reduction. The covering hypothesis can be
         derived from a plainer one: every rival looks like some survivor
         under the representative observation, and no observation class
         (taken inside the prior) is bigger than the tree has leaves. The
         clause "fibres add up to the prior" is not an extra hypothesis;
         it follows [ent2_cover_sum, ent2_partition_old_iff].
         A partition is a stronger hypothesis than a covering
         [ent2_partition_to_reduction, ent2_reduction_not_partition].
      2. The weighted bound. Rivals carry natural-number weights (a prior
         with multiplicities). The tree bound holds for weighted masses, with
         a weighted covering [ent2_weighted_bits] and a weighted fibre form
         [ent2_wreduction_covers]. On a Thiele-complete machine the ledger's
         rise is the same number for every start state, so the expectation
         over a weighted prior is the mass times the record moves, and the
         bound needs no averaging argument [ent2_weighted_representation,
         ent2_weighted_expected_bound].
      3. The observational variant. Drop the record clause: no clean start,
         no raised record. The price bound still holds, and it needs less
         than a Thiele-complete machine: only the exact toll
         [ent2_observed_representation]. What the record adds is exactly the
         earned chain and the floor of 3 [ent2_record_adds]; a clean run
         raises the record iff it contains the earned chain
         [ent2_upgrade_iff]. The small machine runs a member whose record
         stays down and whose bound is met [ent2_observed_small_instance].

    Dependencies: Coq standard library, ThieleComplete.v and
    EntitlementSmall.v. No axioms, no Admitted.                          *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.EntitlementSmall.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 0. Sums over lists.                                                *)
(* ================================================================= *)

Lemma ent2_sum_split : forall {A : Type} (f g : A -> nat) (l : list A),
  fold_right Nat.add 0 (map (fun x => f x + g x) l) =
  fold_right Nat.add 0 (map f l) + fold_right Nat.add 0 (map g l).
Proof. intros A f g l. induction l as [| x l IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma ent2_sum_pos : forall {A : Type} (f : A -> nat) (l : list A),
  (exists x, In x l /\ 1 <= f x) -> 1 <= fold_right Nat.add 0 (map f l).
Proof.
  intros A f l [x [Hx H1]]. induction l as [| y l IH]; simpl; [destruct Hx |].
  destruct Hx as [<- | Hx]; [lia |]. specialize (IH Hx). lia.
Qed.

Lemma ent2_sum_le_mul : forall {A : Type} (f : A -> nat) (c : nat) (l : list A),
  (forall x, In x l -> f x <= c) -> fold_right Nat.add 0 (map f l) <= length l * c.
Proof.
  intros A f c l. induction l as [| x l IH]; intro H; simpl; [lia |].
  assert (Hx : f x <= c) by (apply H; left; reflexivity).
  assert (Hl : fold_right Nat.add 0 (map f l) <= length l * c)
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  lia.
Qed.

(* ================================================================= *)
(* 1. The observation-partition reduction.                            *)
(* ================================================================= *)

(* A union bound: if every member of a list q-matches some member of
   another list, the first list is no longer than the matches summed
   over the second. *)
Lemma ent2_cover_sum_gen : forall {A : Type} (q : A -> A -> bool) (prior post : list A),
  (forall x, In x prior -> exists t, In t post /\ q t x = true) ->
  length prior <= fold_right Nat.add 0 (map (fun t => length (filter (q t) prior)) post).
Proof.
  intros A q prior post. induction prior as [| x prior IH]; intro H; [simpl; lia |].
  assert (Hrest : length prior <=
            fold_right Nat.add 0 (map (fun t => length (filter (q t) prior)) post))
    by (apply IH; intros y Hy; apply H; right; exact Hy).
  assert (Hq : forall t, length (filter (q t) (x :: prior)) =
                         (if q t x then 1 else 0) + length (filter (q t) prior))
    by (intro t; simpl; destruct (q t x); reflexivity).
  assert (Heq : map (fun t => length (filter (q t) (x :: prior))) post =
                map (fun t => (if q t x then 1 else 0) + length (filter (q t) prior)) post)
    by (apply map_ext; exact Hq).
  rewrite Heq, ent2_sum_split. simpl length.
  assert (Hone : 1 <= fold_right Nat.add 0 (map (fun t => if q t x then 1 else 0) post)).
  { apply ent2_sum_pos. destruct (H x (or_introl eq_refl)) as [t [Ht Hqt]].
    exists t. split; [exact Ht |]. rewrite Hqt. lia. }
  lia.
Qed.

Section Partition.

Context {X O : Type}.
Variable eqb : O -> O -> bool.

(* The observation class of the survivor t inside the prior. *)
Definition ent2_obs_fibre (r : X -> O) (prior : list X) (t : X) : list X :=
  filter (fun x => eqb (r x) (r t)) prior.

Definition ent2_fibre_sum (r : X -> O) (prior post : list X) : nat :=
  fold_right Nat.add 0 (map (fun t => length (ent2_obs_fibre r prior t)) post).

(* The partition hypothesis: every rival looks like some survivor under the
   representative observation r, and no class holds more rivals than the
   tree has leaves. *)
Definition ent2_partition (r : X -> O) (T : ent_tree) (prior post : list X) : Prop :=
  (forall x, In x prior -> exists t, In t post /\ r x = r t) /\
  (forall t, In t post -> length (ent2_obs_fibre r prior t) <= ent_leaves T).

(* The partition with a third clause, that the classes add up to at least
   the prior. *)
Definition ent2_partition_old (r : X -> O) (T : ent_tree) (prior post : list X) : Prop :=
  (forall x, In x prior -> exists t, In t post /\ r x = r t) /\
  length prior <= ent2_fibre_sum r prior post /\
  (forall t, In t post -> length (ent2_obs_fibre r prior t) <= ent_leaves T).

Hypothesis eqb_spec : forall o1 o2, eqb o1 o2 = true <-> o1 = o2.

(* The sum clause is not an extra hypothesis: the first clause gives it. *)
Theorem ent2_cover_sum : forall (r : X -> O) (prior post : list X),
  (forall x, In x prior -> exists t, In t post /\ r x = r t) ->
  length prior <= ent2_fibre_sum r prior post.
Proof.
  intros r prior post H. unfold ent2_fibre_sum, ent2_obs_fibre.
  apply (ent2_cover_sum_gen (fun t x => eqb (r x) (r t)) prior post).
  intros x Hx. destruct (H x Hx) as [t [Ht Hr]]. exists t. split; [exact Ht |].
  apply eqb_spec. exact Hr.
Qed.

Theorem ent2_partition_old_iff : forall r T prior post,
  ent2_partition_old r T prior post <-> ent2_partition r T prior post.
Proof.
  intros r T prior post. split.
  - intros [H1 [_ H3]]. exact (conj H1 H3).
  - intros [H1 H3]. exact (conj H1 (conj (ent2_cover_sum r prior post H1) H3)).
Qed.

(* A partition is a covering by fibres: the observation classes are the
   fibres. *)
Theorem ent2_partition_to_reduction : forall r T prior post,
  ent2_partition r T prior post -> ent_reduction r T prior post.
Proof.
  intros r T prior post [H1 H3]. exists (ent2_obs_fibre r prior). split; [| split].
  - intros x Hx. destruct (H1 x Hx) as [t [Ht Hr]]. exists t. split; [exact Ht |].
    split; [| exact Hr]. unfold ent2_obs_fibre. apply filter_In. split; [exact Hx |].
    apply eqb_spec. exact Hr.
  - exact (ent2_cover_sum r prior post H1).
  - exact H3.
Qed.

Theorem ent2_partition_bits : forall r T (prior post : list X),
  0 < length post -> ent2_partition r T prior post ->
  Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_depth T.
Proof.
  intros r T prior post Hpos Hp.
  apply (ent_index_bits_le_depth r T prior post Hpos), ent2_partition_to_reduction, Hp.
Qed.

End Partition.

(* A covering by fibres is weaker than a partition: if two survivors look
   alike, a covering may split their class between them, and a partition may
   not. Four rivals, two survivors, one observation, a tree with two leaves. *)
Theorem ent2_reduction_not_partition :
  exists (prior post : list nat) (r : nat -> nat) (T : ent_tree),
    ent_reduction r T prior post /\
    ~ ent2_partition Nat.eqb r T prior post.
Proof.
  exists [0; 1; 2; 3], [0; 1], (fun _ => 0), (ent_complete 1). split.
  - exists (fun t => if Nat.eqb t 0 then [0; 1] else [2; 3]). split; [| split].
    + intros x Hx. simpl in Hx.
      destruct Hx as [<- | [<- | [<- | [<- | []]]]].
      * exists 0. simpl. repeat split; auto.
      * exists 0. simpl. repeat split; auto.
      * exists 1. simpl. repeat split; auto.
      * exists 1. simpl. repeat split; auto.
    + simpl. lia.
    + intros t Ht. simpl in Ht. destruct Ht as [<- | [<- | []]]; simpl; lia.
  - intros [_ Hb]. specialize (Hb 0 (or_introl eq_refl)). vm_compute in Hb. lia.
Qed.

(* ================================================================= *)
(* 2. The weighted bound.                                             *)
(* ================================================================= *)

Definition ent2_mass {X : Type} (w : list (X * nat)) : nat :=
  fold_right Nat.add 0 (map snd w).

(* A uniform weight of 1 is the unweighted case. *)
Lemma ent2_mass_uniform : forall {X : Type} (l : list X),
  ent2_mass (map (fun x => (x, 1)) l) = length l.
Proof.
  intros X l. unfold ent2_mass. induction l as [| x l IH]; simpl; [reflexivity |].
  rewrite <- IH. reflexivity.
Qed.

(* The weighted covering: the prior's mass is at most the tree's leaves
   times the posterior's mass. *)
Definition ent2_wcovers {X : Type} (T : ent_tree) (prior post : list (X * nat)) : Prop :=
  ent2_mass prior <= ent_leaves T * ent2_mass post.

Theorem ent2_weighted_bits : forall {X : Type} (T : ent_tree) (prior post : list (X * nat)),
  0 < ent2_mass post -> ent2_wcovers T prior post ->
  Nat.log2_up (ent2_mass prior) - Nat.log2_up (ent2_mass post) <= ent_depth T.
Proof.
  intros X T prior post Hpos Hc.
  pose proof (ent_cover_bits _ _ _ Hpos Hc). pose proof (ent_log2_leaves_le_depth T). lia.
Qed.

(* The weighted fibre form: each survivor t stands for a weighted fibre
   F t; every rival is in the fibre of a survivor with the same
   representative observation; the fibre masses add up to the prior's mass;
   and no fibre weighs more than the tree's leaves times its survivor's own
   weight. *)
Definition ent2_wreduction {X O : Type} (r : X -> O) (T : ent_tree)
    (prior post : list (X * nat)) : Prop :=
  exists F : X -> list (X * nat),
    (forall p, In p prior -> exists t, In t post /\ In p (F (fst t)) /\ r (fst p) = r (fst t)) /\
    ent2_mass prior <= fold_right Nat.add 0 (map (fun t => ent2_mass (F (fst t))) post) /\
    (forall t, In t post -> ent2_mass (F (fst t)) <= ent_leaves T * snd t).

Theorem ent2_wreduction_covers : forall {X O : Type} (r : X -> O) (T : ent_tree)
    (prior post : list (X * nat)),
  ent2_wreduction r T prior post -> ent2_wcovers T prior post.
Proof.
  intros X O r T prior post [F [_ [Hsum Hb]]]. unfold ent2_wcovers.
  assert (Hle : fold_right Nat.add 0 (map (fun t => ent2_mass (F (fst t))) post)
                <= ent_leaves T * ent2_mass post).
  { clear Hsum. unfold ent2_mass at 2. induction post as [| t post IH]; simpl; [lia |].
    assert (Ht : ent2_mass (F (fst t)) <= ent_leaves T * snd t)
      by (apply Hb; left; reflexivity).
    assert (Hr : fold_right Nat.add 0 (map (fun t => ent2_mass (F (fst t))) post)
                 <= ent_leaves T * fold_right Nat.add 0 (map snd post))
      by (apply IH; intros u Hu; apply Hb; right; exact Hu).
    rewrite Nat.mul_add_distr_l. lia. }
  lia.
Qed.

(* On a certification system: a weighted covering and enough paid steps
   put the weighted index bits under the bill. *)
Theorem ent2_weighted_cs : forall (C : CertificationSystem) {X : Type}
    (tr : list (cs_instr C)) (prior post : list (X * nat)) (T : ent_tree),
  0 < ent2_mass post -> ent2_wcovers T prior post ->
  ent_depth T <= ent_cs_paid C tr ->
  Nat.log2_up (ent2_mass prior) - Nat.log2_up (ent2_mass post) <= ent_cs_bill C tr.
Proof.
  intros C X tr prior post T Hpos Hc Hp.
  pose proof (ent2_weighted_bits T prior post Hpos Hc).
  pose proof (ent_cs_paid_le_bill C tr). lia.
Qed.

(* THE WEIGHTED REPRESENTATION THEOREM. The hypotheses of ent_representation
   with the lists weighted: the supports are the lists of rivals, the
   covering is of masses. The conclusions are the same, with weighted index
   bits. *)
Theorem ent2_weighted_representation :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (d : list (m_move M) -> O) (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list (X * nat)) (T : ent_tree),
    thiele_complete_with I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist (map fst post) (map fst prior) ->
    (exists w, In w (map fst prior) /\ ~ In w (map fst post) /\
               ent_distinguishes obs w (map fst post)) ->
    ti_clean I s0 ->
    ent_certified I s0 tr d (ent_member eqb obs (map fst post)) ->
    ent_depth T <= record_moves I tr ->
    0 < ent2_mass post ->
    ent2_wreduction r T prior post ->
    ent_strictly_stronger (ent_member eqb obs (map fst post))
                          (ent_member eqb obs (map fst prior)) /\
    earned_chain I s0 tr /\
    Nat.log2_up (ent2_mass prior) - Nat.log2_up (ent2_mass post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0 /\
    ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I X O s0 tr d obs r eqb prior post T HC Heq [Hincl _] [w [Hw [_ Hd]]]
         H0 [Hrec _] HT Hpos Hred.
  pose proof HC as [_ [[_ [Hchain _]] [Htoll _]]].
  split; [apply (ent_narrowing_strengthens eqb obs (map fst prior) (map fst post) w
                   Heq Hincl Hw Hd) |].
  split; [apply Hchain; assumption |].
  split; [pose proof (ent2_weighted_bits T prior post Hpos (ent2_wreduction_covers r T prior post Hred));
          lia |].
  split; [apply ent_ledger_rise, Htoll |].
  destruct (certificate_costs_three M I HC s0 tr H0 Hrec) as [_ H3]. lia.
Qed.

(* The ledger's rise on a Thiele-complete machine is a function of the
   moves alone, the same from every start. So the expectation over a
   weighted prior of machine states is the mass times the record moves, and
   the weighted bound needs no averaging argument. *)
Theorem ent2_rise_independent : forall (M : machine) (I : thiele_interface M),
  exact_toll_clause I -> forall tr s s',
    ti_ledger I (run M tr s) - ti_ledger I s = ti_ledger I (run M tr s') - ti_ledger I s'.
Proof.
  intros M I Ht tr s s'. rewrite <- (ent_ledger_rise M I Ht tr s), <- (ent_ledger_rise M I Ht tr s').
  reflexivity.
Qed.

Definition ent2_expected_rise {M : machine} (I : thiele_interface M)
    (tr : list (m_move M)) (prior : list (m_state M * nat)) : nat :=
  fold_right (fun p acc => snd p * (ti_ledger I (run M tr (fst p)) - ti_ledger I (fst p)) + acc)
    0 prior.

Theorem ent2_expected_rise_exact : forall (M : machine) (I : thiele_interface M),
  exact_toll_clause I -> forall tr (prior : list (m_state M * nat)),
    ent2_expected_rise I tr prior = ent2_mass prior * record_moves I tr.
Proof.
  intros M I Ht tr prior. unfold ent2_expected_rise, ent2_mass.
  induction prior as [| p prior IH]; simpl; [reflexivity |].
  rewrite IH, <- (ent_ledger_rise M I Ht tr (fst p)). lia.
Qed.

(* The expected-entropy form: the weighted index-bit drop times the prior's
   mass is at most the weighted numerator of the ledger's rise. *)
Theorem ent2_weighted_expected_bound :
  forall (M : machine) (I : thiele_interface M),
    exact_toll_clause I ->
    forall (tr : list (m_move M)) (prior post : list (m_state M * nat)) (T : ent_tree),
      0 < ent2_mass post -> ent2_wcovers T prior post ->
      ent_depth T <= record_moves I tr ->
      (Nat.log2_up (ent2_mass prior) - Nat.log2_up (ent2_mass post)) * ent2_mass prior
        <= ent2_expected_rise I tr prior.
Proof.
  intros M I Ht tr prior post T Hpos Hc HT.
  rewrite (ent2_expected_rise_exact M I Ht tr prior).
  rewrite Nat.mul_comm. apply Nat.mul_le_mono_l.
  pose proof (ent2_weighted_bits T prior post Hpos Hc). lia.
Qed.

(* ================================================================= *)
(* 3. The observational variant: no record clause.                    *)
(* ================================================================= *)

(* The price bound needs the exact toll and nothing else. No clean start,
   no raised record, no universal base. The receipts only have to be
   accepted by the posterior's test. *)
Theorem ent2_observed_representation :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (d : list (m_move M) -> O) (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    exact_toll_clause I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist post prior ->
    (exists w, In w prior /\ ~ In w post /\ ent_distinguishes obs w post) ->
    ent_member eqb obs post (d tr) = true ->
    ent_depth T <= record_moves I tr ->
    0 < length post ->
    ent_reduction r T prior post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0.
Proof.
  intros M I X O s0 tr d obs r eqb prior post T Htoll Heq [Hincl _] [w [Hw [_ Hd]]]
         _ HT Hpos Hred.
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [pose proof (ent_index_bits_le_depth r T prior post Hpos Hred); lia |].
  apply ent_ledger_rise, Htoll.
Qed.

(* The observational variant with a partition in place of a covering. *)
Theorem ent2_observed_partition_representation :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (d : list (m_move M) -> O) (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    exact_toll_clause I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist post prior ->
    (exists w, In w prior /\ ~ In w post /\ ent_distinguishes obs w post) ->
    ent_member eqb obs post (d tr) = true ->
    ent_depth T <= record_moves I tr ->
    0 < length post ->
    ent2_partition eqb r T prior post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0.
Proof.
  intros M I X O s0 tr d obs r eqb prior post T Htoll Heq Hs Hw Hm HT Hpos Hp.
  apply (ent2_observed_representation M I X O s0 tr d obs r eqb prior post T
           Htoll Heq Hs Hw Hm HT Hpos).
  apply (ent2_partition_to_reduction eqb Heq). exact Hp.
Qed.

(* The record adds exactly the earned chain and the floor. *)
Theorem ent2_record_adds : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true ->
    earned_chain I s0 tr /\ ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I HC s0 tr H0 Hrec.
  pose proof HC as [_ [[_ [Hchain _]] _]].
  split; [apply Hchain; assumption |].
  destruct (certificate_costs_three M I HC s0 tr H0 Hrec) as [_ H3]. lia.
Qed.

(* From a clean start the record is up exactly when the run contains the
   earned chain. So an observed shortcut upgrades to a full one exactly
   when its run contains the chain. *)
Theorem ent2_upgrade_iff : forall (M : machine) (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 ->
    (m_record M (run M tr s0) = true <-> earned_chain I s0 tr).
Proof.
  intros M I HC s0 tr H0. pose proof HC as [_ [[_ [Hchain _]] _]]. split.
  - intro H. apply Hchain; assumption.
  - intros [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [_ [_ [_ [_ [_ [_ Hup]]]]]]]]]]]]]]].
    rewrite Htr. pose proof HC as [[_ [_ [_ Hstay]]] _].
    assert (Hlist : pre ++ chk :: mid1 ++ cmt :: mid2 ++ crt :: post
                    = (pre ++ chk :: mid1 ++ cmt :: mid2 ++ [crt]) ++ post)
      by list_eq.
    rewrite Hlist, run_app.
    assert (Hs : forall l s, m_record M s = true -> m_record M (run M l s) = true)
      by (induction l; intros; simpl; auto).
    apply Hs. exact Hup.
Qed.

(* An observed shortcut: the data of ent_shortcut without the clean start
   and without the raised record. *)
Record ent2_observed_shortcut {M : machine} (I : thiele_interface M) (X O : Type)
    (s0 : m_state M) (tr : list (m_move M)) : Type := {
  ent2_os_decoder : list (m_move M) -> O;
  ent2_os_obs : X -> O;
  ent2_os_repr : X -> O;
  ent2_os_eqb : O -> O -> bool;
  ent2_os_prior : list X;
  ent2_os_post : list X;
  ent2_os_tree : ent_tree;
  ent2_os_eqb_spec : forall o1 o2, ent2_os_eqb o1 o2 = true <-> o1 = o2;
  ent2_os_narrowing : ent_strict_sublist ent2_os_post ent2_os_prior;
  ent2_os_witness : exists w, In w ent2_os_prior /\ ~ In w ent2_os_post /\
                      ent_distinguishes ent2_os_obs w ent2_os_post;
  ent2_os_accepted : ent_member ent2_os_eqb ent2_os_obs ent2_os_post (ent2_os_decoder tr) = true;
  ent2_os_realized : ent_depth ent2_os_tree <= record_moves I tr;
  ent2_os_nonempty : 0 < length ent2_os_post;
  ent2_os_reduction : ent_reduction ent2_os_repr ent2_os_tree ent2_os_prior ent2_os_post
}.

Arguments ent2_os_decoder {M I X O s0 tr} _.
Arguments ent2_os_obs {M I X O s0 tr} _.
Arguments ent2_os_repr {M I X O s0 tr} _.
Arguments ent2_os_eqb {M I X O s0 tr} _.
Arguments ent2_os_prior {M I X O s0 tr} _.
Arguments ent2_os_post {M I X O s0 tr} _.
Arguments ent2_os_tree {M I X O s0 tr} _.

(* Every observed shortcut lands in the bound, on any machine with the exact
   toll. True by packaging. *)
Theorem ent2_every_observed_shortcut_lands_here :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M)) (sc : ent2_observed_shortcut I X O s0 tr),
    exact_toll_clause I ->
    ent_strictly_stronger
      (ent_member (ent2_os_eqb sc) (ent2_os_obs sc) (ent2_os_post sc))
      (ent_member (ent2_os_eqb sc) (ent2_os_obs sc) (ent2_os_prior sc)) /\
    Nat.log2_up (length (ent2_os_prior sc)) - Nat.log2_up (length (ent2_os_post sc))
      <= ti_ledger I (run M tr s0) - ti_ledger I s0.
Proof.
  intros M I X O s0 tr sc Htoll.
  destruct (ent2_observed_representation M I X O s0 tr (ent2_os_decoder sc) (ent2_os_obs sc)
              (ent2_os_repr sc) (ent2_os_eqb sc) (ent2_os_prior sc) (ent2_os_post sc)
              (ent2_os_tree sc) Htoll (@ent2_os_eqb_spec M I X O s0 tr sc)
              (@ent2_os_narrowing M I X O s0 tr sc) (@ent2_os_witness M I X O s0 tr sc)
              (@ent2_os_accepted M I X O s0 tr sc) (@ent2_os_realized M I X O s0 tr sc)
              (@ent2_os_nonempty M I X O s0 tr sc) (@ent2_os_reduction M I X O s0 tr sc))
    as [H1 [H2 H3]].
  split; [exact H1 |]. lia.
Qed.

(* ---- A member whose record stays down ---- *)

(* The small machine's worked member (EntitlementSmall.v) with its COMMIT
   and CERTIFY left off: two questions, nothing committed, record down. *)
Definition ent2_obs_trace : list E.instr :=
  [E.CHECK E.PEven E.CA; E.CHECK (E.PGe 2) E.CA].

Lemma ent2_obs_depth : ent_depth (ent_complete 2) <= record_moves earned_interface ent2_obs_trace.
Proof. vm_compute. lia. Qed.

Theorem ent2_observed_small_instance :
  ent_strictly_stronger (ent_member ent_bools_eqb ent_obs ent_post)
                        (ent_member ent_bools_eqb ent_obs ent_prior) /\
  Nat.log2_up (length ent_prior) - Nat.log2_up (length ent_post) = 2 /\
  E.mu (run earned_machine ent2_obs_trace ent_s0) - E.mu ent_s0 = 2 /\
  Nat.log2_up (length ent_prior) - Nat.log2_up (length ent_post)
    <= E.mu (run earned_machine ent2_obs_trace ent_s0) - E.mu ent_s0 /\
  E.cert (E.run ent2_obs_trace ent_s0) = false /\
  ~ earned_chain earned_interface ent_s0 ent2_obs_trace /\
  ~ (ti_ledger earned_interface ent_s0 + 3
       <= ti_ledger earned_interface (run earned_machine ent2_obs_trace ent_s0)).
Proof.
  pose proof ent_earned_complete_with as HC. pose proof HC as [_ [_ [Htoll _]]].
  destruct (ent2_observed_representation earned_machine earned_interface E.state (list bool)
              ent_s0 ent2_obs_trace ent_decode ent_obs ent_repr ent_bools_eqb
              ent_prior ent_post (ent_complete 2) Htoll ent_bools_eqb_eq
              ent_small_narrowing ent_small_witness ltac:(vm_compute; reflexivity)
              ent2_obs_depth ltac:(simpl; lia) ent_small_reduction)
    as [C1 [C4 C5]].
  split; [exact C1 |]. split; [reflexivity |].
  split; [vm_compute; reflexivity |].
  split; [simpl in C5; simpl; lia |].
  split; [vm_compute; reflexivity |].
  split.
  - intros [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr _]]]]]]]]].
    apply (f_equal (@length _)) in Htr. unfold ent2_obs_trace in Htr. simpl in Htr.
    repeat (rewrite app_length in Htr; simpl in Htr). lia.
  - intro H. vm_compute in H. lia.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions ent2_cover_sum_gen.
Print Assumptions ent2_cover_sum.
Print Assumptions ent2_partition_old_iff.
Print Assumptions ent2_partition_to_reduction.
Print Assumptions ent2_partition_bits.
Print Assumptions ent2_reduction_not_partition.
Print Assumptions ent2_mass_uniform.
Print Assumptions ent2_weighted_bits.
Print Assumptions ent2_wreduction_covers.
Print Assumptions ent2_weighted_cs.
Print Assumptions ent2_weighted_representation.
Print Assumptions ent2_rise_independent.
Print Assumptions ent2_expected_rise_exact.
Print Assumptions ent2_weighted_expected_bound.
Print Assumptions ent2_observed_representation.
Print Assumptions ent2_observed_partition_representation.
Print Assumptions ent2_record_adds.
Print Assumptions ent2_upgrade_iff.
Print Assumptions ent2_every_observed_shortcut_lands_here.
Print Assumptions ent2_observed_small_instance.
