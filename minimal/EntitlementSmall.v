(** EntitlementSmall.v: structural entitlement, stated on the model and
    run on the small machine.

    The question. A run narrows a list of rivals (the prior) to a shorter
    list (the posterior) and ends with its record up. What does the run
    have to have paid? The counting floor says: a yes/no question splits a
    list into at most two piles, so f questions tell apart at most 2^f
    cases, and narrowing a prior of n rivals to a posterior of m needs at
    least log2 n - log2 m questions (rounded up separately, cut off at 0).
    This file ties that floor to moves the run actually made and paid for.

    What is proved (every result closed under the global context):

      1. Decision trees and the counting floor, on their own. A tree is no
         wider than two to its depth [ent_leaves_le_pow2,
         ent_log2_leaves_le_depth]; a covering |prior| <= leaves * |post|
         gives the index-bit drop at most the depth
         [ent_index_bits_le_depth]; narrowing with a distinguishing rival
         makes the membership test strictly stronger
         [ent_narrowing_strengthens].
      2. On any certification system (ThieleComplete.v's record). A run
         whose reading goes from no to yes contains a raising step that
         costs at least 1 [ent_cs_raising_step], and a run with at least
         depth(T) paid steps has a bill of at least the index bits a
         covering by T commits to [ent_cs_count]. Together, with every
         hypothesis printed [ent_cs_entitlement].
      3. On every Thiele-complete machine. The representation theorem
         [ent_representation]: eight hypotheses (exact equality test,
         strict narrowing, a distinguishing rival, a clean start, a
         certified end, a tree no deeper than the record moves the run
         made, a non-empty posterior, a covering by fibres) give six
         conclusions: a strictly stronger posterior test, the earned chain
         (a passing CHECK, a COMMIT of the same claim, the CERTIFY that
         raised the record), the committed claim held when checked and when
         committed, the index-bit drop at most the record moves the run
         made, those moves equal to the ledger's rise, and the ledger up by
         at least 3. A shortcut that hands over its receipts and these data
         is a record [ent_shortcut]; every one lands in the bound
         [ent_every_shortcut_lands_here]. The distinguishing observation
         can never be the representative one [ent_two_observations]. A
         complete tree of the right depth always covers, so a run with
         enough record moves pays the index bits with no tree supplied,
         only a count [ent_exists_covering_tree, ent_complete_tree_bound].
      4. A floor with no supplied tree [ent_questions_floor]. The questions
         are the claims the run's own CHECK moves asked. Asked of every
         rival, they split the prior by answers; if no answer class is
         bigger than m, then the index-bit drop to m is at most the number
         of CHECK moves the run made, which is at most its record moves,
         which is the ledger's rise.
      5. The small machine (EarnedCore.v) is an instance, with a worked
         member [ent_small_instance, ent_small_shortcut,
         ent_small_lands, ent_small_questions]. Eight rivals: counter A in
         0..3, counter B in 0..1. The program CHECK "A is even",
         CHECK "A >= 2", COMMIT "A >= 2", CERTIFY. The posterior is the two
         rivals with A = 2, and it is exactly the set of rivals from which
         that program raises the record [ent_small_posterior_is_certified].
         The representative observation reads B, so each survivor stands
         for the four rivals sharing its B. Index bits: 3 - 1 = 2; record
         moves and ledger rise: 4; CHECK moves: 2, so the questions floor
         is met with equality.

      6. The run generates the narrowing [ent_run_entitlement]. The
         candidates are start states; each CHECK the run made and passed is
         a test, asked of a candidate by replaying the run's prefix from it;
         the posterior is the candidates that pass every such test. On
         every Thiele-complete machine, from a clean start, on a run ending
         with the record up and a prior containing the start: the
         posterior sits inside the prior and keeps the start; every dropped
         candidate fails, replayed, a check the run passed; the exact count
         |prior| * (product of the "after" lengths) = |post| * (product of
         the "before" lengths) holds [ent_stages_product]; if every passing
         check keeps at least a 2^-k share of the candidates standing
         before it, the index bits lost are at most k times the passing
         checks, at most k times the record moves, which are the ledger's
         rise. With no share assumed, the index bits are at most the sum of
         log2 (before / after) rounded up [ent_run_round_bits]. On the
         small machine the worked member's posterior is generated by its
         run, 8 to 4 to 2 [ent_small_run_narrowing], and the share
         hypothesis can't be dropped: CHECK "A >= 15" narrows sixteen
         candidates to one, 4 index bits for 3 record moves
         [ent_share_needed].

    What is not proved, said plainly. The prior, the posterior, the tree
    and the fibres in item 3 are supplied; nothing reads them off the run
    (item 6 reads the posterior off the run, given the prior).
    The covering limits how much can be dropped per leaf paid for; it does
    not say why anything was dropped. In item 4 the questions are the run's
    own, but they are asked of each rival directly, not at the state the
    run was in when it checked. Free branching (a DEC on zero) can narrow
    without paying, so nothing here says every narrowing costs; it says a
    narrowing explained by the run's paid moves costs at least its index
    bits.

    Dependencies: Coq standard library, ThieleComplete.v and the files it
    requires (EarnedCore.v, EarnedGeneric.v). No axioms, no Admitted.      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* 1. Decision trees, the counting floor, strengthening.              *)
(* ================================================================= *)

(* A decision tree is a bare shape: a leaf, or a branch with two subtrees.
   Nothing is written on it. *)
Inductive ent_tree : Type :=
| ent_leaf
| ent_branch (l r : ent_tree).

Fixpoint ent_depth (t : ent_tree) : nat :=
  match t with
  | ent_leaf => 0
  | ent_branch l r => S (Nat.max (ent_depth l) (ent_depth r))
  end.

Fixpoint ent_leaves (t : ent_tree) : nat :=
  match t with
  | ent_leaf => 1
  | ent_branch l r => ent_leaves l + ent_leaves r
  end.

(* The complete tree of depth k. *)
Fixpoint ent_complete (k : nat) : ent_tree :=
  match k with 0 => ent_leaf | S k => ent_branch (ent_complete k) (ent_complete k) end.

Lemma ent_complete_depth : forall k, ent_depth (ent_complete k) = k.
Proof. induction k; simpl; [reflexivity | rewrite IHk, Nat.max_id; reflexivity]. Qed.

Lemma ent_complete_leaves : forall k, ent_leaves (ent_complete k) = 2 ^ k.
Proof. induction k; simpl; [reflexivity | rewrite IHk; lia]. Qed.

Lemma ent_leaves_le_pow2 : forall t, ent_leaves t <= 2 ^ ent_depth t.
Proof.
  induction t as [| l IHl r IHr]; simpl; [lia |].
  assert (2 ^ ent_depth l <= 2 ^ Nat.max (ent_depth l) (ent_depth r))
    by (apply Nat.pow_le_mono_r; lia).
  assert (2 ^ ent_depth r <= 2 ^ Nat.max (ent_depth l) (ent_depth r))
    by (apply Nat.pow_le_mono_r; lia).
  lia.
Qed.

Lemma ent_leaves_pos : forall t, 0 < ent_leaves t.
Proof. induction t; simpl; lia. Qed.

Lemma ent_log2_leaves_le_depth : forall t, Nat.log2_up (ent_leaves t) <= ent_depth t.
Proof.
  intro t. apply (proj1 (Nat.log2_up_le_pow2 _ _ (ent_leaves_pos t))).
  apply ent_leaves_le_pow2.
Qed.

(* The arithmetic of the count: a covering a <= l * b, with b > 0, drops at
   most log2 l index bits. *)
Lemma ent_cover_bits : forall a b l,
  0 < b -> a <= l * b -> Nat.log2_up a - Nat.log2_up b <= Nat.log2_up l.
Proof.
  intros a b l Hb H.
  assert (H1 : Nat.log2_up a <= Nat.log2_up (l * b)) by (apply Nat.log2_up_le_mono; exact H).
  assert (H2 : Nat.log2_up (l * b) <= Nat.log2_up l + Nat.log2_up b)
    by (apply Nat.log2_up_mul_above; lia).
  lia.
Qed.

Section Rivals.

Context {X O : Type}.

(* The posterior is a strict sublist of the prior. *)
Definition ent_strict_sublist (post prior : list X) : Prop :=
  incl post prior /\ exists x, In x prior /\ ~ In x post.

(* The rival w gives an observation no posterior rival gives. *)
Definition ent_distinguishes (obs : X -> O) (w : X) (post : list X) : Prop :=
  forall t, In t post -> obs w <> obs t.

(* The membership test of a list under an observation. *)
Definition ent_member (eqb : O -> O -> bool) (obs : X -> O) (L : list X) (o : O) : bool :=
  existsb (fun t => eqb (obs t) o) L.

Definition ent_stronger (P Q : O -> bool) : Prop :=
  forall o, P o = true -> Q o = true.

Definition ent_strictly_stronger (P Q : O -> bool) : Prop :=
  ent_stronger P Q /\ exists o, P o = false /\ Q o = true.

(* A covering by fibres: each posterior rival t stands for a fibre F t of
   prior rivals; every prior rival sits in the fibre of a survivor with the
   same representative observation; the fibres add up to at least the
   prior's length; and no fibre has more members than the tree has
   leaves. *)
Definition ent_reduction (r : X -> O) (T : ent_tree) (prior post : list X) : Prop :=
  exists F : X -> list X,
    (forall x, In x prior -> exists t, In t post /\ In x (F t) /\ r x = r t) /\
    length prior <= fold_right Nat.add 0 (map (fun t => length (F t)) post) /\
    (forall t, In t post -> length (F t) <= ent_leaves T).

Theorem ent_narrowing_strengthens :
  forall (eqb : O -> O -> bool) (obs : X -> O) (prior post : list X) (w : X),
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    incl post prior ->
    In w prior -> ent_distinguishes obs w post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior).
Proof.
  intros eqb obs prior post w Heq Hincl Hw Hdist. split.
  - intros o H. unfold ent_member in *. apply existsb_exists in H as [t [Ht Ho]].
    apply existsb_exists. exists t. split; [apply Hincl, Ht | exact Ho].
  - exists (obs w). split.
    + unfold ent_member. destruct (existsb (fun t => eqb (obs t) (obs w)) post) eqn:E;
        [| reflexivity].
      apply existsb_exists in E as [t [Ht Ho]]. apply Heq in Ho.
      exfalso. apply (Hdist t Ht). symmetry. exact Ho.
    + unfold ent_member. apply existsb_exists. exists w. split; [exact Hw |].
      apply Heq. reflexivity.
Qed.

Lemma ent_reduction_covers : forall r T prior post,
  ent_reduction r T prior post -> length prior <= ent_leaves T * length post.
Proof.
  intros r T prior post [F [_ [Hsum Hb]]].
  assert (Hle : fold_right Nat.add 0 (map (fun t => length (F t)) post)
                <= ent_leaves T * length post).
  { clear Hsum. induction post as [| t post IH]; simpl; [lia |].
    assert (Ht : length (F t) <= ent_leaves T) by (apply Hb; left; reflexivity).
    assert (Hr : fold_right Nat.add 0 (map (fun t => length (F t)) post)
                 <= ent_leaves T * length post)
      by (apply IH; intros u Hu; apply Hb; right; exact Hu).
    rewrite Nat.mul_succ_r. lia. }
  lia.
Qed.

Theorem ent_index_bits_le_depth : forall r T (prior post : list X),
  0 < length post -> ent_reduction r T prior post ->
  Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_depth T.
Proof.
  intros r T prior post Hpos Hred.
  eapply Nat.le_trans; [| apply ent_log2_leaves_le_depth].
  apply ent_cover_bits; [exact Hpos |]. apply (ent_reduction_covers r), Hred.
Qed.

(* Why two observations: the distinguishing observation can never serve as
   the representative one. *)
Theorem ent_two_observations : forall (obs : X -> O) (T : ent_tree) (prior post : list X) w,
  In w prior -> ent_distinguishes obs w post -> ~ ent_reduction obs T prior post.
Proof.
  intros obs T prior post w Hw Hd [F [Hassign _]].
  destruct (Hassign w Hw) as [t [Ht [_ Heq]]]. exact (Hd t Ht Heq).
Qed.

(* For any two lists with a non-empty posterior, the complete tree of depth
   log2_up (|prior| / |post| + 1) covers the narrowing. *)
Theorem ent_exists_covering_tree : forall (prior post : list X),
  0 < length post ->
  length prior
    <= ent_leaves (ent_complete (Nat.log2_up (length prior / length post + 1))) * length post.
Proof.
  intros prior post Hpos. rewrite ent_complete_leaves.
  set (q := length prior / length post).
  assert (Hq : length prior < (q + 1) * length post).
  { pose proof (Nat.div_mod (length prior) (length post) ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound (length prior) (length post) ltac:(lia)) as Hmb.
    unfold q. nia. }
  assert (Hp : q + 1 <= 2 ^ Nat.log2_up (q + 1)).
  { apply (proj2 (Nat.log2_up_le_pow2 (q + 1) (Nat.log2_up (q + 1)) ltac:(lia))). lia. }
  assert ((q + 1) * length post <= 2 ^ Nat.log2_up (q + 1) * length post)
    by (apply Nat.mul_le_mono_r; exact Hp).
  lia.
Qed.

End Rivals.

(* ================================================================= *)
(* 2. On any certification system.                                    *)
(* ================================================================= *)

Section OnCertificationSystems.

Variable C : CertificationSystem.

Fixpoint ent_cs_run (tr : list (cs_instr C)) (s : cs_state C) : cs_state C :=
  match tr with [] => s | i :: rest => ent_cs_run rest (cs_step C s i) end.

(* The bill of a run: the sum of what each step was charged. *)
Fixpoint ent_cs_bill (tr : list (cs_instr C)) : nat :=
  match tr with [] => 0 | i :: rest => cs_cost C i + ent_cs_bill rest end.

(* The paid steps of a run: the steps charged at least 1. *)
Fixpoint ent_cs_paid (tr : list (cs_instr C)) : nat :=
  match tr with
  | [] => 0
  | i :: rest => (if Nat.leb 1 (cs_cost C i) then 1 else 0) + ent_cs_paid rest
  end.

Lemma ent_cs_paid_le_bill : forall tr, ent_cs_paid tr <= ent_cs_bill tr.
Proof.
  induction tr as [| i tr IH]; simpl; [lia |].
  destruct (cs_cost C i); simpl; lia.
Qed.

(* A run whose reading goes from no to yes contains the step that raised
   it, and that step paid the toll. *)
Theorem ent_cs_raising_step : forall tr s,
  cs_cert C s = false -> cs_cert C (ent_cs_run tr s) = true ->
  exists pre i post, tr = pre ++ i :: post /\
    cs_cert C (ent_cs_run pre s) = false /\
    cs_cert C (cs_step C (ent_cs_run pre s) i) = true /\ cs_cost C i >= 1.
Proof.
  induction tr as [| i tr IH]; intros s H0 H1; simpl in H1; [congruence |].
  destruct (cs_cert C (cs_step C s i)) eqn:Hi.
  - exists [], i, tr. simpl. repeat split; auto. apply (cs_cert_costs C s i H0 Hi).
  - destruct (IH (cs_step C s i) Hi H1) as [pre [j [post [Htr [Ha [Hb Hc]]]]]].
    exists (i :: pre), j, post. simpl. rewrite Htr. auto.
Qed.

(* The count: given a covering of the narrowing by a tree and a run with
   at least depth(T) paid steps, the bill covers the index bits. *)
Theorem ent_cs_count : forall {X : Type} (tr : list (cs_instr C))
    (prior post : list X) (T : ent_tree),
  0 < length post ->
  length prior <= ent_leaves T * length post ->
  ent_depth T <= ent_cs_paid tr ->
  Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_cs_bill tr.
Proof.
  intros X tr prior post T Hpos Hcov Hpaid.
  pose proof (ent_cover_bits _ _ _ Hpos Hcov).
  pose proof (ent_log2_leaves_le_depth T). pose proof (ent_cs_paid_le_bill tr). lia.
Qed.

(* Structural entitlement on a certification system, every hypothesis
   printed. *)
Theorem ent_cs_entitlement :
  forall {X O : Type} (tr : list (cs_instr C)) (s : cs_state C)
         (d : list (cs_instr C) -> O) (obs : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist post prior ->
    (exists w, In w prior /\ ~ In w post /\ ent_distinguishes obs w post) ->
    cs_cert C s = false ->
    cs_cert C (ent_cs_run tr s) = true ->
    ent_member eqb obs post (d tr) = true ->
    0 < length post ->
    length prior <= ent_leaves T * length post ->
    ent_depth T <= ent_cs_paid tr ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    (exists pre i rest, tr = pre ++ i :: rest /\
       cs_cert C (ent_cs_run pre s) = false /\
       cs_cert C (cs_step C (ent_cs_run pre s) i) = true /\ cs_cost C i >= 1) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= ent_cs_bill tr.
Proof.
  intros X O tr s d obs eqb prior post T Heq [Hincl _] [w [Hw [_ Hd]]] H0 H1 _ Hpos Hcov Hp.
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [apply ent_cs_raising_step; assumption |].
  apply (ent_cs_count tr prior post T Hpos Hcov Hp).
Qed.

End OnCertificationSystems.

(* ================================================================= *)
(* 3. On every Thiele-complete machine.                               *)
(* ================================================================= *)

(* The end of the run is certified for a test P: the record is up, and P
   accepts what the decoder reads off the receipts (the moves of the run). *)
Definition ent_certified {M : machine} (I : thiele_interface M) {O : Type}
    (s0 : m_state M) (tr : list (m_move M))
    (d : list (m_move M) -> O) (P : O -> bool) : Prop :=
  m_record M (run M tr s0) = true /\ P (d tr) = true.

Lemma ent_ledger_rise : forall M (I : thiele_interface M),
  exact_toll_clause I -> forall tr s,
  record_moves I tr = ti_ledger I (run M tr s) - ti_ledger I s.
Proof.
  intros M I Ht tr s. rewrite (ledger_counts_record_moves M I Ht). lia.
Qed.

(* The complete-tree form: no tree is supplied, only a count. If the run
   made at least log2_up (|prior| / |post| + 1) record moves, the ledger
   rose by at least the index bits. Nothing ties the lists to the run; the
   lists only pick how many record moves are needed. *)
Theorem ent_complete_tree_bound : forall (M : machine) (I : thiele_interface M),
  exact_toll_clause I ->
  forall {X : Type} (s0 : m_state M) (tr : list (m_move M)) (prior post : list X),
    0 < length post ->
    Nat.log2_up (length prior / length post + 1) <= record_moves I tr ->
    Nat.log2_up (length prior) - Nat.log2_up (length post)
      <= ti_ledger I (run M tr s0) - ti_ledger I s0.
Proof.
  intros M I Htoll X s0 tr prior post Hpos Hk.
  pose proof (ent_exists_covering_tree prior post Hpos) as Hcov.
  pose proof (ent_cover_bits _ _ _ Hpos Hcov) as Hb.
  pose proof (ent_log2_leaves_le_depth (ent_complete (Nat.log2_up (length prior / length post + 1)))) as Hd.
  rewrite ent_complete_depth in Hd.
  rewrite <- (ent_ledger_rise M I Htoll). lia.
Qed.

(* THE REPRESENTATION THEOREM, on the model.
   (H1) eqb decides equality of observations.
   (H2) the posterior is a strict sublist of the prior.
   (H3) some prior rival not in the posterior is distinguished from every
        posterior rival by obs.
   (H4) the run starts clean.
   (H5) the end is certified for the posterior's membership test.
   (H6) the tree is no deeper than the record moves the run made.
   (H7) the posterior is not empty.
   (H8) there is a covering of the prior by fibres of the posterior, for
        the representative observation r and the tree T.
   Conclusions:
   (C1) the posterior's test is strictly stronger than the prior's.
   (C2) the run contains the earned chain: a passing CHECK of a claim, a
        COMMIT of the same claim with the thing it is about unchanged in
        between, and the CERTIFY that raised the record.
   (C3) the committed claim held when checked and when committed.
   (C4) the index-bit drop is at most the record moves the run made.
   (C5) those record moves are exactly the ledger's rise.
   (C6) the ledger rose by at least 3. *)
Theorem ent_representation :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M))
         (d : list (m_move M) -> O) (obs r : X -> O) (eqb : O -> O -> bool)
         (prior post : list X) (T : ent_tree),
    thiele_complete_with I ->
    (forall o1 o2, eqb o1 o2 = true <-> o1 = o2) ->
    ent_strict_sublist post prior ->
    (exists w, In w prior /\ ~ In w post /\ ent_distinguishes obs w post) ->
    ti_clean I s0 ->
    ent_certified I s0 tr d (ent_member eqb obs post) ->
    ent_depth T <= record_moves I tr ->
    0 < length post ->
    ent_reduction r T prior post ->
    ent_strictly_stronger (ent_member eqb obs post) (ent_member eqb obs prior) /\
    earned_chain I s0 tr /\
    (exists pre c chk mid1 cmt rest,
       tr = pre ++ chk :: mid1 ++ cmt :: rest /\
       ti_kind I chk = KCheck c /\ ti_kind I cmt = KCommit c /\
       ti_meaning I c (run M pre s0) /\ ti_meaning I c (run M (pre ++ chk :: mid1) s0)) /\
    Nat.log2_up (length prior) - Nat.log2_up (length post) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0 /\
    ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I X O s0 tr d obs r eqb prior post T HC Heq [Hincl _] [w [Hw [_ Hd]]]
         H0 [Hrec _] HT Hpos Hred.
  pose proof HC as [_ [[_ [Hchain _]] [Htoll _]]].
  split; [apply (ent_narrowing_strengthens eqb obs prior post w Heq Hincl Hw Hd) |].
  split; [apply Hchain; assumption |].
  split; [apply (committed_claim_holds M I HC s0 tr H0 Hrec) |].
  split; [pose proof (ent_index_bits_le_depth r T prior post Hpos Hred); lia |].
  split; [apply ent_ledger_rise, Htoll |].
  destruct (certificate_costs_three M I HC s0 tr H0 Hrec) as [_ H3]. lia.
Qed.

(* A sound structural shortcut, on the model: seven pieces of data and
   the eight hypotheses (H1)-(H8) for them, fifteen fields in all. The
   receipts it hands over are the moves of its run. *)
Record ent_shortcut {M : machine} (I : thiele_interface M) (X O : Type)
    (s0 : m_state M) (tr : list (m_move M)) : Type := {
  ent_sc_decoder : list (m_move M) -> O;
  ent_sc_obs : X -> O;
  ent_sc_repr : X -> O;
  ent_sc_eqb : O -> O -> bool;
  ent_sc_prior : list X;
  ent_sc_post : list X;
  ent_sc_tree : ent_tree;
  ent_sc_eqb_spec : forall o1 o2, ent_sc_eqb o1 o2 = true <-> o1 = o2;
  ent_sc_narrowing : ent_strict_sublist ent_sc_post ent_sc_prior;
  ent_sc_witness : exists w, In w ent_sc_prior /\ ~ In w ent_sc_post /\
                     ent_distinguishes ent_sc_obs w ent_sc_post;
  ent_sc_clean : ti_clean I s0;
  ent_sc_certified : ent_certified I s0 tr ent_sc_decoder
                       (ent_member ent_sc_eqb ent_sc_obs ent_sc_post);
  ent_sc_realized : ent_depth ent_sc_tree <= record_moves I tr;
  ent_sc_nonempty : 0 < length ent_sc_post;
  ent_sc_reduction : ent_reduction ent_sc_repr ent_sc_tree ent_sc_prior ent_sc_post
}.

Arguments ent_sc_decoder {M I X O s0 tr} _.
Arguments ent_sc_obs {M I X O s0 tr} _.
Arguments ent_sc_repr {M I X O s0 tr} _.
Arguments ent_sc_eqb {M I X O s0 tr} _.
Arguments ent_sc_prior {M I X O s0 tr} _.
Arguments ent_sc_post {M I X O s0 tr} _.
Arguments ent_sc_tree {M I X O s0 tr} _.

(* Every sound shortcut on a Thiele-complete machine lands in the bound.
   True by packaging: the record carries exactly the theorem's
   hypotheses. *)
Theorem ent_every_shortcut_lands_here :
  forall (M : machine) (I : thiele_interface M) (X O : Type)
         (s0 : m_state M) (tr : list (m_move M)) (sc : ent_shortcut I X O s0 tr),
    thiele_complete_with I ->
    ent_strictly_stronger (ent_member (ent_sc_eqb sc) (ent_sc_obs sc) (ent_sc_post sc))
                          (ent_member (ent_sc_eqb sc) (ent_sc_obs sc) (ent_sc_prior sc)) /\
    earned_chain I s0 tr /\
    Nat.log2_up (length (ent_sc_prior sc)) - Nat.log2_up (length (ent_sc_post sc))
      <= ti_ledger I (run M tr s0) - ti_ledger I s0 /\
    ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I X O s0 tr sc HC.
  destruct (ent_representation M I X O s0 tr (ent_sc_decoder sc) (ent_sc_obs sc)
              (ent_sc_repr sc) (ent_sc_eqb sc) (ent_sc_prior sc) (ent_sc_post sc)
              (ent_sc_tree sc) HC (@ent_sc_eqb_spec M I X O s0 tr sc)
              (@ent_sc_narrowing M I X O s0 tr sc) (@ent_sc_witness M I X O s0 tr sc)
              (@ent_sc_clean M I X O s0 tr sc) (@ent_sc_certified M I X O s0 tr sc)
              (@ent_sc_realized M I X O s0 tr sc) (@ent_sc_nonempty M I X O s0 tr sc)
              (@ent_sc_reduction M I X O s0 tr sc))
    as [H1 [H2 [_ [H4 [H5 H6]]]]].
  split; [exact H1 |]. split; [exact H2 |]. split; [lia | exact H6].
Qed.

(* ================================================================= *)
(* 4. A floor with no supplied tree: the run's own questions.         *)
(* ================================================================= *)

Fixpoint ent_bools_eqb (u v : list bool) : bool :=
  match u, v with
  | [], [] => true
  | a :: u', b :: v' => Bool.eqb a b && ent_bools_eqb u' v'
  | _, _ => false
  end.

Lemma ent_bools_eqb_eq : forall u v, ent_bools_eqb u v = true <-> u = v.
Proof.
  induction u as [| a u IH]; destruct v as [| b v]; simpl; split; intro H;
    try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2]. apply Bool.eqb_prop in H1.
    apply IH in H2. subst. reflexivity.
  - inversion H. subst. rewrite Bool.eqb_reflx. simpl. apply IH. reflexivity.
Qed.

(* Every list of k booleans. *)
Fixpoint ent_all_bools (k : nat) : list (list bool) :=
  match k with
  | 0 => [[]]
  | S k => map (cons true) (ent_all_bools k) ++ map (cons false) (ent_all_bools k)
  end.

Lemma ent_all_bools_length : forall k, length (ent_all_bools k) = 2 ^ k.
Proof. induction k; simpl; [reflexivity |]. rewrite app_length, !map_length, IHk. lia. Qed.

Lemma ent_all_bools_complete : forall bl, In bl (ent_all_bools (length bl)).
Proof.
  induction bl as [| b bl IH]; simpl; [left; reflexivity |].
  apply in_or_app. destruct b; [left | right]; apply in_map; exact IH.
Qed.

Lemma ent_filter_split : forall {A} (p : A -> bool) (l : list A),
  length (filter p l) + length (filter (fun x => negb (p x)) l) = length l.
Proof. intros A p l. induction l as [| x l IH]; simpl; [reflexivity |]. destruct (p x); simpl; lia. Qed.

Lemma ent_filter_filter_le : forall {A} (p q : A -> bool) (l : list A),
  length (filter p (filter q l)) <= length (filter p l).
Proof.
  intros A p q l. induction l as [| x l IH]; simpl; [lia |].
  destruct (q x); simpl; destruct (p x) eqn:Hp; simpl; try rewrite Hp; simpl; lia.
Qed.

(* If every value of f on l lies in imgs and no value class of l has more
   than m members, then l has at most m times as many members as imgs. *)
Lemma ent_fibres_count : forall {A B : Type} (eqb : B -> B -> bool),
  (forall u v, eqb u v = true <-> u = v) ->
  forall (f : A -> B) (m : nat) (imgs : list B) (l : list A),
    (forall x, In x l -> In (f x) imgs) ->
    (forall x, In x l -> length (filter (fun y => eqb (f y) (f x)) l) <= m) ->
    length l <= m * length imgs.
Proof.
  intros A B eqb Heq f m imgs. induction imgs as [| v imgs IH]; intros l Himg Hfib.
  - destruct l as [| x l]; [simpl; lia |]. exfalso. apply (Himg x). left. reflexivity.
  - pose proof (ent_filter_split (fun y => eqb (f y) v) l) as Hsplit.
    assert (HA : length (filter (fun y => eqb (f y) v) l) <= m).
    { destruct (filter (fun y => eqb (f y) v) l) as [| x0 rest] eqn:E; [simpl; lia |].
      assert (Hx0 : In x0 (filter (fun y => eqb (f y) v) l)) by (rewrite E; left; reflexivity).
      apply filter_In in Hx0 as [Hx0l Hx0v]. apply Heq in Hx0v.
      rewrite <- E. rewrite <- Hx0v. apply Hfib. exact Hx0l. }
    assert (HB : length (filter (fun y => negb (eqb (f y) v)) l) <= m * length imgs).
    { apply IH.
      - intros x Hx. apply filter_In in Hx as [Hxl Hxv].
        destruct (Himg x Hxl) as [Hfx | Hfx]; [| exact Hfx].
        assert (Hb : eqb (f x) v = true) by (apply Heq; symmetry; exact Hfx).
        rewrite Hb in Hxv. discriminate.
      - intros x Hx. pose proof Hx as Hx'. apply filter_In in Hx' as [Hxl _].
        eapply Nat.le_trans; [apply ent_filter_filter_le | apply Hfib, Hxl]. }
    simpl. rewrite Nat.mul_succ_r. lia.
Qed.

(* The claims the run's CHECK moves asked, in order. *)
Fixpoint ent_checked {M : machine} (I : thiele_interface M) (tr : list (m_move M))
    : list (ti_claim I) :=
  match tr with
  | [] => []
  | m :: rest =>
      match ti_kind I m with
      | KCheck c => c :: ent_checked I rest
      | _ => ent_checked I rest
      end
  end.

(* The answers those same questions give at a rival state x. *)
Definition ent_answers {M : machine} (I : thiele_interface M) (tr : list (m_move M))
    (x : m_state M) : list bool :=
  map (ti_check I x) (ent_checked I tr).

Lemma ent_checked_le_record_moves : forall M (I : thiele_interface M) tr,
  length (ent_checked I tr) <= record_moves I tr.
Proof.
  intros M I tr. induction tr as [| m tr IH]; simpl; [lia |].
  unfold record_move. destruct (ti_kind I m); simpl; lia.
Qed.

(* The questions floor. Whichever rival is the truth, if the run's own
   questions leave at most m rivals with its answers, then the index-bit
   drop from the prior to m is at most the CHECK moves the run made, at
   most its record moves, and those are the ledger's rise. *)
Theorem ent_questions_floor :
  forall (M : machine) (I : thiele_interface M),
    exact_toll_clause I ->
    forall (s0 : m_state M) (tr : list (m_move M)) (prior : list (m_state M)) (m : nat),
      0 < m ->
      (forall x, In x prior ->
         length (filter (fun y => ent_bools_eqb (ent_answers I tr y) (ent_answers I tr x))
                        prior) <= m) ->
      Nat.log2_up (length prior) - Nat.log2_up m <= length (ent_checked I tr) /\
      length (ent_checked I tr) <= record_moves I tr /\
      ti_ledger I (run M tr s0) = ti_ledger I s0 + record_moves I tr.
Proof.
  intros M I Htoll s0 tr prior m Hm Hfib.
  set (k := length (ent_checked I tr)).
  assert (Hcount : length prior <= m * 2 ^ k).
  { rewrite <- ent_all_bools_length.
    apply (ent_fibres_count ent_bools_eqb ent_bools_eqb_eq (ent_answers I tr) m
             (ent_all_bools k) prior); [| exact Hfib].
    intros x _. unfold k.
    replace (length (ent_checked I tr)) with (length (ent_answers I tr x))
      by (unfold ent_answers; apply map_length).
    apply ent_all_bools_complete. }
  split.
  - assert (H1 : Nat.log2_up (length prior) <= Nat.log2_up (m * 2 ^ k))
      by (apply Nat.log2_up_le_mono; exact Hcount).
    assert (H2 : Nat.log2_up (m * 2 ^ k) <= Nat.log2_up m + Nat.log2_up (2 ^ k))
      by (apply Nat.log2_up_mul_above; lia).
    rewrite Nat.log2_up_pow2 in H2 by lia. lia.
  - split; [apply ent_checked_le_record_moves |].
    apply (ledger_counts_record_moves M I Htoll).
Qed.

(* ================================================================= *)
(* 5. The small machine is an instance, with a worked member.         *)
(* ================================================================= *)

(* The small machine's interface meets all four clauses. This is the
   proof of earned_core_thiele_complete, stated for the named interface. *)
Lemma ent_earned_complete_with : thiele_complete_with earned_interface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply E.start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply E.cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply earned_chain_holds; [exact H0 |].
      rewrite <- run_earned. exact H1.
    + split.
      * intros s [p c] H. simpl in *. unfold E.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply E.eval_iff, H.
      * intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
  - split; [intros []; reflexivity | intros s m; apply E.mu_conservation].
  - exists (E.PZero, E.CA), (E.CHECK E.PZero E.CA), (E.COMMIT E.PZero E.CA), E.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 0, 0; reflexivity | exists 1, 0; simpl; intro H; discriminate H]].
    intros a b. destruct a as [| a]; simpl; split; intro H;
      try reflexivity; try discriminate H.
Qed.

(* The two questions about counter A. *)
Definition ent_q : list (E.prop * E.ctr) := [(E.PEven, E.CA); (E.PGe 2, E.CA)].

(* The program: ask both, commit the second, certify. *)
Definition ent_trace : list E.instr :=
  [E.CHECK E.PEven E.CA; E.CHECK (E.PGe 2) E.CA; E.COMMIT (E.PGe 2) E.CA; E.CERTIFY].

(* The distinguishing observation: the answers to the two questions. *)
Definition ent_obs (x : E.state) : list bool :=
  map (fun pc => E.eval (fst pc) (E.val (E.core_of x) (snd pc))) ent_q.

(* The representative observation: whether counter B is 0, the part the
   questions never ask about. *)
Definition ent_repr (x : E.state) : list bool := [E.eval E.PZero (E.cb (E.core_of x))].

Definition ent_is_check (i : E.instr) : bool :=
  match i with E.CHECK _ _ => true | _ => false end.

(* The decoder reads the receipts: one "passed" per CHECK in them. On this
   machine a failing CHECK traps for good, so on a certified run every
   CHECK in the receipts passed. *)
Definition ent_decode (tr : list E.instr) : list bool :=
  map (fun _ => true) (filter ent_is_check tr).

Definition ent_prior : list E.state :=
  [E.start 0 0; E.start 1 0; E.start 2 0; E.start 3 0;
   E.start 0 1; E.start 1 1; E.start 2 1; E.start 3 1].

Definition ent_post : list E.state := [E.start 2 0; E.start 2 1].

Definition ent_s0 : E.state := E.start 2 0.

Definition ent_fibre (t : E.state) : list E.state :=
  filter (fun y => ent_bools_eqb (ent_repr y) (ent_repr t)) ent_prior.

Ltac ent_neq := let H := fresh in intro H; vm_compute in H; congruence.

(* From any start, the program raises the record exactly when A is even and
   at least 2; on the eight rivals that is exactly A = 2. *)
Theorem ent_small_certifies_iff : forall a b,
  E.cert (E.run ent_trace (E.start a b)) = Nat.even a && Nat.leb 2 a.
Proof.
  intros a b. destruct a as [| [| n]]; [reflexivity | reflexivity |].
  cbv -[Nat.even]. change (Nat.even (S (S n))) with (Nat.even n).
  destruct (Nat.even n); cbv; reflexivity.
Qed.

Theorem ent_small_posterior_is_certified : forall x, In x ent_prior ->
  (In x ent_post <-> E.cert (E.run ent_trace x) = true).
Proof.
  intros x Hx. unfold ent_prior in Hx.
  destruct Hx as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]];
    rewrite ent_small_certifies_iff; simpl;
    first
      [ split; [intros _; reflexivity | intros _; auto]
      | split; [intros H; exfalso; destruct H as [H | [H | []]]; vm_compute in H; congruence
               | intros H; discriminate H] ].
Qed.

Theorem ent_small_ledger : forall a b, E.mu (E.run ent_trace (E.start a b)) = 4.
Proof. intros. rewrite E.mu_conservation_trace. reflexivity. Qed.

Lemma ent_small_reduction : ent_reduction ent_repr (ent_complete 2) ent_prior ent_post.
Proof.
  exists ent_fibre. split; [| split].
  - intros x Hx. unfold ent_prior in Hx.
    repeat (destruct Hx as [<- | Hx];
      [first [ exists (E.start 2 0); split; [left; reflexivity |];
               split; [vm_compute; auto 10 | reflexivity]
             | exists (E.start 2 1); split; [right; left; reflexivity |];
               split; [vm_compute; auto 10 | reflexivity] ] |]).
    destruct Hx.
  - vm_compute. lia.
  - intros t Ht. destruct Ht as [<- | [<- | []]]; vm_compute; lia.
Qed.

Lemma ent_small_witness : exists w, In w ent_prior /\ ~ In w ent_post /\
  ent_distinguishes ent_obs w ent_post.
Proof.
  exists (E.start 0 0). split; [left; reflexivity |]. split.
  - intros [H | [H | []]]; revert H; ent_neq.
  - intros t [<- | [<- | []]]; ent_neq.
Qed.

Lemma ent_small_narrowing : ent_strict_sublist ent_post ent_prior.
Proof.
  split.
  - intros t [<- | [<- | []]]; vm_compute; auto 10.
  - destruct ent_small_witness as [w [H1 [H2 _]]]. exists w. auto.
Qed.

Lemma ent_small_certified : ent_certified earned_interface ent_s0 ent_trace ent_decode
  (ent_member ent_bools_eqb ent_obs ent_post).
Proof. split; vm_compute; reflexivity. Qed.

Lemma ent_small_realized : ent_depth (ent_complete 2) <= record_moves earned_interface ent_trace.
Proof. vm_compute. lia. Qed.

(* The worked member, all conclusions with the numbers filled in. *)
Theorem ent_small_instance :
  ent_strictly_stronger (ent_member ent_bools_eqb ent_obs ent_post)
                        (ent_member ent_bools_eqb ent_obs ent_prior) /\
  earned_chain earned_interface ent_s0 ent_trace /\
  Nat.log2_up (length ent_prior) - Nat.log2_up (length ent_post) = 2 /\
  record_moves earned_interface ent_trace = 4 /\
  E.mu (run earned_machine ent_trace ent_s0) - E.mu ent_s0 = 4 /\
  Nat.log2_up (length ent_prior) - Nat.log2_up (length ent_post)
    <= E.mu (run earned_machine ent_trace ent_s0) - E.mu ent_s0.
Proof.
  destruct (ent_representation earned_machine earned_interface E.state (list bool)
              ent_s0 ent_trace ent_decode ent_obs ent_repr ent_bools_eqb
              ent_prior ent_post (ent_complete 2) ent_earned_complete_with
              ent_bools_eqb_eq ent_small_narrowing ent_small_witness
              (E.start_clean 2 0) ent_small_certified ent_small_realized
              ltac:(simpl; lia) ent_small_reduction)
    as [C1 [C2 [_ [C4 [C5 _]]]]].
  split; [exact C1 |]. split; [exact C2 |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [vm_compute; reflexivity |].
  simpl in C5. simpl. lia.
Qed.

Definition ent_small_shortcut :
  ent_shortcut earned_interface E.state (list bool) ent_s0 ent_trace :=
  @Build_ent_shortcut earned_machine earned_interface E.state (list bool) ent_s0 ent_trace
    ent_decode ent_obs ent_repr ent_bools_eqb ent_prior ent_post (ent_complete 2)
    ent_bools_eqb_eq ent_small_narrowing ent_small_witness (E.start_clean 2 0)
    ent_small_certified ent_small_realized ltac:(simpl; lia) ent_small_reduction.

Theorem ent_small_lands :
  Nat.log2_up (length ent_prior) - Nat.log2_up (length ent_post)
    <= E.mu (run earned_machine ent_trace ent_s0) - E.mu ent_s0.
Proof.
  destruct (ent_every_shortcut_lands_here earned_machine earned_interface E.state (list bool)
              ent_s0 ent_trace ent_small_shortcut ent_earned_complete_with)
    as [_ [_ [H _]]].
  exact H.
Qed.

(* The questions floor on the member: the run asked two questions; asked of
   each of the eight rivals they leave classes of two (B is free); so
   3 - 1 = 2 index bits, at most the 2 CHECK moves, at most the 4 record
   moves, which are the ledger's rise. Here the floor is met exactly by the
   CHECK count. *)
Theorem ent_small_questions :
  ent_checked earned_interface ent_trace = ent_q /\
  Nat.log2_up (length ent_prior) - Nat.log2_up 2 = 2 /\
  Nat.log2_up (length ent_prior) - Nat.log2_up 2
    <= length (ent_checked earned_interface ent_trace) /\
  length (ent_checked earned_interface ent_trace) <= record_moves earned_interface ent_trace /\
  E.mu (run earned_machine ent_trace ent_s0) = E.mu ent_s0 + record_moves earned_interface ent_trace.
Proof.
  pose proof ent_earned_complete_with as [_ [_ [Htoll _]]].
  destruct (ent_questions_floor earned_machine earned_interface Htoll ent_s0 ent_trace
              ent_prior 2 ltac:(lia)) as [H1 [H2 H3]].
  - intros x Hx. unfold ent_prior in Hx.
    repeat (destruct Hx as [<- | Hx]; [vm_compute; lia |]). destruct Hx.
  - split; [reflexivity |]. split; [reflexivity |]. auto.
Qed.

(* ================================================================= *)
(* 6. The run generates the narrowing.                                *)
(* ================================================================= *)

(* Items 3 and 4 take the prior, the posterior and the tree as given.
   Here the posterior is read off the run: the candidates (start states)
   from which every check the run passed passes again when the run is
   replayed from them. Each passing check is one yes/no test, and the
   tests are applied in the order the run made them. *)

(* 6a. Narrowing a list by a sequence of yes/no tests, counted. *)

Section Narrowing.

Context {X : Type}.

Fixpoint ent_narrow (fs : list (X -> bool)) (L : list X) : list X :=
  match fs with [] => L | f :: fs' => ent_narrow fs' (filter f L) end.

(* The length of the standing list before and after each test. *)
Fixpoint ent_stages (fs : list (X -> bool)) (L : list X) : list (nat * nat) :=
  match fs with
  | [] => []
  | f :: fs' => (length L, length (filter f L)) :: ent_stages fs' (filter f L)
  end.

Definition ent_prod (l : list nat) : nat := fold_right Nat.mul 1 l.
Definition ent_sum (l : list nat) : nat := fold_right Nat.add 0 l.

(* Narrowing by the tests in turn is keeping the members that pass them
   all. *)
Lemma ent_narrow_filter : forall fs L,
  ent_narrow fs L = filter (fun x => forallb (fun f => f x) fs) L.
Proof.
  induction fs as [| f fs IH]; intros L; simpl.
  - induction L as [| x L IHL]; simpl; [reflexivity | f_equal; exact IHL].
  - rewrite IH. clear IH. induction L as [| x L IHL]; simpl; [reflexivity |].
    destruct (f x); simpl.
    + destruct (forallb (fun g => g x) fs); simpl; [f_equal |]; exact IHL.
    + exact IHL.
Qed.

Lemma ent_narrow_le : forall fs L, length (ent_narrow fs L) <= length L.
Proof.
  intros fs L. rewrite ent_narrow_filter.
  induction L as [| x L IH]; simpl; [lia |]. destruct (forallb _ fs); simpl; lia.
Qed.

(* The exact count: the prior's length times the product of the "after"
   lengths equals the posterior's length times the product of the
   "before" lengths. Taking base-two logarithms, the index bits lost,
   log2 |prior| - log2 |post|, are exactly the sum over the tests of
   log2 (before / after) whenever the posterior is not empty. *)
Theorem ent_stages_product : forall fs L,
  length L * ent_prod (map snd (ent_stages fs L))
    = length (ent_narrow fs L) * ent_prod (map fst (ent_stages fs L)).
Proof.
  induction fs as [| f fs IH]; intros L; simpl; [unfold ent_prod; simpl; lia |].
  unfold ent_prod in *. simpl. rewrite IH. ring.
Qed.

(* A drop covered by 2^s loses at most s index bits. *)
Lemma ent_bits_of_cover : forall a b s,
  a <= 2 ^ s * b -> Nat.log2_up a - Nat.log2_up b <= s.
Proof.
  intros a b s H. destruct b as [| b].
  - rewrite Nat.mul_0_r in H. assert (a = 0) by lia. subst a. simpl. lia.
  - pose proof (ent_cover_bits a (S b) (2 ^ s) ltac:(lia) H) as Hb.
    rewrite Nat.log2_up_pow2 in Hb by lia. exact Hb.
Qed.

(* If test i keeps at least a 2^-k_i share of the list standing before it,
   the prior is at most 2^(k_1 + ... + k_n) times the posterior. *)
Lemma ent_stages_cover : forall fs L ks,
  Forall2 (fun st k => fst st <= 2 ^ k * snd st) (ent_stages fs L) ks ->
  length L <= 2 ^ ent_sum ks * length (ent_narrow fs L).
Proof.
  induction fs as [| f fs IH]; intros L ks H; simpl in H.
  - inversion H; subst. simpl. lia.
  - inversion H as [| st k rest ks' Hk Hrest]; subst. simpl in Hk |- *.
    specialize (IH (filter f L) ks' Hrest).
    rewrite Nat.pow_add_r.
    assert (2 ^ k * length (filter f L)
            <= 2 ^ k * (2 ^ ent_sum ks' * length (ent_narrow fs (filter f L))))
      by (apply Nat.mul_le_mono_l; exact IH).
    rewrite <- Nat.mul_assoc. lia.
Qed.

(* Index bits at most the sum of the bits each test was allowed to take. *)
Theorem ent_stages_bits : forall fs L ks,
  Forall2 (fun st k => fst st <= 2 ^ k * snd st) (ent_stages fs L) ks ->
  Nat.log2_up (length L) - Nat.log2_up (length (ent_narrow fs L)) <= ent_sum ks.
Proof. intros fs L ks H. apply ent_bits_of_cover, ent_stages_cover, H. Qed.

(* The uniform form: if every test keeps at least a 2^-k share of the list
   standing before it, the index bits lost are at most k times the number
   of tests. *)
Theorem ent_stages_share_bits : forall fs L k,
  Forall (fun st => fst st <= 2 ^ k * snd st) (ent_stages fs L) ->
  Nat.log2_up (length L) - Nat.log2_up (length (ent_narrow fs L)) <= k * length fs.
Proof.
  intros fs L k H.
  assert (Hks : Forall2 (fun st k => fst st <= 2 ^ k * snd st) (ent_stages fs L)
                        (repeat k (length fs))).
  { revert L H. induction fs as [| f fs IH]; intros L H; simpl in *; [constructor |].
    inversion H; subst. constructor; [assumption | apply IH; assumption]. }
  pose proof (ent_stages_bits fs L _ Hks) as Hb.
  assert (Hs : forall n, ent_sum (repeat k n) = k * n)
    by (induction n; simpl; [lia | rewrite IHn; lia]).
  rewrite Hs in Hb. exact Hb.
Qed.

(* The rounded form with nothing assumed: the bits test i takes are
   log2 (before / after), both rounded up. *)
Definition ent_test_bits (st : nat * nat) : nat :=
  Nat.log2_up ((fst st + snd st - 1) / snd st).

Lemma ent_test_bits_cover : forall b a, 0 < a -> b <= 2 ^ ent_test_bits (b, a) * a.
Proof.
  intros b a Ha. unfold ent_test_bits. simpl.
  set (q := (b + a - 1) / a).
  assert (Hq : b <= a * q).
  { pose proof (Nat.div_mod (b + a - 1) a ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound (b + a - 1) a ltac:(lia)) as Hmb.
    unfold q. lia. }
  destruct q as [| q'] eqn:Eq.
  - lia.
  - assert (Hp : S q' <= 2 ^ Nat.log2_up (S q'))
      by (apply (proj2 (Nat.log2_up_le_pow2 (S q') (Nat.log2_up (S q')) ltac:(lia))); lia).
    assert (a * S q' <= a * 2 ^ Nat.log2_up (S q')) by (apply Nat.mul_le_mono_l; exact Hp).
    lia.
Qed.

Lemma ent_stages_after_pos : forall fs L,
  0 < length (ent_narrow fs L) -> Forall (fun st => 0 < snd st) (ent_stages fs L).
Proof.
  induction fs as [| f fs IH]; intros L H; simpl in *; [constructor |].
  constructor; [| apply IH, H].
  simpl. pose proof (ent_narrow_le fs (filter f L)). lia.
Qed.

(* Index bits at most the sum, over the tests, of log2 (before / after)
   rounded up, whenever the posterior is not empty. *)
Theorem ent_stages_round_bits : forall fs L,
  0 < length (ent_narrow fs L) ->
  Nat.log2_up (length L) - Nat.log2_up (length (ent_narrow fs L))
    <= ent_sum (map ent_test_bits (ent_stages fs L)).
Proof.
  intros fs L Hpos. apply ent_stages_bits.
  pose proof (ent_stages_after_pos fs L Hpos) as Hall.
  induction Hall as [| [b a] l Ha _ IH]; simpl; constructor; [| exact IH].
  apply ent_test_bits_cover, Ha.
Qed.

End Narrowing.

(* 6b. On a machine: the checks the run passed, as tests of candidates. *)

(* The checks the run passed, from state s with the moves done so far: for
   each CHECK move of claim c whose check passes at the state the run is in,
   the prefix before it and c. *)
Fixpoint ent_passes {M : machine} (I : thiele_interface M) (s : m_state M)
    (done tr : list (m_move M)) : list (list (m_move M) * ti_claim I) :=
  match tr with
  | [] => []
  | m :: rest =>
      let tail := ent_passes I (m_step M s m) (done ++ [m]) rest in
      match ti_kind I m with
      | KCheck c => if ti_check I s c then (done, c) :: tail else tail
      | _ => tail
      end
  end.

(* Each passing check, as a test of a candidate start x: replay the prefix
   from x and ask the same claim. *)
Definition ent_run_tests {M : machine} (I : thiele_interface M) (s0 : m_state M)
    (tr : list (m_move M)) : list (m_state M -> bool) :=
  map (fun pc x => ti_check I (run M (fst pc) x) (snd pc)) (ent_passes I s0 [] tr).

(* The posterior the run generates: the candidates consistent with every
   check the run passed. *)
Definition ent_run_posterior {M : machine} (I : thiele_interface M) (s0 : m_state M)
    (tr : list (m_move M)) (prior : list (m_state M)) : list (m_state M) :=
  ent_narrow (ent_run_tests I s0 tr) prior.

Lemma ent_passes_le_checked : forall M (I : thiele_interface M) tr s done,
  length (ent_passes I s done tr) <= length (ent_checked I tr).
Proof.
  intros M I tr. induction tr as [| m tr IH]; intros s done; simpl; [lia |].
  destruct (ti_kind I m); simpl; try apply IH.
  destruct (ti_check I s c); simpl; [apply le_n_S |]; [apply IH | ].
  pose proof (IH (m_step M s m) (done ++ [m])). lia.
Qed.

(* Each recorded check is a CHECK move of the run, at the recorded
   prefix, and it passed there. *)
Lemma ent_passes_sound : forall M (I : thiele_interface M) s0 tr s done,
  s = run M done s0 ->
  forall pc, In pc (ent_passes I s done tr) ->
    (exists m post, done ++ tr = fst pc ++ m :: post /\ ti_kind I m = KCheck (snd pc)) /\
    ti_check I (run M (fst pc) s0) (snd pc) = true.
Proof.
  intros M I s0 tr. induction tr as [| m tr IH]; intros s done Hs pc Hin; simpl in Hin;
    [destruct Hin |].
  assert (Hs' : m_step M s m = run M (done ++ [m]) s0)
    by (rewrite run_app, <- Hs; reflexivity).
  assert (Htail : In pc (ent_passes I (m_step M s m) (done ++ [m]) tr) ->
      (exists m' post, done ++ m :: tr = fst pc ++ m' :: post /\ ti_kind I m' = KCheck (snd pc)) /\
      ti_check I (run M (fst pc) s0) (snd pc) = true).
  { intro H. destruct (IH _ _ Hs' pc H) as [[m' [post [Heq Hk]]] Hc].
    split; [| exact Hc]. exists m', post.
    split; [rewrite <- Heq, <- app_assoc; reflexivity | exact Hk]. }
  destruct (ti_kind I m) eqn:Hk; try (apply Htail; exact Hin).
  destruct (ti_check I s c) eqn:Hc; [| apply Htail; exact Hin].
  destruct Hin as [<- | Hin]; [| apply Htail; exact Hin].
  simpl. split; [exists m, tr; split; [reflexivity | exact Hk] |].
  rewrite <- Hs. exact Hc.
Qed.

Lemma ent_forallb_false : forall {A : Type} (f : A -> bool) (l : list A),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f l. induction l as [| x l IH]; simpl; [discriminate |].
  destruct (f x) eqn:Hx; simpl; intro H.
  - destruct (IH H) as [y [Hy Hfy]]. exists y. auto.
  - exists x. auto.
Qed.

(* Structural entitlement with the narrowing generated by the run. On a
   Thiele-complete machine, take a clean start s0, a run tr from it that
   ends with the record up, and a prior list of candidate starts that
   contains s0. The posterior is the candidates from which every check the
   run passed passes again. Then:
   (1) the posterior is inside the prior and contains s0;
   (2) every candidate dropped fails, replayed, a CHECK the run made and
       passed;
   (3) the exact count: |prior| times the product of the "after" lengths
       equals |post| times the product of the "before" lengths, one pair
       per passing check;
   (4) if every passing check keeps at least a 2^-k share of the candidates
       standing before it, the index bits lost are at most k times the
       number of passing checks;
   (5) that number is at most the record moves of the run, which are the
       ledger's rise, so the index bits are at most k times the ledger's
       rise;
   (6) the run contains the earned chain, and the ledger rose by at
       least 3. *)
Theorem ent_run_entitlement :
  forall (M : machine) (I : thiele_interface M),
    thiele_complete_with I ->
    forall (s0 : m_state M) (tr : list (m_move M)) (prior : list (m_state M)) (k : nat),
    ti_clean I s0 ->
    m_record M (run M tr s0) = true ->
    In s0 prior ->
    Forall (fun st => fst st <= 2 ^ k * snd st) (ent_stages (ent_run_tests I s0 tr) prior) ->
    incl (ent_run_posterior I s0 tr prior) prior /\
    In s0 (ent_run_posterior I s0 tr prior) /\
    (forall x, In x prior -> ~ In x (ent_run_posterior I s0 tr prior) ->
       exists pre c m rest, tr = pre ++ m :: rest /\ ti_kind I m = KCheck c /\
         ti_check I (run M pre s0) c = true /\ ti_check I (run M pre x) c = false) /\
    length prior * ent_prod (map snd (ent_stages (ent_run_tests I s0 tr) prior))
      = length (ent_run_posterior I s0 tr prior)
          * ent_prod (map fst (ent_stages (ent_run_tests I s0 tr) prior)) /\
    Nat.log2_up (length prior) - Nat.log2_up (length (ent_run_posterior I s0 tr prior))
      <= k * length (ent_passes I s0 [] tr) /\
    length (ent_passes I s0 [] tr) <= record_moves I tr /\
    record_moves I tr = ti_ledger I (run M tr s0) - ti_ledger I s0 /\
    Nat.log2_up (length prior) - Nat.log2_up (length (ent_run_posterior I s0 tr prior))
      <= k * (ti_ledger I (run M tr s0) - ti_ledger I s0) /\
    earned_chain I s0 tr /\
    ti_ledger I s0 + 3 <= ti_ledger I (run M tr s0).
Proof.
  intros M I HC s0 tr prior k H0 H1 Hin Hshare.
  pose proof HC as [_ [[_ [Hchain _]] [Htoll _]]].
  pose proof (ent_passes_sound M I s0 tr s0 [] eq_refl) as Hsound.
  assert (Hpost : ent_run_posterior I s0 tr prior
                  = filter (fun x => forallb (fun f => f x) (ent_run_tests I s0 tr)) prior)
    by apply ent_narrow_filter.
  assert (Hlen : length (ent_run_tests I s0 tr) = length (ent_passes I s0 [] tr))
    by (unfold ent_run_tests; apply map_length).
  assert (Hbits := ent_stages_share_bits (ent_run_tests I s0 tr) prior k Hshare).
  change (ent_narrow (ent_run_tests I s0 tr) prior) with (ent_run_posterior I s0 tr prior)
    in Hbits.
  rewrite Hlen in Hbits.
  assert (Hle := ent_passes_le_checked M I tr s0 []).
  assert (Hck := ent_checked_le_record_moves M I tr).
  assert (Hrise := ent_ledger_rise M I Htoll tr s0).
  assert (Hprod := ent_stages_product (ent_run_tests I s0 tr) prior).
  change (ent_narrow (ent_run_tests I s0 tr) prior) with (ent_run_posterior I s0 tr prior)
    in Hprod.
  split; [intros x Hx; rewrite Hpost in Hx; apply filter_In in Hx; apply Hx |].
  split.
  { rewrite Hpost. apply filter_In. split; [exact Hin |]. apply forallb_forall.
    intros f Hf. unfold ent_run_tests in Hf. apply in_map_iff in Hf as [pc [<- Hpc]].
    apply (Hsound pc Hpc). }
  split.
  { intros x Hx Hout.
    assert (Hf : forallb (fun f => f x) (ent_run_tests I s0 tr) = false).
    { destruct (forallb (fun f => f x) (ent_run_tests I s0 tr)) eqn:E; [| reflexivity].
      exfalso. apply Hout. rewrite Hpost. apply filter_In. auto. }
    apply ent_forallb_false in Hf as [f [Hf Hfx]].
    unfold ent_run_tests in Hf. apply in_map_iff in Hf as [pc [<- Hpc]].
    destruct (Hsound pc Hpc) as [[m [post [Htr Hk]]] Hpass].
    exists (fst pc), (snd pc), m, post. auto. }
  split; [exact Hprod |].
  split; [exact Hbits |].
  split; [lia |].
  split; [exact Hrise |].
  split; [assert (k * length (ent_passes I s0 [] tr) <= k * record_moves I tr)
            by (apply Nat.mul_le_mono_l; lia); lia |].
  split; [apply Hchain; assumption |].
  destruct (certificate_costs_three M I HC s0 tr H0 H1) as [_ H3]. lia.
Qed.

(* The same with nothing assumed about shares: the index bits are at most
   the sum, over the run's passing checks, of log2 (before / after) rounded
   up. *)
Theorem ent_run_round_bits :
  forall (M : machine) (I : thiele_interface M) (s0 : m_state M)
         (tr : list (m_move M)) (prior : list (m_state M)),
    In s0 prior ->
    Nat.log2_up (length prior) - Nat.log2_up (length (ent_run_posterior I s0 tr prior))
      <= ent_sum (map ent_test_bits (ent_stages (ent_run_tests I s0 tr) prior)).
Proof.
  intros M I s0 tr prior Hin. apply ent_stages_round_bits.
  assert (Hs0 : In s0 (ent_run_posterior I s0 tr prior)).
  { unfold ent_run_posterior. rewrite ent_narrow_filter. apply filter_In.
    split; [exact Hin |]. apply forallb_forall.
    intros f Hf. unfold ent_run_tests in Hf. apply in_map_iff in Hf as [pc [<- Hpc]].
    apply (ent_passes_sound M I s0 tr s0 [] eq_refl pc Hpc). }
  unfold ent_run_posterior in Hs0.
  destruct (ent_narrow (ent_run_tests I s0 tr) prior); [destruct Hs0 | simpl; lia].
Qed.

(* 6c. The small machine. *)

(* The worked member of item 5, with the posterior generated by the run.
   The run passes two checks, "A is even" and "A >= 2"; replayed from the
   eight candidates they leave four, then two, the two starts with A = 2,
   which is ent_post. Each keeps half, so k = 1: 3 - 1 = 2 index bits, at
   most 1 times 2 passing checks, at most the 4 record moves, the ledger's
   rise. *)
Theorem ent_small_run_narrowing :
  ent_run_posterior earned_interface ent_s0 ent_trace ent_prior = ent_post /\
  ent_stages (ent_run_tests earned_interface ent_s0 ent_trace) ent_prior = [(8, 4); (4, 2)] /\
  length (ent_passes earned_interface ent_s0 [] ent_trace) = 2 /\
  Nat.log2_up (length ent_prior)
    - Nat.log2_up (length (ent_run_posterior earned_interface ent_s0 ent_trace ent_prior)) = 2 /\
  Nat.log2_up (length ent_prior)
    - Nat.log2_up (length (ent_run_posterior earned_interface ent_s0 ent_trace ent_prior))
    <= 1 * (E.mu (run earned_machine ent_trace ent_s0) - E.mu ent_s0).
Proof.
  assert (Hst : ent_stages (ent_run_tests earned_interface ent_s0 ent_trace) ent_prior
                = [(8, 4); (4, 2)]) by (vm_compute; reflexivity).
  destruct (ent_run_entitlement earned_machine earned_interface ent_earned_complete_with
              ent_s0 ent_trace ent_prior 1 (E.start_clean 2 0) ltac:(vm_compute; reflexivity)
              ltac:(simpl; auto 10) ltac:(rewrite Hst; repeat constructor; simpl; lia))
    as [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]].
  split; [vm_compute; reflexivity |]. split; [exact Hst |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  exact H.
Qed.

(* Why the share hypothesis is needed. Sixteen candidates, A in 0..15. The
   run CHECK "A >= 15", COMMIT, CERTIFY from A = 15 raises the record with
   3 record moves; its one passing check keeps 1 of 16, a 2^-4 share, so
   the run narrows 16 candidates to 1, 4 index bits, more than the 3 record
   moves. The bound with k = 4 holds (4 <= 4 * 1); with k = 1 it fails. *)
Definition ent_big_prior : list E.state := map (fun a => E.start a 0) (seq 0 16).

Definition ent_big_trace : list E.instr :=
  [E.CHECK (E.PGe 15) E.CA; E.COMMIT (E.PGe 15) E.CA; E.CERTIFY].

Theorem ent_share_needed :
  E.cert (run earned_machine ent_big_trace (E.start 15 0)) = true /\
  ent_run_posterior earned_interface (E.start 15 0) ent_big_trace ent_big_prior
    = [E.start 15 0] /\
  ent_stages (ent_run_tests earned_interface (E.start 15 0) ent_big_trace) ent_big_prior
    = [(16, 1)] /\
  record_moves earned_interface ent_big_trace = 3 /\
  Nat.log2_up (length ent_big_prior)
    - Nat.log2_up (length (ent_run_posterior earned_interface (E.start 15 0)
                             ent_big_trace ent_big_prior)) = 4 /\
  ~ (Nat.log2_up (length ent_big_prior)
       - Nat.log2_up (length (ent_run_posterior earned_interface (E.start 15 0)
                                ent_big_trace ent_big_prior))
     <= 1 * record_moves earned_interface ent_big_trace).
Proof.
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |]. split; [vm_compute; reflexivity |].
  split; [vm_compute; reflexivity |]. vm_compute. lia.
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions ent_leaves_le_pow2.
Print Assumptions ent_log2_leaves_le_depth.
Print Assumptions ent_narrowing_strengthens.
Print Assumptions ent_index_bits_le_depth.
Print Assumptions ent_cs_raising_step.
Print Assumptions ent_cs_count.
Print Assumptions ent_cs_entitlement.
Print Assumptions ent_two_observations.
Print Assumptions ent_exists_covering_tree.
Print Assumptions ent_complete_tree_bound.
Print Assumptions ent_representation.
Print Assumptions ent_every_shortcut_lands_here.
Print Assumptions ent_questions_floor.
Print Assumptions ent_earned_complete_with.
Print Assumptions ent_small_certifies_iff.
Print Assumptions ent_small_posterior_is_certified.
Print Assumptions ent_small_ledger.
Print Assumptions ent_small_instance.
Print Assumptions ent_small_shortcut.
Print Assumptions ent_small_lands.
Print Assumptions ent_small_questions.
Print Assumptions ent_narrow_filter.
Print Assumptions ent_stages_product.
Print Assumptions ent_stages_bits.
Print Assumptions ent_stages_share_bits.
Print Assumptions ent_stages_round_bits.
Print Assumptions ent_passes_sound.
Print Assumptions ent_run_entitlement.
Print Assumptions ent_run_round_bits.
Print Assumptions ent_small_run_narrowing.
Print Assumptions ent_share_needed.
