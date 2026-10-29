(** AxSmall: the small machine with a record that is a set of established
    claims.

    The small machine of EarnedGeneric.v keeps one bit: has anything been
    certified.  Here the record is the list of claims certified so far, a
    point of the free semilattice of finite sets of claims under inclusion
    (a preorder on lists; two lists are equivalent when they hold the same
    claims).  Every claim is a point, every finite set of claims is a point,
    and the order is inclusion, so the axis has infinitely many points as
    soon as the property language has infinitely many properties.

    The machine is the book's machine with one more coordinate.  CERTIFY adds
    the claim named by the commitment channel to the record.  Projecting the
    record to "is it nonempty" gives back the book's flag exactly
    ([small_flag_agrees]).

    Results (closed), for every property language with an exact checker and a
    property true of one value and false of another:

      small_axis_thiele_complete   the machine is Thiele-complete on the axis.
      small_flag_agrees            the book's flag is "the record is not below
                                   the floor", and the projection onto the
                                   book's machine commutes with every move.
      small_every_claim            for every claim (property, counter) the bare
                                   chain CHECK, COMMIT, CERTIFY puts that claim
                                   in the record exactly when the property holds
                                   of the counter at the start.
      small_record_is_join         a CERTIFY that moves the record makes it the
                                   join of the old record and the point of the
                                   committed claim.

    Over the property language with PGe n (the counter is at least n):

      over_nec_join                a reading of the record that over-claims
                                   meets every clause but the join: the join
                                   clause of the axis definition is needed.
      trap_nec_growth              a reading that forgets the record on a trap
                                   meets every clause but growth: the growth
                                   clause is needed.
      small_infinite_fibre         one window of the shadow, and for every n a
                                   state at it reached from a clean start whose
                                   record contains the claim "A >= n"; the
                                   records are pairwise inequivalent, so the
                                   fibre over that window holds infinitely many
                                   points of the axis. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxLatch AxComplete AxComplete2.
Require Minimal.ThieleComplete.
Require Minimal.EarnedGeneric.
Module T := Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module W := Minimal.ThieleCompleteWindow.

Ltac list_eq_tac := repeat first [rewrite <- app_assoc | progress simpl]; reflexivity.

(** The earned clause without its last conjunct (the join): used for the
    witness that the join clause is not implied by the others. *)
Definition axc_earned_exit_nolub {A P} {AM : amachine A P} (I : ax_interface AM)
    (s0 : am_state AM) (tr : list (am_move AM)) (m : am_move AM) : Prop :=
  exists pre c chk mid1 cmt mid2,
    tr = pre ++ chk :: mid1 ++ cmt :: mid2 /\
    axi_kind I chk = T.KCheck c /\ axi_kind I cmt = T.KCommit c /\
    axi_kind I m = T.KCertify /\
    axi_check I (am_run AM pre s0) c = true /\
    (forall t1 t2, mid1 = t1 ++ t2 ->
       axi_same I c (am_run AM pre s0) (am_run AM (pre ++ chk :: t1) s0)).

Definition axc_earned_nolub {A P} {AM : amachine A P} (I : ax_interface AM) : Prop :=
  (forall s, axi_clean I s -> am_rec AM s = axi_floor I) /\
  (forall s0 tr m, axi_clean I s0 -> ax_exit_step (am_run AM tr s0) m ->
     axc_earned_exit_nolub I s0 tr m) /\
  (forall s c, axi_check I s c = true -> axi_meaning I c s) /\
  (forall c s s', axi_same I c s s' -> axi_meaning I c s -> axi_meaning I c s').

(** The base clause without growth. *)
Definition axc_base_nogrowth {A P} {AM : amachine A P} (I : ax_interface AM) : Prop :=
  (forall i, axi_kind I (T.ub_compile (axi_base I) i) = T.KBase) /\
  (forall a b, axi_clean I (ax_load I a b)) /\
  (forall s m, axi_kind I m = T.KBase -> am_rec AM (am_step AM s m) = am_rec AM s).

Definition axc_growth {A P} {AM : amachine A P} : Prop :=
  forall s m, bp_le P (am_rec AM s) (am_rec AM (am_step AM s m)).

Section SmallAxis.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.
Hypothesis eval_iff : forall p v, eval p v = true <-> holds p v.

Local Notation st := (@G.state prop).
Local Notation instr := (@G.instr prop).

(** * Claims and the order of inclusion *)

Definition aclaim : Type := (prop * G.ctr)%type.

Definition aclaim_eqb (x y : aclaim) : bool :=
  prop_eqb (fst x) (fst y) && G.ctr_eqb (snd x) (snd y).

Lemma aclaim_eqb_eq : forall x y, aclaim_eqb x y = true <-> x = y.
Proof.
  intros [p c] [q d]. unfold aclaim_eqb. simpl. rewrite andb_true_iff, prop_eqb_eq. split.
  - intros [Hp Hc]. subst q. destruct c, d; simpl in Hc; try discriminate; reflexivity.
  - intro H. injection H as <- <-. split; [reflexivity | destruct c; reflexivity].
Qed.

Definition set_leb (xs ys : list aclaim) : bool :=
  forallb (fun x => existsb (aclaim_eqb x) ys) xs.

Lemma set_leb_spec : forall xs ys,
  set_leb xs ys = true <-> (forall x, In x xs -> In x ys).
Proof.
  intros xs ys. unfold set_leb. rewrite forallb_forall. split.
  - intros H x Hx. specialize (H x Hx). apply existsb_exists in H as [y [Hy He]].
    apply aclaim_eqb_eq in He. subst. exact Hy.
  - intros H x Hx. apply existsb_exists. exists x. split; [apply H; exact Hx |].
    apply aclaim_eqb_eq. reflexivity.
Qed.

Definition claims_pre : BPre (list aclaim).
Proof.
  refine {| bp_leb := set_leb |}.
  - intro x. apply set_leb_spec. intros y Hy. exact Hy.
  - intros x y z Hxy Hyz. apply set_leb_spec. intros a Ha.
    apply (proj1 (set_leb_spec y z) Hyz). apply (proj1 (set_leb_spec x y) Hxy). exact Ha.
Defined.

Lemma claims_le : forall xs ys, bp_le claims_pre xs ys <-> (forall x, In x xs -> In x ys).
Proof. intros xs ys. unfold bp_le. simpl. apply set_leb_spec. Qed.

Lemma claims_lub_cons : forall xs c, ax_is_lub claims_pre xs [c] (c :: xs).
Proof.
  intros xs c. unfold ax_is_lub. split; [| split].
  - apply claims_le. intros x Hx. right. exact Hx.
  - apply claims_le. intros x [<- | []]. left. reflexivity.
  - intros w Hxs Hc. apply claims_le. intros x [Hx | Hx].
    + subst x. apply (proj1 (claims_le [c] w) Hc). left. reflexivity.
    + apply (proj1 (claims_le xs w) Hxs). exact Hx.
Qed.

(** * The machine *)

Record astate : Type := mkas { as_core : st; as_set : list aclaim }.

Definition fact_claim (f : @G.fact prop) : aclaim := (G.f_prop f, G.f_ctr f).

Definition as_exec (s : astate) (i : instr) : astate :=
  mkas (G.exec prop_eqb eval (as_core s) i)
    (if G.fires (G.core_of (as_core s)) i
     then match G.chan (G.core_of (as_core s)) with
          | Some f => fact_claim f :: as_set s
          | None => as_set s
          end
     else as_set s).

Definition small_axm : amachine (list aclaim) claims_pre :=
  mk_am (list aclaim) claims_pre astate instr as_exec (@G.cost prop) as_set.

Lemma as_run_core : forall tr s,
  as_core (am_run small_axm tr s) = G.run prop_eqb eval tr (as_core s).
Proof.
  induction tr as [| i tr IH]; intro s; [reflexivity |].
  rewrite am_run_cons. simpl am_step. rewrite IH. reflexivity.
Qed.

(** What a step does to the record. *)
Lemma as_exec_cases : forall s i,
  (G.fires (G.core_of (as_core s)) i = false /\ as_set (as_exec s i) = as_set s) \/
  (i = G.CERTIFY /\ exists f, G.chan (G.core_of (as_core s)) = Some f /\
     G.certify_ok (G.core_of (as_core s)) = true /\
     G.fires (G.core_of (as_core s)) i = true /\
     as_set (as_exec s i) = fact_claim f :: as_set s).
Proof.
  intros s i. unfold as_exec. simpl.
  destruct i; simpl; try (left; split; reflexivity).
  destruct (G.certify_ok (G.core_of (as_core s))) eqn:Hok; [| left; split; reflexivity].
  destruct (G.chan (G.core_of (as_core s))) as [f |] eqn:Hf.
  - right. split; [reflexivity |]. exists f. repeat split; auto.
  - exfalso. unfold G.certify_ok in Hok. rewrite Hf in Hok. rewrite andb_false_r in Hok. discriminate.
Qed.

Lemma as_set_grows : forall s i, bp_le claims_pre (as_set s) (as_set (as_exec s i)).
Proof.
  intros s i. apply claims_le. intros x Hx.
  destruct (as_exec_cases s i) as [[_ H] | [_ [f [_ [_ [_ H]]]]]];
    [rewrite H; exact Hx | rewrite H; right; exact Hx].
Qed.

(** * The universal base and the interface *)

Definition sm_ub : T.universal_base (am_bare small_axm) :=
  T.mk_ub (am_bare small_axm) (fun s => T.generic_window (as_core s))
    (fun s => G.err (G.core_of (as_core s)) = false)
    (@T.generic_compile prop) (fun a b => mkas (G.start a b) [])
    (fun a b => eq_refl) (fun a b => eq_refl)
    (fun s i Hl => T.generic_sim prop_eqb eval (as_core s) i Hl).

Definition sm_ai : ax_interface small_axm :=
  mk_axi (list aclaim) claims_pre small_axm sm_ub aclaim (@T.generic_kind prop)
    (fun pc s => holds (fst pc) (G.val (G.core_of (as_core s)) (snd pc)))
    (fun s pc => G.check_ok eval (G.core_of (as_core s)) (fst pc) (snd pc))
    (fun pc s t => G.ver (G.core_of (as_core s)) (snd pc) = G.ver (G.core_of (as_core t)) (snd pc) /\
                   G.val (G.core_of (as_core s)) (snd pc) = G.val (G.core_of (as_core t)) (snd pc))
    (fun s => G.clean_start (as_core s) /\ as_set s = [])
    (fun s => G.mu (as_core s)) [] (fun c => [c]).

Lemma sm_base : axc_base sm_ai.
Proof.
  split; [| split; [| split]].
  - intros [[|] | [|] j]; reflexivity.
  - intros a b. split; [apply G.generic_start_clean | reflexivity].
  - intros s m Hk. simpl in Hk. destruct (as_exec_cases s m) as [[_ H] | [Hm _]].
    + exact H.
    + subst m. discriminate.
  - intros s m. apply as_set_grows.
Qed.

(** * The earned clause *)

Lemma sm_earned_exit : forall s0 tr m,
  axi_clean sm_ai s0 -> ax_exit_step (am_run small_axm tr s0) m ->
  axc_earned_exit sm_ai s0 tr m.
Proof.
  intros s0 tr m [H0 Hset0] Hexit.
  set (s := am_run small_axm tr s0) in *.
  destruct (as_exec_cases s m) as [[_ Hsame] | [Hm [f [Hf [Hok [_ Hnew]]]]]].
  - exfalso. apply Hexit.
    change (bp_le claims_pre (as_set (as_exec s m)) (as_set s)).
    rewrite Hsame. apply bp_le_refl.
  - subst m. pose proof H0 as [_ [Hch Hc0]].
    assert (Hcore : as_core s = G.run prop_eqb eval tr (as_core s0)) by apply as_run_core.
    assert (Hf' : G.chan (G.core_of (G.run prop_eqb eval tr (as_core s0))) = Some f)
      by (rewrite <- Hcore; exact Hf).
    destruct (G.generic_chan_origin prop_eqb eval (as_core s0) tr f Hch Hf')
      as [preC [p [c [mid2 [HpreC [Hcm Hfeq]]]]]].
    destruct (G.generic_earned_commitment_provenance prop_eqb prop_eqb_eq eval
                (as_core s0) preC p c H0 Hcm)
      as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
    assert (Hlist : pre1 ++ G.CHECK p c :: mid1 ++ G.COMMIT p c :: mid2 = tr)
      by (rewrite HpreC, Hpre1; list_eq_tac).
    exists pre1, (p, c), (G.CHECK p c), mid1, (G.COMMIT p c), mid2.
    split; [symmetry; exact Hlist |].
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split.
    { simpl. rewrite as_run_core. exact Hck. }
    split.
    { intros t1 t2 Hm. simpl. rewrite !as_run_core.
      replace (pre1 ++ G.CHECK p c :: t1) with ((pre1 ++ [G.CHECK p c]) ++ t1)
        by (rewrite <- app_assoc; reflexivity).
      rewrite G.generic_run_app.
      destruct (T.generic_untouched_prefix prop_eqb eval _ _ _ Hun t1 t2 Hm) as [Hv Hw].
      rewrite Hv, Hw, G.generic_run_snoc.
      change (G.core_of (G.exec prop_eqb eval (G.run prop_eqb eval pre1 (as_core s0)) (G.CHECK p c)))
        with (G.cexec prop_eqb eval (G.core_of (G.run prop_eqb eval pre1 (as_core s0))) (G.CHECK p c)).
      rewrite G.generic_ver_check, G.generic_val_check.
      split; reflexivity. }
    change (ax_is_lub claims_pre (as_set s) [(p, c)] (as_set (as_exec s G.CERTIFY))).
    rewrite Hnew, Hfeq. unfold fact_claim, G.claim. simpl.
    apply claims_lub_cons.
Qed.

Lemma sm_earned : axc_earned sm_ai.
Proof.
  split.
  - intros s [_ H]. exact H.
  - split; [| split].
    + exact sm_earned_exit.
    + intros s [p c] H. simpl in *. unfold G.check_ok in H.
      apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
      apply eval_iff, H.
    + intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
Qed.

Lemma sm_toll : axc_toll sm_ai.
Proof.
  split.
  - intros []; reflexivity.
  - intros s m. reflexivity.
Qed.


Definition sm_chain (p : prop) (c : G.ctr) : list instr := [G.CHECK p c; G.COMMIT p c; G.CERTIFY].
Definition sm_load (a b : nat) : astate := mkas (G.start a b) [].

Lemma sm_chain_set : forall p c a b,
  as_set (am_run small_axm (sm_chain p c) (sm_load a b)) =
  if eval p (@G.val prop (@G.start_core prop a b) c) then [(p, c)] else [].
Proof.
  intros p c a b. destruct (eval p (@G.val prop (@G.start_core prop a b) c)) eqn:E.
  - assert (Hck : G.check_ok eval (@G.start_core prop a b) p c = true)
      by (unfold G.check_ok; simpl; rewrite E; reflexivity).
    assert (H1 : G.cexec prop_eqb eval (@G.start_core prop a b) (G.CHECK p c)
                 = G.record_fact (@G.start_core prop a b) (G.claim (@G.start_core prop a b) p c))
      by (unfold G.cexec; simpl; rewrite Hck; reflexivity).
    assert (Hcm : G.commit_ok prop_eqb (G.record_fact (@G.start_core prop a b)
                    (G.claim (@G.start_core prop a b) p c)) p c = true).
    { apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq). split; [reflexivity |]. left. destruct c; reflexivity. }
    assert (H2 : G.cexec prop_eqb eval (G.record_fact (@G.start_core prop a b)
                    (G.claim (@G.start_core prop a b) p c)) (G.COMMIT p c)
                 = G.commit_to (G.record_fact (@G.start_core prop a b)
                    (G.claim (@G.start_core prop a b) p c))
                    (G.claim (G.record_fact (@G.start_core prop a b)
                    (G.claim (@G.start_core prop a b) p c)) p c)).
    { unfold G.cexec. simpl. rewrite Hcm. reflexivity. }
    unfold sm_chain, am_run. simpl. unfold as_exec. simpl.
    rewrite H1, H2. simpl. reflexivity.
  - assert (Hck : G.check_ok eval (@G.start_core prop a b) p c = false)
      by (unfold G.check_ok; simpl; rewrite E; reflexivity).
    assert (H1 : G.cexec prop_eqb eval (@G.start_core prop a b) (G.CHECK p c)
                 = G.trap (@G.start_core prop a b))
      by (unfold G.cexec; simpl; rewrite Hck; reflexivity).
    unfold sm_chain, am_run. simpl. unfold as_exec. simpl.
    rewrite H1. simpl. reflexivity.
Qed.


Lemma sm_chain_err : forall p c a b,
  eval p (@G.val prop (@G.start_core prop a b) c) = true ->
  G.err (G.core_of (as_core (am_run small_axm (sm_chain p c) (sm_load a b)))) = false.
Proof.
  intros p c a b E.
  assert (Hck : G.check_ok eval (@G.start_core prop a b) p c = true)
    by (unfold G.check_ok; simpl; rewrite E; reflexivity).
  assert (H1 : G.cexec prop_eqb eval (@G.start_core prop a b) (G.CHECK p c)
               = G.record_fact (@G.start_core prop a b) (G.claim (@G.start_core prop a b) p c))
    by (unfold G.cexec; simpl; rewrite Hck; reflexivity).
  assert (Hcm : G.commit_ok prop_eqb (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) p c = true).
  { apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq). split; [reflexivity |]. left. destruct c; reflexivity. }
  assert (H2 : G.cexec prop_eqb eval (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) (G.COMMIT p c)
               = G.commit_to (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c))
                  (G.claim (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) p c)).
  { unfold G.cexec. simpl. rewrite Hcm. reflexivity. }
  unfold sm_chain, am_run. simpl. unfold as_exec. simpl.
  rewrite H1, H2. simpl. reflexivity.
Qed.

(** Every claim is a point of the axis: the bare chain establishes it exactly
    when the property holds of the counter at the start. *)
Theorem small_every_claim : forall p c a b,
  bp_le claims_pre [(p, c)] (as_set (am_run small_axm (sm_chain p c) (sm_load a b)))
  <-> holds p (@G.val prop (@G.start_core prop a b) c).
Proof.
  intros p c a b. rewrite sm_chain_set. rewrite <- (eval_iff p).
  destruct (eval p (@G.val prop (@G.start_core prop a b) c)) eqn:E.
  - split; [intros _; reflexivity |]. intros _. apply claims_le.
    intros x [<- | []]. left. reflexivity.
  - split; [| intro H; discriminate H]. intro H.
    pose proof (proj1 (claims_le _ _) H (p, c) (or_introl eq_refl)) as H'. destruct H'.
Qed.

Lemma sm_nonvac : (exists p v w, holds p v /\ ~ holds p w) -> axc_nonvac sm_ai.
Proof.
  intros [p [v [w [Hv Hw]]]].
  exists (p, G.CA), (G.CHECK p G.CA), (G.COMMIT p G.CA), G.CERTIFY.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split.
  - intros a b. exact (small_every_claim p G.CA a b).
  - split; [exists v, 0; exact Hv | exists w, 0; exact Hw].
Qed.

(** The machine is Thiele-complete on the axis. *)
Theorem small_axis_thiele_complete :
  (exists p v w, holds p v /\ ~ holds p w) -> ax_tc_with sm_ai.
Proof.
  intro H. split; [exact sm_base | split; [exact sm_earned | split; [exact sm_toll | exact (sm_nonvac H)]]].
Qed.

(** A move that takes the record out of the down-set makes it the join of the
    old record and the point of the committed claim. *)
Theorem small_record_is_join : forall s0 tr m,
  axi_clean sm_ai s0 -> ax_exit_step (am_run small_axm tr s0) m ->
  exists c, ax_is_lub claims_pre (as_set (am_run small_axm tr s0)) [c]
              (as_set (am_step small_axm (am_run small_axm tr s0) m)).
Proof.
  intros s0 tr m Hc Hex.
  destruct (sm_earned_exit s0 tr m Hc Hex)
    as [pre [c [chk [mid1 [cmt [mid2 [_ [_ [_ [_ [_ [_ Hlub]]]]]]]]]]]].
  exists c. exact Hlub.
Qed.

(** The book's flag is the record having left the floor. *)
Lemma sm_flag_inv : forall tr a b,
  G.cert (as_core (am_run small_axm tr (sm_load a b))) = true <->
  as_set (am_run small_axm tr (sm_load a b)) <> [].
Proof.
  intros tr a b. induction tr as [| i tr IH] using rev_ind.
  - rewrite am_run_nil. simpl. split; [discriminate | intro H; exfalso; apply H; reflexivity].
  - rewrite am_run_snoc. set (s := am_run small_axm tr (sm_load a b)) in *.
    destruct (as_exec_cases s i) as [[Hf Hs] | [Hi [f [Hch [Hok [Hf Hnew]]]]]].
    + change (G.cert (G.exec prop_eqb eval (as_core s) i) = true <-> as_set (as_exec s i) <> []).
      rewrite Hs. simpl. rewrite Hf, orb_false_r. exact IH.
    + subst i. change (G.cert (G.exec prop_eqb eval (as_core s) G.CERTIFY) = true <->
                       as_set (as_exec s G.CERTIFY) <> []).
      rewrite Hnew. simpl. rewrite Hok, orb_true_r.
      split; [intros _; discriminate | intros _; reflexivity].
Qed.

Theorem small_flag_agrees : forall tr a b,
  G.cert (as_core (am_run small_axm tr (sm_load a b))) = true <->
  ~ bp_le claims_pre (as_set (am_run small_axm tr (sm_load a b))) [].
Proof.
  intros tr a b. rewrite sm_flag_inv. split.
  - intros H Hle. apply H. destruct (as_set (am_run small_axm tr (sm_load a b))) as [| x xs];
      [reflexivity |].
    pose proof (proj1 (claims_le _ _) Hle x (or_introl eq_refl)) as H'. destruct H'.
  - intros H Hz. apply H. rewrite Hz. apply bp_le_refl.
Qed.

(** The projection to the book's machine commutes with every move: the core
    of a step of the axis machine is the book's step of the core. *)
Theorem small_projection_commutes : forall s i,
  as_core (as_exec s i) = G.exec prop_eqb eval (as_core s) i.
Proof. reflexivity. Qed.


(** ** An infinite fibre *)

Variable pge : nat -> prop.
Hypothesis pge_holds : forall n v, n <= v -> holds (pge n) v.
Hypothesis pge_inj : forall n m, pge n = pge m -> n = m.

(** Over any window of the shadow there are, for every n, states reached from
    a clean start whose record is exactly the single claim "A >= n"; two of
    them are inequivalent points of the axis unless n = m.  The fibre over one
    classical state holds infinitely many points. *)
Theorem small_infinite_fibre :
  (exists p v w, holds p v /\ ~ holds p w) ->
  forall W0 : T.cm_conf,
    (forall n, exists s : astate,
       T.ub_window sm_ub s = W0 /\
       (exists tr, s = am_run small_axm tr (sm_load n 0)) /\
       as_set s = [(pge n, G.CA)]) /\
    (forall n m, bp_le claims_pre [(pge n, G.CA)] [(pge m, G.CA)] -> n = m).
Proof.
  intros H W0. pose proof (small_axis_thiele_complete H) as HC.
  destruct W0 as [pc0 [x0 y0]]. split.
  - intro n.
    assert (Hev : eval (pge n) (@G.val prop (@G.start_core prop n 0) G.CA) = true)
      by (apply eval_iff; apply pge_holds; simpl; lia).
    set (cn := am_run small_axm (sm_chain (pge n) G.CA) (sm_load n 0)).
    assert (Hcn : as_set cn = [(pge n, G.CA)])
      by (unfold cn; rewrite sm_chain_set, Hev; reflexivity).
    assert (Hlive : T.ub_live sm_ub cn) by exact (sm_chain_err (pge n) G.CA n 0 Hev).
    destruct (W.cm_reach (T.ub_window sm_ub cn) pc0 x0 y0) as [is His].
    destruct (ax_tc_conservative sm_ai HC is cn Hlive) as [Hw [_ [Hr _]]].
    exists (am_run small_axm (map (T.ub_compile sm_ub) is) cn). split; [| split].
    + exact (eq_trans Hw His).
    + exists (sm_chain (pge n) G.CA ++ map (T.ub_compile sm_ub) is).
      unfold cn. rewrite am_run_app. reflexivity.
    + exact (eq_trans Hr Hcn).
  - intros n m Hle.
    pose proof (proj1 (claims_le _ _) Hle (pge n, G.CA) (or_introl eq_refl)) as Hin.
    destruct Hin as [Heq | []]. injection Heq as Hp. apply pge_inj. symmetry. exact Hp.
Qed.


(** ** Two readings of the same machine, each breaking one axis clause *)

(** The records below are read off the same states and moves as the machine
    above; only the reading of the record changes.  The first reading
    over-claims: it holds, with every established claim, the same claim about
    the other counter.  The second forgets the record when the machine traps. *)

Definition flip_ctr (c : G.ctr) : G.ctr := match c with G.CA => G.CB | G.CB => G.CA end.
Definition flip_claim (x : aclaim) : aclaim := (fst x, flip_ctr (snd x)).
Definition over_rec (s : astate) : list aclaim := as_set s ++ map flip_claim (as_set s).

Definition over_axm : amachine (list aclaim) claims_pre :=
  mk_am (list aclaim) claims_pre astate instr as_exec (@G.cost prop) over_rec.

Definition over_ai : ax_interface over_axm :=
  mk_axi (list aclaim) claims_pre over_axm sm_ub aclaim (@T.generic_kind prop)
    (fun pc s => holds (fst pc) (G.val (G.core_of (as_core s)) (snd pc)))
    (fun s pc => G.check_ok eval (G.core_of (as_core s)) (fst pc) (snd pc))
    (fun pc s t => G.ver (G.core_of (as_core s)) (snd pc) = G.ver (G.core_of (as_core t)) (snd pc) /\
                   G.val (G.core_of (as_core s)) (snd pc) = G.val (G.core_of (as_core t)) (snd pc))
    (fun s => G.clean_start (as_core s) /\ as_set s = [])
    (fun s => G.mu (as_core s)) [] (fun c => [c]).

Lemma over_mono : forall xs ys, bp_le claims_pre xs ys ->
  bp_le claims_pre (xs ++ map flip_claim xs) (ys ++ map flip_claim ys).
Proof.
  intros xs ys H. apply claims_le. intros x Hx.
  apply in_app_or in Hx as [Hx | Hx]; apply in_or_app.
  - left. exact (proj1 (claims_le xs ys) H x Hx).
  - right. apply in_map_iff in Hx as [y [<- Hy]]. apply in_map.
    exact (proj1 (claims_le xs ys) H y Hy).
Qed.

Lemma over_exit_set_exit : forall s m,
  ax_exit_step (AM := over_axm) s m -> ax_exit_step (AM := small_axm) s m.
Proof.
  intros s m Hex Hle. apply Hex. exact (over_mono _ _ Hle).
Qed.

Lemma as_set_nonfire : forall s i, i <> G.CERTIFY -> as_set (as_exec s i) = as_set s.
Proof.
  intros s i Hi. destruct (as_exec_cases s i) as [[_ H] | [Hc _]]; [exact H | contradiction].
Qed.

(** The join clause is needed: a CERTIFY that over-claims is earned in every
    other respect. *)
Theorem over_nec_join :
  (exists p v w, holds p v /\ ~ holds p w) ->
  axc_base over_ai /\ axc_toll over_ai /\ axc_nonvac over_ai /\
  axc_earned_nolub over_ai /\ ~ axc_earned over_ai.
Proof.
  intros [p [v [w [Hv Hw]]]].
  destruct sm_base as [H1 [H2 [H3 H4]]].
  assert (Hearned := sm_earned).
  destruct Hearned as [Hcl [Hex [Hs Hr]]].
  assert (Hbase : axc_base over_ai).
  { split; [exact H1 |]. split; [exact H2 |]. split.
    - intros s m Hk. assert (H3' : as_set (as_exec s m) = as_set s) by exact (H3 s m Hk).
      change (over_rec (as_exec s m) = over_rec s). unfold over_rec. rewrite H3'. reflexivity.
    - intros s m. exact (over_mono _ _ (H4 s m)). }
  refine (conj Hbase (conj sm_toll (conj _ (conj _ _)))).
  - exists (p, G.CA), (G.CHECK p G.CA), (G.COMMIT p G.CA), G.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split.
    + intros a b. change (bp_le claims_pre [(p, G.CA)]
        (over_rec (am_run over_axm [G.CHECK p G.CA; G.COMMIT p G.CA; G.CERTIFY] (sm_load a b)))
        <-> holds p (@G.val prop (@G.start_core prop a b) G.CA)).
      assert (Hrun : am_run over_axm [G.CHECK p G.CA; G.COMMIT p G.CA; G.CERTIFY] (sm_load a b)
                     = am_run small_axm (sm_chain p G.CA) (sm_load a b)) by reflexivity.
      rewrite Hrun. unfold over_rec. rewrite sm_chain_set. rewrite <- (eval_iff p).
      destruct (eval p (@G.val prop (@G.start_core prop a b) G.CA)) eqn:E.
      * split; [intros _; reflexivity |]. intros _. apply claims_le. intros x [<- | []].
        apply in_or_app. left. left. reflexivity.
      * split; [| intro Hd; discriminate Hd]. intro Hle.
        pose proof (proj1 (claims_le _ _) Hle (p, G.CA) (or_introl eq_refl)) as Hin. destruct Hin.
    + split; [exists v, 0; exact Hv | exists w, 0; exact Hw].
  - split; [intros s [_ Hz]; change (over_rec s = []); unfold over_rec; rewrite Hz; reflexivity |].
    split; [| split; [exact Hs | exact Hr]].
    intros s0 tr m Hc Hexit.
    pose proof (sm_earned_exit s0 tr m Hc (over_exit_set_exit _ _ Hexit))
      as [pre [c [chk [mid1 [cmt [mid2 [Ht [Hk1 [Hk2 [Hk3 [Hck [Hsame _]]]]]]]]]]]].
    exists pre, c, chk, mid1, cmt, mid2.
    split; [exact Ht | split; [exact Hk1 | split; [exact Hk2 | split; [exact Hk3 | split; [exact Hck | exact Hsame]]]]].
  - intros [_ [Hexit _]].
    set (s0 := sm_load v 0).
    set (tr := [G.CHECK p G.CA; G.COMMIT p G.CA]).
    assert (Hc0 : axi_clean over_ai s0) by (apply H2).
    assert (Hcur : as_set (am_run small_axm tr s0) = []).
    { change (as_set (as_exec (as_exec s0 (G.CHECK p G.CA)) (G.COMMIT p G.CA)) = []).
      rewrite (as_set_nonfire _ (G.COMMIT p G.CA)) by discriminate.
      rewrite (as_set_nonfire _ (G.CHECK p G.CA)) by discriminate. reflexivity. }
    assert (Hnext : as_set (am_step small_axm (am_run small_axm tr s0) G.CERTIFY) = [(p, G.CA)]).
    { assert (Hev : eval p (@G.val prop (@G.start_core prop v 0) G.CA) = true)
        by (apply eval_iff; exact Hv).
      pose proof (sm_chain_set p G.CA v 0) as Hch. rewrite Hev in Hch.
      exact Hch. }
    assert (Hcur' : over_rec (am_run over_axm tr s0) = []).
    { change (as_set (am_run small_axm tr s0) ++ map flip_claim (as_set (am_run small_axm tr s0)) = []).
      rewrite Hcur. reflexivity. }
    assert (Hnext' : over_rec (am_step over_axm (am_run over_axm tr s0) G.CERTIFY)
                     = [(p, G.CA); (p, G.CB)]).
    { change (as_set (am_step small_axm (am_run small_axm tr s0) G.CERTIFY)
              ++ map flip_claim (as_set (am_step small_axm (am_run small_axm tr s0) G.CERTIFY))
              = [(p, G.CA); (p, G.CB)]).
      rewrite Hnext. reflexivity. }
    assert (Hx : ax_exit_step (AM := over_axm) (am_run over_axm tr s0) G.CERTIFY).
    { intro Hle.
      change (bp_le claims_pre (over_rec (am_step over_axm (am_run over_axm tr s0) G.CERTIFY))
                (over_rec (am_run over_axm tr s0))) in Hle.
      rewrite Hnext', Hcur' in Hle.
      pose proof (proj1 (claims_le _ _) Hle (p, G.CA) (or_introl eq_refl)) as Hin.
      destruct Hin. }
    destruct (Hexit s0 tr G.CERTIFY Hc0 Hx)
      as [pre [c [chk [mid1 [cmt [mid2 [_ [_ [_ [_ [_ [_ Hlub]]]]]]]]]]]].
    change (ax_is_lub claims_pre (over_rec (am_run over_axm tr s0)) [c]
              (over_rec (am_step over_axm (am_run over_axm tr s0) G.CERTIFY))) in Hlub.
    rewrite Hnext', Hcur' in Hlub.
    destruct Hlub as [_ [_ Hwl]].
    assert (Hw' := Hwl [c] (proj2 (claims_le [] [c]) (fun x Hx => False_ind _ Hx))
                      (bp_le_refl claims_pre [c])).
    pose proof (proj1 (claims_le _ _) Hw' (p, G.CA) (or_introl eq_refl)) as Ha.
    pose proof (proj1 (claims_le _ _) Hw' (p, G.CB) (or_intror (or_introl eq_refl))) as Hb.
    destruct Ha as [Ha | []]. destruct Hb as [Hb | []].
    rewrite Ha in Hb. discriminate (f_equal snd Hb).
Qed.

(** The second reading forgets the record when the machine traps. *)

Definition trap_rec (s : astate) : list aclaim :=
  if G.err (G.core_of (as_core s)) then [] else as_set s.

Definition trap_axm : amachine (list aclaim) claims_pre :=
  mk_am (list aclaim) claims_pre astate instr as_exec (@G.cost prop) trap_rec.

Definition trap_ai : ax_interface trap_axm :=
  mk_axi (list aclaim) claims_pre trap_axm sm_ub aclaim (@T.generic_kind prop)
    (fun pc s => holds (fst pc) (G.val (G.core_of (as_core s)) (snd pc)))
    (fun s pc => G.check_ok eval (G.core_of (as_core s)) (fst pc) (snd pc))
    (fun pc s t => G.ver (G.core_of (as_core s)) (snd pc) = G.ver (G.core_of (as_core t)) (snd pc) /\
                   G.val (G.core_of (as_core s)) (snd pc) = G.val (G.core_of (as_core t)) (snd pc))
    (fun s => G.clean_start (as_core s) /\ as_set s = [])
    (fun s => G.mu (as_core s)) [] (fun c => [c]).

Lemma err_stays : forall s i, G.err (G.core_of (as_core s)) = true ->
  G.err (G.core_of (as_core (as_exec s i))) = true.
Proof.
  intros s i H. unfold as_exec. simpl. unfold G.cexec. rewrite H. exact H.
Qed.

Lemma err_base : forall s i, @T.generic_kind prop i = T.KBase ->
  G.err (G.core_of (as_core (as_exec s i))) = G.err (G.core_of (as_core s)).
Proof.
  intros s i Hk. unfold as_exec. simpl. unfold G.cexec.
  destruct (G.err (G.core_of (as_core s))) eqn:He; [simpl; exact He |].
  destruct i as [c | c j | | p0 c | p0 c |]; simpl in Hk; try discriminate; simpl.
  - destruct c; exact He.
  - destruct (G.val (G.core_of (as_core s)) c); destruct c; exact He.
  - exact He.
Qed.

Lemma trap_rec_ok : forall s, G.err (G.core_of (as_core s)) = false -> trap_rec s = as_set s.
Proof. intros s H. unfold trap_rec. rewrite H. reflexivity. Qed.

Lemma trap_rec_err : forall s, G.err (G.core_of (as_core s)) = true -> trap_rec s = [].
Proof. intros s H. unfold trap_rec. rewrite H. reflexivity. Qed.

Lemma sm_chain_trap : forall p c a b,
  eval p (@G.val prop (@G.start_core prop a b) c) = false ->
  G.err (G.core_of (as_core (am_run small_axm (sm_chain p c) (sm_load a b)))) = true.
Proof.
  intros p c a b E.
  assert (Hck : G.check_ok eval (@G.start_core prop a b) p c = false)
    by (unfold G.check_ok; simpl; rewrite E; reflexivity).
  assert (H1 : G.cexec prop_eqb eval (@G.start_core prop a b) (G.CHECK p c)
               = G.trap (@G.start_core prop a b))
    by (unfold G.cexec; simpl; rewrite Hck; reflexivity).
  unfold sm_chain, am_run. simpl. unfold as_exec. simpl.
  rewrite H1. simpl. reflexivity.
Qed.

(** The state after the chain on a true claim: its table holds the one fact. *)
Lemma sm_chain_facts : forall p c a b,
  eval p (@G.val prop (@G.start_core prop a b) c) = true ->
  G.facts (G.core_of (as_core (am_run small_axm (sm_chain p c) (sm_load a b))))
  = [G.claim (@G.start_core prop a b) p c].
Proof.
  intros p c a b E.
  assert (Hck : G.check_ok eval (@G.start_core prop a b) p c = true)
    by (unfold G.check_ok; simpl; rewrite E; reflexivity).
  assert (H1 : G.cexec prop_eqb eval (@G.start_core prop a b) (G.CHECK p c)
               = G.record_fact (@G.start_core prop a b) (G.claim (@G.start_core prop a b) p c))
    by (unfold G.cexec; simpl; rewrite Hck; reflexivity).
  assert (Hcm : G.commit_ok prop_eqb (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) p c = true).
  { apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq). split; [reflexivity |]. left. destruct c; reflexivity. }
  assert (H2 : G.cexec prop_eqb eval (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) (G.COMMIT p c)
               = G.commit_to (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c))
                  (G.claim (G.record_fact (@G.start_core prop a b)
                  (G.claim (@G.start_core prop a b) p c)) p c)).
  { unfold G.cexec. simpl. rewrite Hcm. reflexivity. }
  unfold sm_chain, am_run. simpl. unfold as_exec. simpl.
  rewrite H1, H2. simpl. reflexivity.
Qed.

(** The growth clause is needed: a machine that loses its record on a trap
    meets the other clauses. *)
Theorem trap_nec_growth :
  (exists p v w, holds p v /\ ~ holds p w) ->
  axc_base_nogrowth trap_ai /\ axc_toll trap_ai /\ axc_nonvac trap_ai /\
  axc_earned trap_ai /\ ~ axc_growth (AM := trap_axm).
Proof.
  intros [p [v [w [Hv Hw]]]].
  destruct sm_base as [H1 [H2 [H3 H4]]].
  destruct sm_earned as [Hcl [Hex [Hs Hr]]].
  refine (conj _ (conj sm_toll (conj _ (conj _ _)))).
  - split; [exact H1 |]. split; [exact H2 |].
    intros s m Hk.
    assert (H3' : as_set (as_exec s m) = as_set s) by exact (H3 s m Hk).
    change (trap_rec (as_exec s m) = trap_rec s). unfold trap_rec.
    rewrite (err_base s m Hk), H3'. reflexivity.
  - exists (p, G.CA), (G.CHECK p G.CA), (G.COMMIT p G.CA), G.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split.
    + intros a b. change (bp_le claims_pre [(p, G.CA)]
        (trap_rec (am_run small_axm (sm_chain p G.CA) (sm_load a b)))
        <-> holds p (@G.val prop (@G.start_core prop a b) G.CA)).
      rewrite <- (eval_iff p).
      destruct (eval p (@G.val prop (@G.start_core prop a b) G.CA)) eqn:E.
      * rewrite (trap_rec_ok _ (sm_chain_err p G.CA a b E)), sm_chain_set, E.
        split; [intros _; reflexivity |]. intros _. apply claims_le.
        intros x [<- | []]. left. reflexivity.
      * rewrite (trap_rec_err _ (sm_chain_trap p G.CA a b E)).
        split; [| intro Hd; discriminate Hd]. intro Hle.
        pose proof (proj1 (claims_le _ _) Hle (p, G.CA) (or_introl eq_refl)) as Hin. destruct Hin.
    + split; [exists v, 0; exact Hv | exists w, 0; exact Hw].
  - split; [intros s [_ Hz]; change (trap_rec s = []); unfold trap_rec; rewrite Hz;
            destruct (G.err (G.core_of (as_core s))); reflexivity |].
    split; [| split; [exact Hs | exact Hr]].
    intros s0 tr m Hc Hexit.
    set (s := am_run small_axm tr s0) in *.
    destruct (G.err (G.core_of (as_core s))) eqn:Hes.
    + exfalso. apply Hexit.
      change (bp_le claims_pre (trap_rec (as_exec s m)) (trap_rec s)).
      rewrite (trap_rec_err _ (err_stays s m Hes)), (trap_rec_err _ Hes). apply bp_le_refl.
    + destruct (G.err (G.core_of (as_core (as_exec s m)))) eqn:Hen.
      * exfalso. apply Hexit.
        change (bp_le claims_pre (trap_rec (as_exec s m)) (trap_rec s)).
        rewrite (trap_rec_err _ Hen). apply claims_le. intros x Hx. destruct Hx.
      * assert (Hset : ax_exit_step (AM := small_axm) s m).
        { intro Hle. apply Hexit.
          change (bp_le claims_pre (trap_rec (as_exec s m)) (trap_rec s)).
          rewrite (trap_rec_ok _ Hen), (trap_rec_ok _ Hes). exact Hle. }
        destruct (sm_earned_exit s0 tr m Hc Hset)
          as [pre [c [chk [mid1 [cmt [mid2 [Ht [Hk1 [Hk2 [Hk3 [Hck [Hsame Hlub]]]]]]]]]]]].
        exists pre, c, chk, mid1, cmt, mid2.
        split; [exact Ht |]. split; [exact Hk1 |]. split; [exact Hk2 |]. split; [exact Hk3 |].
        split; [exact Hck |]. split; [exact Hsame |].
        change (ax_is_lub claims_pre (trap_rec s) [c] (trap_rec (as_exec s m))).
        rewrite (trap_rec_ok _ Hen), (trap_rec_ok _ Hes). exact Hlub.
  - intro Hg.
    set (s := am_run small_axm (sm_chain p G.CA) (sm_load v 0)).
    assert (Hev : eval p (@G.val prop (@G.start_core prop v 0) G.CA) = true)
      by (apply eval_iff; exact Hv).
    assert (Hes : G.err (G.core_of (as_core s)) = false) by exact (sm_chain_err p G.CA v 0 Hev).
    assert (Hfacts : G.facts (G.core_of (as_core s)) = [G.claim (@G.start_core prop v 0) p G.CA])
      by exact (sm_chain_facts p G.CA v 0 Hev).
    assert (Hcm : G.commit_ok prop_eqb (G.core_of (as_core s)) p G.CB = false).
    { destruct (G.commit_ok prop_eqb (G.core_of (as_core s)) p G.CB) eqn:E; [| reflexivity].
      exfalso. apply (G.generic_commit_ok_iff prop_eqb prop_eqb_eq) in E as [_ Hin].
      rewrite Hfacts in Hin. destruct Hin as [Heq | []].
      discriminate (f_equal G.f_ctr Heq). }
    pose proof (G.generic_unearned_commit_traps prop_eqb eval (G.core_of (as_core s)) p G.CB Hcm)
      as [Herr _].
    pose proof (Hg s (G.COMMIT p G.CB)) as Hle.
    change (bp_le claims_pre (trap_rec s) (trap_rec (as_exec s (G.COMMIT p G.CB)))) in Hle.
    assert (Hen : G.err (G.core_of (as_core (as_exec s (G.COMMIT p G.CB)))) = true)
      by exact Herr.
    rewrite (trap_rec_err _ Hen), (trap_rec_ok _ Hes) in Hle.
    assert (Hset : as_set s = [(p, G.CA)]) by (unfold s; rewrite sm_chain_set, Hev; reflexivity).
    rewrite Hset in Hle.
    pose proof (proj1 (claims_le _ _) Hle (p, G.CA) (or_introl eq_refl)) as Hin. destruct Hin.
Qed.

End SmallAxis.

Print Assumptions small_axis_thiele_complete.
Print Assumptions small_every_claim.
Print Assumptions small_record_is_join.
Print Assumptions small_flag_agrees.
Print Assumptions small_projection_commutes.
Print Assumptions small_infinite_fibre.
Print Assumptions over_nec_join.
Print Assumptions trap_nec_growth.
