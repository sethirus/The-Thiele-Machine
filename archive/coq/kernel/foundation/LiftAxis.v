(** LiftAxis: the lifting theorem on the axis.

    AxComplete.v defines Thiele-complete on the axis: the record is a position
    in any preorder, and a move that takes the record out of the down-set of
    where it stood is a CERTIFY preceded by an earned chain, landing exactly on
    the least upper bound of the old record and the point the claim stands
    for.  Here the earned layer of LiftCore.v is lifted again, now with the
    certified flag replaced by a record in any axis (A, P) with a floor and
    joins.

    The record starts at the floor.  CERTIFY with a committed fact of claim c
    replaces the record r by the join of r and the point of c.  Nothing else
    touches the record.

    Results (closed):

      lift_lax_thiele_complete          for every universal base of every machine,
                                   every axis with joins, every claim language
                                   whose points are given by a function, every
                                   cap of at least 1, and a claim that is true
                                   at one loaded start, false at another, and
                                   whose point is not below the floor, the
                                   lifted axis machine is Thiele-complete on the
                                   axis.
      lift_lax_window_thiele_complete   with the window language, whose claims carry
                                   a point from any sequence of points of the
                                   axis: every universal base lifts onto every
                                   axis with joins and a point above the floor.
      lift_ax_tc_point_above_floor      the point above the floor is necessary: any
                                   Thiele-complete axis machine, on any base,
                                   has a claim whose point is not below its
                                   floor; so an axis in which everything is below
                                   the floor carries no Thiele-complete machine.
      lift_ax_tc_exit_is_lub            joins are what the landing needs: every move
                                   that leaves the down-set lands on a least
                                   upper bound.  On the V-shaped axis f < x,
                                   f < y, x and y incomparable, a record at x
                                   can never leave x's down-set
                                   [V_no_exit_from_x], so no machine carries a
                                   record that every claim can raise from every
                                   state without joins.
      lift_lax_flag_view                reading the lifted axis machine through "the
                                   record has left the floor" gives a machine
                                   Thiele-complete in the one-bit sense of
                                   ThieleComplete.v.                         *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Minimal Require Import LiftCore LiftConverse.

Ltac lift_lax_leq := repeat first [rewrite <- app_assoc | progress simpl]; reflexivity.

(** An axis with a floor and joins. *)
Record lift_axis {A : Type} (P : BPre A) : Type := lift_mk_lax {
  lift_la_floor : A;
  lift_la_join : A -> A -> A;
  lift_la_join_lub : forall x y, ax_is_lub P x y (lift_la_join x y)
}.

Arguments lift_la_floor {A P} _.
Arguments lift_la_join {A P} _ _ _.
Arguments lift_la_join_lub {A P} _ _ _.

Section LAX.

Context {A : Type} {P : BPre A} (AX : lift_axis P).
Variable M0 : T.machine.
Variable LG : lift_lang (T.m_state M0).
Variable cap : nat.
Variable pt : lift_ll_claim LG -> A.

(** The record after one move: raised only by CERTIFY with a fact in the channel. *)
Definition lift_lax_next (s : lift_lstate M0 LG) (r : A) (m : lift_lmove M0 LG) : A :=
  match m with
  | lift_LCertify =>
      if lift_certify_ok s then
        match lift_ls_chan s with
        | Some f => lift_la_join AX r (pt (lift_lf_claim f))
        | None => r
        end
      else r
  | _ => r
  end.

Definition lift_lax_machine : amachine A P :=
  mk_am A P (lift_lstate M0 LG * A)%type (lift_lmove M0 LG)
    (fun x m => (lift_step cap (fst x) m, lift_lax_next (fst x) (snd x) m))
    (fun m => lift_cost m) (fun x => snd x).

Lemma lift_lax_run_fst : forall tr x,
  fst (am_run lift_lax_machine tr x) = lift_lrun cap tr (fst x).
Proof.
  induction tr as [| m tr IH]; intro x; [reflexivity |].
  rewrite am_run_cons. simpl. rewrite IH. reflexivity.
Qed.

Lemma lift_lax_next_cases : forall s r m, ~ bp_le P (lift_lax_next s r m) r ->
  m = lift_LCertify /\ lift_certify_ok s = true /\
  exists f, lift_ls_chan s = Some f /\ lift_lax_next s r m = lift_la_join AX r (pt (lift_lf_claim f)).
Proof.
  intros s r m H. destruct m; simpl in H; try (exfalso; apply H; apply bp_le_refl).
  unfold lift_lax_next in H |- *. destruct (lift_certify_ok s) eqn:Eok;
    [| exfalso; apply H; apply bp_le_refl].
  destruct (lift_ls_chan s) as [f |] eqn:Ech; [| exfalso; apply H; apply bp_le_refl].
  split; [reflexivity |]. split; [reflexivity |]. exists f. split; reflexivity.
Qed.

Lemma lift_lax_grows : forall s r m, bp_le P r (lift_lax_next s r m).
Proof.
  intros s r m. unfold lift_lax_next. destruct m; try apply bp_le_refl.
  destruct (lift_certify_ok s); [| apply bp_le_refl].
  destruct (lift_ls_chan s); [| apply bp_le_refl].
  exact (proj1 (lift_la_join_lub AX _ _)).
Qed.

Lemma lift_lax_step_eq : forall x m, am_step lift_lax_machine x m
  = (lift_step cap (fst x) m, lift_lax_next (fst x) (snd x) m).
Proof. reflexivity. Qed.

Lemma lift_lax_next_certify_ok : forall (s : lift_lstate M0 LG) r f,
  lift_certify_ok s = true -> lift_ls_chan s = Some f ->
  lift_lax_next s r lift_LCertify = lift_la_join AX r (pt (lift_lf_claim f)).
Proof. intros s r f Hok Hch. unfold lift_lax_next. rewrite Hok, Hch. reflexivity. Qed.

Lemma lift_lax_next_certify_no : forall (s : lift_lstate M0 LG) r,
  lift_certify_ok s = false -> lift_lax_next s r lift_LCertify = r.
Proof. intros s r Hok. unfold lift_lax_next. rewrite Hok. reflexivity. Qed.

Section Interface.

Variable U : T.universal_base M0.

Local Notation ld a b := (@lift_load M0 LG U a b).

Definition lift_lax_ub : T.universal_base (am_bare lift_lax_machine) :=
  T.mk_ub (am_bare lift_lax_machine) (fun x => T.ub_window U (lift_ls_base (fst x)))
    (fun x => lift_live U (fst x))
    (fun i => lift_LBase (T.ub_compile U i))
    (fun a b => (ld a b, lift_la_floor AX))
    (fun a b => T.ub_load_window U a b)
    (fun a b => conj eq_refl (T.ub_load_live U a b))
    (fun x i Hl => lift_sim M0 LG cap U (fst x) i Hl).

Definition lift_lax_interface : ax_interface lift_lax_machine :=
  mk_axi A P lift_lax_machine lift_lax_ub (lift_ll_claim LG) (fun m => lift_kind m)
    (fun c x => lift_ll_mean LG c (lift_ls_base (fst x)))
    (fun x c => lift_check_ok cap (fst x) c)
    (fun c x y => lift_ls_base (fst x) = lift_ls_base (fst y))
    (fun x => lift_clean (fst x) /\ snd x = lift_la_floor AX)
    (fun x => lift_ls_mu (fst x))
    (lift_la_floor AX) pt.

(** (a) *)
Lemma lift_lax_base_clause : axc_base lift_lax_interface.
Proof.
  split; [| split; [| split]].
  - intro i. reflexivity.
  - intros a b. unfold ax_load. simpl. split; [| reflexivity].
    unfold lift_clean. simpl. repeat split; reflexivity.
  - intros x m Hk. destruct m; simpl in Hk; try discriminate. reflexivity.
  - intros x m. simpl. apply lift_lax_grows.
Qed.

(** (b) *)
Lemma lift_lax_earned_exit : forall s0 tr m, axi_clean lift_lax_interface s0 ->
  ax_exit_step (am_run lift_lax_machine tr s0) m -> axc_earned_exit lift_lax_interface s0 tr m.
Proof.
  intros [s00 r0] tr m [[Hf [Hc H0]] Hr0] Hex. simpl in Hf, Hc, H0, Hr0.
  unfold ax_exit_step in Hex. simpl in Hex.
  destruct (lift_lax_next_cases _ _ _ Hex) as [-> [Hok [f [Hch Hnext]]]].
  rewrite lift_lax_run_fst in Hch. simpl in Hch.
  unfold lift_certify_ok in Hok. rewrite lift_lax_run_fst in Hok. simpl in Hok.
  destruct (lift_chan_prov M0 LG cap s00 Hc tr f Hch)
    as [pre [c [mid2 [Htr [Hfc Hin]]]]].
  destruct (lift_facts_prov M0 LG cap s00 Hf pre f Hin)
    as [pre1 [c1 [mid1 [Hpre1 [Hfc1 Hck]]]]].
  rewrite Hfc in Hfc1. injection Hfc1 as Hc1 Hv. subst c1.
  assert (Hall : tr = pre1 ++ lift_LCheck c :: mid1 ++ lift_LCommit c :: mid2)
    by (rewrite Htr, Hpre1; lift_lax_leq).
  exists pre1, c, (lift_LCheck c), mid1, (lift_LCommit c), mid2.
  split; [exact Hall |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split.
  - simpl. rewrite lift_lax_run_fst. simpl. exact Hck.
  - split.
    + intros t1 t2 Hm. simpl. rewrite !lift_lax_run_fst. simpl.
      set (s := lift_lrun cap pre1 s00) in *.
      assert (Hrun : lift_lrun cap pre s00 = lift_lrun cap t2 (lift_lrun cap (lift_LCheck c :: t1) s)).
      { rewrite Hpre1, lift_lrun_app, Hm.
        replace (lift_LCheck c :: (t1 ++ t2)) with ((lift_LCheck c :: t1) ++ t2) by reflexivity.
        rewrite lift_lrun_app. reflexivity. }
      assert (Hlo : lift_ls_ver s <= lift_ls_ver (lift_lrun cap (lift_LCheck c :: t1) s))
        by apply lift_ver_mono_run.
      assert (Hhi : lift_ls_ver (lift_lrun cap (lift_LCheck c :: t1) s) <= lift_ls_ver (lift_lrun cap pre s00)).
      { rewrite Hrun. apply lift_ver_mono_run. }
      assert (Heq : lift_ls_ver (lift_lrun cap (lift_LCheck c :: t1) s) = lift_ls_ver s) by lia.
      unfold s in *.
      replace (lift_lrun cap (pre1 ++ lift_LCheck c :: t1) s00)
        with (lift_lrun cap (lift_LCheck c :: t1) (lift_lrun cap pre1 s00)) by (rewrite lift_lrun_app; reflexivity).
      rewrite (lift_ver_eq_base_run M0 LG cap (lift_LCheck c :: t1) (lift_lrun cap pre1 s00) Heq).
      reflexivity.
    + change (ax_is_lub P (snd (am_run lift_lax_machine tr (s00, r0))) (pt c)
                (lift_lax_next (fst (am_run lift_lax_machine tr (s00, r0)))
                   (snd (am_run lift_lax_machine tr (s00, r0))) lift_LCertify)).
      rewrite Hnext, Hfc. simpl. apply lift_la_join_lub.
Qed.

Lemma lift_lax_earned_clause : axc_earned lift_lax_interface.
Proof.
  split; [intros x [_ H]; exact H |]. split.
  - intros s0 tr m Hc Hex. apply lift_lax_earned_exit; assumption.
  - split.
    + intros x c H. simpl in *. unfold lift_check_ok in H.
      apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
      apply lift_ll_eval_iff, H.
    + intros c x y Hs Hm. simpl in *. rewrite <- Hs. exact Hm.
Qed.

(** (c) *)
Lemma lift_lax_toll_clause : axc_toll lift_lax_interface.
Proof.
  split.
  - intro m. destruct m; reflexivity.
  - intros x m. simpl. apply lift_mu_step.
Qed.

(** (d) *)
Definition lift_lax_nonvacuous : Prop :=
  exists c, (exists a b, lift_ll_mean LG c (T.ub_load U a b)) /\
            (exists a b, ~ lift_ll_mean LG c (T.ub_load U a b)) /\
            ~ bp_le P (pt c) (lift_la_floor AX).

Lemma lift_lax_chain_true : forall (s : lift_lstate M0 LG) r c, 0 < cap -> lift_ls_err s = false ->
  lift_ls_facts s = [] -> lift_ll_mean LG c (lift_ls_base s) ->
  snd (am_run lift_lax_machine [lift_LCheck c; lift_LCommit c; lift_LCertify] (s, r)) = lift_la_join AX r (pt c).
Proof.
  intros s r c Hcap He Hf Hm.
  assert (Hk : lift_check_ok cap s c = true).
  { unfold lift_check_ok. rewrite He, Hf. simpl. apply andb_true_iff. split.
    - apply lift_ll_eval_iff, Hm.
    - apply Nat.ltb_lt. exact Hcap. }
  set (s1 := lift_step cap s (lift_LCheck c)).
  assert (Hs1 : s1 = lift_mk_ls (lift_ls_base s) (lift_ls_ver s) (lift_mk_lfact c (lift_ls_ver s) :: lift_ls_facts s)
                           (lift_ls_chan s) false (lift_ls_mu s + 1) (lift_ls_cert s))
    by (apply lift_step_check_ok; assumption).
  assert (Hc : lift_commit_ok s1 c = true).
  { rewrite Hs1. unfold lift_commit_ok. simpl. apply orb_true_iff. left.
    apply lift_lfact_eqb_eq. reflexivity. }
  set (s2 := lift_step cap s1 (lift_LCommit c)).
  assert (Hs2 : s2 = lift_mk_ls (lift_ls_base s1) (lift_ls_ver s1) (lift_ls_facts s1)
                           (Some (lift_mk_lfact c (lift_ls_ver s1))) false (lift_ls_mu s1 + 1) (lift_ls_cert s1))
    by (apply lift_step_commit_ok; [rewrite Hs1; reflexivity | exact Hc]).
  assert (Hr : lift_certify_ok s2 = true) by (rewrite Hs2; reflexivity).
  assert (Hchan : lift_ls_chan s2 = Some (lift_mk_lfact c (lift_ls_ver s1))) by (rewrite Hs2; reflexivity).
  rewrite !am_run_cons, am_run_nil, !lift_lax_step_eq. cbn [fst snd].
  change (lift_step cap s (lift_LCheck c)) with s1.
  change (lift_step cap s1 (lift_LCommit c)) with s2.
  assert (HX : lift_lax_next s1 (lift_lax_next s r (lift_LCheck c)) (lift_LCommit c) = r) by reflexivity.
  rewrite HX. rewrite (lift_lax_next_certify_ok s2 r _ Hr Hchan). reflexivity.
Qed.

Lemma lift_lax_chain_false : forall (s : lift_lstate M0 LG) r c, 0 < cap -> lift_ls_err s = false ->
  ~ lift_ll_mean LG c (lift_ls_base s) ->
  snd (am_run lift_lax_machine [lift_LCheck c; lift_LCommit c; lift_LCertify] (s, r)) = r.
Proof.
  intros s r c Hcap He Hn.
  assert (Hk : lift_check_ok cap s c = false).
  { destruct (lift_check_ok cap s c) eqn:E; [| reflexivity]. exfalso. apply Hn.
    unfold lift_check_ok in E. apply andb_true_iff in E as [E _].
    apply andb_true_iff in E as [_ E]. apply lift_ll_eval_iff, E. }
  set (s1 := lift_step cap s (lift_LCheck c)).
  assert (Hs1 : lift_ls_err s1 = true)
    by (unfold s1; rewrite (lift_step_check_fail M0 LG cap s c He Hk); reflexivity).
  set (s2 := lift_step cap s1 (lift_LCommit c)).
  assert (Hs2 : lift_ls_err s2 = true)
    by (unfold s2; rewrite (lift_step_err M0 LG cap s1 (lift_LCommit c) Hs1); reflexivity).
  assert (Hn2 : lift_certify_ok s2 = false)
    by (unfold lift_certify_ok; rewrite Hs2; reflexivity).
  rewrite !am_run_cons, am_run_nil, !lift_lax_step_eq. cbn [fst snd].
  change (lift_step cap s (lift_LCheck c)) with s1.
  change (lift_step cap s1 (lift_LCommit c)) with s2.
  assert (HX : lift_lax_next s1 (lift_lax_next s r (lift_LCheck c)) (lift_LCommit c) = r) by reflexivity.
  rewrite HX. rewrite (lift_lax_next_certify_no s2 r Hn2). reflexivity.
Qed.

Lemma lift_lax_nonvac_clause : 0 < cap -> lift_lax_nonvacuous -> axc_nonvac lift_lax_interface.
Proof.
  intros Hcap [c [Hy [Hn Hp]]].
  exists c, (lift_LCheck c), (lift_LCommit c), lift_LCertify.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| split; [exact Hy | exact Hn]].
  intros a b. unfold ax_load. simpl.
  change (bp_le P (pt c) (snd (am_run lift_lax_machine [lift_LCheck c; lift_LCommit c; lift_LCertify]
                                       (ld a b, lift_la_floor AX)))
          <-> lift_ll_mean LG c (lift_ls_base (ld a b))).
  split.
  - intro H. destruct (lift_ll_eval LG c (lift_ls_base (ld a b))) eqn:E.
    + apply lift_ll_eval_iff, E.
    + exfalso.
      assert (Hm : ~ lift_ll_mean LG c (lift_ls_base (ld a b))).
      { intro Hm. apply lift_ll_eval_iff in Hm. congruence. }
      rewrite (lift_lax_chain_false (ld a b) (lift_la_floor AX) c Hcap eq_refl Hm) in H.
      exact (Hp H).
  - intro H. rewrite (lift_lax_chain_true (ld a b) (lift_la_floor AX) c Hcap eq_refl eq_refl H).
    exact (proj1 (proj2 (lift_la_join_lub AX (lift_la_floor AX) (pt c)))).
Qed.

End Interface.

End LAX.

(** * The lifting theorem on the axis *)

Theorem lift_lax_thiele_complete_with : forall {A : Type} {P : BPre A} (AX : lift_axis P)
    M0 (LG : lift_lang (T.m_state M0)) cap (pt : lift_ll_claim LG -> A)
    (U : T.universal_base M0),
  0 < cap -> lift_lax_nonvacuous AX M0 LG pt U ->
  ax_tc_with (lift_lax_interface AX M0 LG cap pt U).
Proof.
  intros A P AX M0 LG cap pt U Hcap Hnv.
  split; [apply lift_lax_base_clause |]. split; [apply lift_lax_earned_clause |].
  split; [apply lift_lax_toll_clause | apply lift_lax_nonvac_clause; assumption].
Qed.

Theorem lift_lax_thiele_complete : forall {A : Type} {P : BPre A} (AX : lift_axis P)
    M0 (LG : lift_lang (T.m_state M0)) cap (pt : lift_ll_claim LG -> A)
    (U : T.universal_base M0),
  0 < cap -> lift_lax_nonvacuous AX M0 LG pt U ->
  ax_thiele_complete (lift_lax_machine AX M0 LG cap pt).
Proof.
  intros A P AX M0 LG cap pt U Hcap Hnv. exists (lift_lax_interface AX M0 LG cap pt U).
  apply lift_lax_thiele_complete_with; assumption.
Qed.

(** * The window language with points *)

Definition lift_wcn_eqb (c d : lift_wclaim * nat) : bool :=
  lift_wc_eqb (fst c) (fst d) && Nat.eqb (snd c) (snd d).

Lemma lift_wcn_eqb_eq : forall c d, lift_wcn_eqb c d = true <-> c = d.
Proof.
  intros [c n] [d m]. unfold lift_wcn_eqb. simpl.
  rewrite andb_true_iff, lift_wc_eqb_eq, Nat.eqb_eq. split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H. auto.
Qed.

(** A claim is a window claim and an index; its point is the point of the axis
    at that index. *)
Definition lift_window_lang_pts (M0 : T.machine) (U : T.universal_base M0)
  : lift_lang (T.m_state M0) :=
  lift_mk_ll (T.m_state M0) (lift_wclaim * nat)%type lift_wcn_eqb lift_wcn_eqb_eq
    (fun c s => lift_wc_mean (fst c) (T.ub_window U s))
    (fun c s => lift_wc_eval (fst c) (T.ub_window U s))
    (fun c s => lift_wc_eval_iff (fst c) (T.ub_window U s)).

Theorem lift_lax_window_thiele_complete : forall {A : Type} {P : BPre A} (AX : lift_axis P)
    M0 (U : T.universal_base M0) cap (pts : nat -> A) k0,
  0 < cap -> ~ bp_le P (pts k0) (lift_la_floor AX) ->
  ax_thiele_complete
    (lift_lax_machine AX M0 (lift_window_lang_pts M0 U) cap (fun ck => pts (snd ck))).
Proof.
  intros A P AX M0 U cap pts k0 Hcap Hp.
  apply (lift_lax_thiele_complete AX M0 _ cap _ U Hcap).
  exists (lift_WGe T.RA 1, k0). split; [| split; [| exact Hp]].
  - exists 1, 0. simpl. rewrite (T.ub_load_window U 1 0). simpl. lia.
  - exists 0, 0. simpl. rewrite (T.ub_load_window U 0 0). simpl. lia.
Qed.

(** * Necessity on the axis *)

(** Some claim has a point not below the floor: a Thiele-complete axis machine,
    on any base, needs room above its floor. *)
Theorem lift_ax_tc_point_above_floor : forall {A : Type} {P : BPre A} {AM : amachine A P}
    (I : ax_interface AM), ax_tc_with I ->
  exists c, ~ bp_le P (axi_point I c) (axi_floor I).
Proof.
  intros A P AM I HC. pose proof HC as HC'.
  destruct HC' as [_ [_ [_ Hn]]].
  destruct Hn as [c [chk [cmt [crt [_ [_ [_ [Hiff [_ Hno]]]]]]]]].
  exists c. exact (ax_witness_nontrivial I HC c chk cmt crt Hiff Hno).
Qed.

(** An axis in which everything is below everything carries no Thiele-complete
    machine. *)
Corollary lift_ax_indiscrete_no_machine : forall {A : Type} {P : BPre A} (AM : amachine A P),
  (forall x y, bp_le P x y) -> ~ ax_thiele_complete AM.
Proof.
  intros A P AM Hall [I HC]. destruct (lift_ax_tc_point_above_floor I HC) as [c Hc].
  apply Hc. apply Hall.
Qed.

(** Every move that leaves the down-set lands on a least upper bound of the
    old record and the point of its claim. *)
Theorem lift_ax_tc_exit_is_lub : forall {A : Type} {P : BPre A} {AM : amachine A P}
    (I : ax_interface AM), ax_tc_with I ->
  forall s0 tr m, axi_clean I s0 -> ax_exit_step (am_run AM tr s0) m ->
  exists c, ax_is_lub P (am_rec AM (am_run AM tr s0)) (axi_point I c)
                        (am_rec AM (am_step AM (am_run AM tr s0) m)).
Proof.
  intros A P AM I HC s0 tr m Hcl Hex.
  destruct HC as [_ [[_ [Hexit _]] _]].
  destruct (Hexit s0 tr m Hcl Hex) as [pre [c [chk [mid1 [cmt [mid2 Hq]]]]]].
  destruct Hq as [_ [_ [_ [_ [_ [_ Hlub]]]]]].
  exists c. exact Hlub.
Qed.

(** The V-shaped axis: a floor f below two incomparable points x and y. *)
Inductive lift_vpt : Type := lift_Vf | lift_Vx | lift_Vy.

Definition lift_vle (a b : lift_vpt) : bool :=
  match a, b with
  | lift_Vf, _ => true
  | lift_Vx, lift_Vx => true
  | lift_Vy, lift_Vy => true
  | _, _ => false
  end.

Definition lift_V_pre : BPre lift_vpt.
Proof.
  refine {| bp_leb := lift_vle |}.
  - intros []; reflexivity.
  - intros [] [] []; simpl; auto; discriminate.
Defined.

Lemma lift_V_no_join : ~ exists z, ax_is_lub lift_V_pre lift_Vx lift_Vy z.
Proof.
  intros [z [Hx [Hy _]]]. destruct z; unfold bp_le in *; simpl in *; discriminate.
Qed.

(** So the lifting cannot be built over the V axis: it asks for a join. *)
Corollary lift_V_not_a_lift_axis : lift_axis lift_V_pre -> False.
Proof.
  intro AX. apply lift_V_no_join. exists (lift_la_join AX lift_Vx lift_Vy). apply lift_la_join_lub.
Qed.

(** In a Thiele-complete machine on the V axis a record at x stays at x for
    ever: it can never be raised towards y.  The growth clause alone gives it. *)
Theorem lift_V_record_stays_x : forall {AM : amachine lift_vpt lift_V_pre} (I : ax_interface AM),
  ax_tc_with I -> forall s tr, am_rec AM s = lift_Vx -> am_rec AM (am_run AM tr s) = lift_Vx.
Proof.
  intros AM I HC s tr Hs. pose proof (ax_run_grows I HC tr s) as H.
  rewrite Hs in H. unfold bp_le in H. destruct (am_rec AM (am_run AM tr s)); simpl in H;
    try discriminate; reflexivity.
Qed.

(** * Reading the lifted axis machine as a one-bit machine *)

Theorem lift_lax_flag_view : forall {A : Type} {P : BPre A} (AX : lift_axis P)
    M0 (LG : lift_lang (T.m_state M0)) cap (pt : lift_ll_claim LG -> A)
    (U : T.universal_base M0),
  0 < cap -> lift_lax_nonvacuous AX M0 LG pt U ->
  T.thiele_complete_with
    (ax_ti_pt (lift_lax_interface AX M0 LG cap pt U)
       (ax_flag_fn (lift_lax_interface AX M0 LG cap pt U))).
Proof.
  intros A P AX M0 LG cap pt U Hcap Hnv.
  exact (ax_flag_view_complete (lift_lax_interface AX M0 LG cap pt U)
           (lift_lax_thiele_complete_with AX M0 LG cap pt U Hcap Hnv)).
Qed.

Print Assumptions lift_lax_thiele_complete.
Print Assumptions lift_lax_window_thiele_complete.
Print Assumptions lift_ax_tc_point_above_floor.
Print Assumptions lift_ax_tc_exit_is_lub.
Print Assumptions lift_V_record_stays_x.
Print Assumptions lift_lax_flag_view.
