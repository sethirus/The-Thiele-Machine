(** NecSClean.v: which part of "clean start" the small machine's earned
    chain really needs, and exactly how much each part is worth.

    The book's chapter "The smallest honest machine" proves that from a
    clean start (empty table, empty channel, flag down) a raised flag costs
    at least 3 and was checked, then committed, then certified. This file
    pushes those statements to their limit:

      - each of the three conjuncts of a clean start is necessary, and each
        one is worth exactly one unit of the price: without the flag down a
        certificate can cost 0, without the empty channel 1, without the
        empty table 2, and each of those floors is attained;
      - the empty table can be weakened to a table whose facts are all
        stale (every fact about an older version than the counter's current
        one), and with that weakening the condition is EXACT: from a state
        the floor of 3 holds for every run if and only if the flag is down
        and either the trap is up or (the channel is empty and every fact
        is stale);
      - checker soundness needs only a sound start table, not a clean
        start, and both halves of "sound" are needed;
      - no forging holds exactly when the start table is empty.

    Everything is about the repository's own machine (Minimal.EarnedCore). *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.EarnedCore.

(* ================================================================= *)
(* Basic run facts.                                                   *)
(* ================================================================= *)

Lemma nec_s_run_trapped : forall tr s,
  err (core_of s) = true ->
  core_of (run tr s) = core_of s /\ cert (run tr s) = cert s.
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [auto |].
  assert (Hk : cexec (core_of s) i = core_of s) by (unfold cexec; rewrite H; reflexivity).
  assert (Hf : fires (core_of s) i = false).
  { destruct i; simpl; try reflexivity. unfold certify_ok. rewrite H. reflexivity. }
  destruct (IH (exec s i)) as [H1 H2]; [simpl; rewrite Hk; exact H |].
  rewrite H1, H2. simpl. rewrite Hk, Hf, orb_false_r. auto.
Qed.

Lemma nec_s_total_cost_incs : forall n c, total_cost (repeat (INC c) n) = 0.
Proof. induction n; intros; simpl; auto. Qed.

Lemma nec_s_inc_step : forall s c,
  err (core_of s) = false ->
  ver (core_of (exec s (INC c))) c = S (ver (core_of s) c) /\
  val (core_of (exec s (INC c))) c = S (val (core_of s) c) /\
  (forall d, d <> c -> val (core_of (exec s (INC c))) d = val (core_of s) d) /\
  facts (core_of (exec s (INC c))) = facts (core_of s) /\
  chan (core_of (exec s (INC c))) = chan (core_of s) /\
  err (core_of (exec s (INC c))) = false /\
  cert (exec s (INC c)) = cert s.
Proof.
  intros [[a b u v p fs ch e] m r] c He. simpl in He. subst e.
  destruct c; simpl; repeat split; try reflexivity; try apply orb_false_r;
    intros [] Hd; simpl; try reflexivity; congruence.
Qed.

Lemma nec_s_dec_step : forall s c j n,
  err (core_of s) = false -> val (core_of s) c = S n ->
  val (core_of (exec s (DEC c j))) c = n /\
  (forall d, d <> c -> val (core_of (exec s (DEC c j))) d = val (core_of s) d) /\
  pc (core_of (exec s (DEC c j))) = j /\
  err (core_of (exec s (DEC c j))) = false /\
  cert (exec s (DEC c j)) = cert s.
Proof.
  intros [[a b u v p fs ch e] m r] c j n He Hv. simpl in He, Hv. subst e.
  destruct c; simpl in *; subst; simpl; repeat split; try reflexivity;
    try apply orb_false_r; intros [] Hd; simpl; try reflexivity; congruence.
Qed.

(* n increments of counter c from an untrapped state. *)
Lemma nec_s_run_incs : forall n s c,
  err (core_of s) = false ->
  ver (core_of (run (repeat (INC c) n) s)) c = ver (core_of s) c + n /\
  val (core_of (run (repeat (INC c) n) s)) c = val (core_of s) c + n /\
  (forall d, d <> c ->
     val (core_of (run (repeat (INC c) n) s)) d = val (core_of s) d) /\
  facts (core_of (run (repeat (INC c) n) s)) = facts (core_of s) /\
  chan (core_of (run (repeat (INC c) n) s)) = chan (core_of s) /\
  err (core_of (run (repeat (INC c) n) s)) = false /\
  cert (run (repeat (INC c) n) s) = cert s.
Proof.
  induction n as [| n IH]; intros s c He; simpl.
  - repeat split; auto; lia.
  - destruct (nec_s_inc_step s c He) as [Hv1 [Hval1 [Hoth1 [Hf1 [Hc1 [He1 Hcert1]]]]]].
    destruct (IH (exec s (INC c)) c He1) as [Hv [Hval [Hoth [Hf [Hc [He' Hcert]]]]]].
    rewrite Hv, Hval, Hf, Hc, He', Hcert, Hv1, Hval1, Hf1, Hc1, Hcert1.
    repeat split; try lia; auto.
    intros d Hd. rewrite Hoth, Hoth1 by exact Hd. reflexivity.
Qed.

(* n decrements (each on a positive counter) of counter c. *)
Lemma nec_s_run_decs : forall n s c j,
  err (core_of s) = false -> n <= val (core_of s) c ->
  val (core_of (run (repeat (DEC c j) n) s)) c = val (core_of s) c - n /\
  (forall d, d <> c ->
     val (core_of (run (repeat (DEC c j) n) s)) d = val (core_of s) d) /\
  err (core_of (run (repeat (DEC c j) n) s)) = false /\
  cert (run (repeat (DEC c j) n) s) = cert s.
Proof.
  induction n as [| n IH]; intros s c j He Hn; simpl.
  - repeat split; auto; lia.
  - destruct (val (core_of s) c) as [| v] eqn:Hv; [lia |].
    destruct (nec_s_dec_step s c j v He Hv) as [Hval1 [Hoth1 [_ [He1 Hcert1]]]].
    destruct (IH (exec s (DEC c j)) c j He1 ltac:(lia)) as [Hval [Hoth [He' Hcert]]].
    rewrite Hval, He', Hcert, Hval1, Hcert1.
    repeat split; try lia; auto.
    intros d Hd. rewrite Hoth, Hoth1 by exact Hd. reflexivity.
Qed.

(* ================================================================= *)
(* 1. Each conjunct of a clean start is worth exactly one unit.       *)
(* ================================================================= *)

(* Flag already up, otherwise clean. *)
Definition nec_s_flag_up : state := mkst (start_core 0 0) 0 true.
(* Channel already holding a commitment, otherwise clean. *)
Definition nec_s_chan_set : state :=
  mkst (mkcore 0 0 0 0 1 [] (Some (mkfact PZero CA 0)) false) 0 false.
(* Table already holding a live fact, otherwise clean. *)
Definition nec_s_fact_set : state :=
  mkst (mkcore 0 0 0 0 1 [mkfact PZero CA 0] None false) 0 false.

Theorem nec_s_clean_conjuncts_each_buy_one :
  (facts (core_of nec_s_flag_up) = [] /\ chan (core_of nec_s_flag_up) = None /\
   cert (run [] nec_s_flag_up) = true /\ total_cost [] = 0) /\
  (facts (core_of nec_s_chan_set) = [] /\ cert nec_s_chan_set = false /\
   cert (run [CERTIFY] nec_s_chan_set) = true /\ total_cost [CERTIFY] = 1) /\
  (chan (core_of nec_s_fact_set) = None /\ cert nec_s_fact_set = false /\
   cert (run [COMMIT PZero CA; CERTIFY] nec_s_fact_set) = true /\
   total_cost [COMMIT PZero CA; CERTIFY] = 2).
Proof. vm_compute. repeat split. Qed.

(* With the flag down and the channel empty, a certificate costs at least
   2 whatever the table holds: some COMMIT and then the CERTIFY. *)
Theorem nec_s_floor_two : forall s0 tr,
  cert s0 = false -> chan (core_of s0) = None -> cert (run tr s0) = true ->
  total_cost tr >= 2.
Proof.
  intros s0 tr Hc0 Hch H1.
  destruct (cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  unfold certify_ok in Hok. apply andb_true_iff in Hok as [_ Hok].
  destruct (chan (core_of (run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (chan_origin s0 pre f Hch Hf) as [pre1 [p [c [mid [-> _]]]]].
  rewrite !total_cost_app. simpl. lia.
Qed.

(* The three ways to drop a conjunct, each refuting the floor it buys. *)
Theorem nec_s_min_cost_needs_flag_down :
  ~ (forall s0 tr, facts (core_of s0) = [] -> chan (core_of s0) = None ->
       cert (run tr s0) = true -> total_cost tr >= 1).
Proof.
  intro H. specialize (H nec_s_flag_up [] eq_refl eq_refl eq_refl). simpl in H. lia.
Qed.

Theorem nec_s_min_cost_needs_empty_channel :
  ~ (forall s0 tr, facts (core_of s0) = [] -> cert s0 = false ->
       cert (run tr s0) = true -> total_cost tr >= 2).
Proof.
  intro H. specialize (H nec_s_chan_set [CERTIFY] eq_refl eq_refl eq_refl).
  simpl in H. lia.
Qed.

Theorem nec_s_min_cost_needs_empty_table :
  ~ (forall s0 tr, chan (core_of s0) = None -> cert s0 = false ->
       cert (run tr s0) = true -> total_cost tr >= 3).
Proof.
  intro H. specialize (H nec_s_fact_set [COMMIT PZero CA; CERTIFY] eq_refl eq_refl eq_refl).
  simpl in H. lia.
Qed.

(* ================================================================= *)
(* 2. The empty table weakened to a stale table.                      *)
(* ================================================================= *)

(* Every fact in the table is about an older version of its counter. *)
Definition nec_s_stale_table (k : core) : Prop :=
  forall f, In f (facts k) -> f_ver f < ver k (f_ctr f).

Lemma nec_s_old_or_earned : forall s0 tr f,
  In f (facts (core_of (run tr s0))) -> In f (facts (core_of s0)) \/ earned s0 tr f.
Proof.
  intros s0 tr f. revert f. induction tr as [| i tr IH] using rev_ind; intros f Hin.
  - left. exact Hin.
  - rewrite run_snoc in Hin. simpl in Hin.
    destruct (facts_step _ i f Hin) as [Hold | [Hi [Hc Hf]]].
    + destruct (IH f Hold) as [H0 | [pre [mid [Htr [Hc [Hf _]]]]]]; [left; exact H0 |].
      right. rewrite Htr, <- app_assoc. simpl. apply earned_intro; assumption.
    + right. subst i. apply earned_intro; assumption.
Qed.

Theorem nec_s_stale_commitment_provenance : forall s0 pre p c,
  nec_s_stale_table (core_of s0) ->
  commit_ok (core_of (run pre s0)) p c = true ->
  exists pre1 mid,
    pre = pre1 ++ CHECK p c :: mid /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    cost (CHECK p c) >= 1 /\ cost (COMMIT p c) >= 1 /\
    ver (core_of (run pre1 s0)) c = ver (core_of (run pre s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid c.
Proof.
  intros s0 pre p c Hst Hc. apply commit_ok_iff in Hc as [_ Hin].
  destruct (nec_s_old_or_earned s0 pre _ Hin) as [Hold | Hear].
  - exfalso. pose proof (Hst _ Hold) as Hlt. simpl in Hlt.
    pose proof (ver_mono_run pre s0 c). lia.
  - destruct Hear as [pre1 [mid [Htr [Hck [Hf Hlive]]]]].
    simpl in *. exists pre1, mid.
    split; [exact Htr |]. split; [exact Hck |].
    split; [simpl; lia |]. split; [simpl; lia |].
    split; [unfold claim in Hf; injection Hf as Hv; symmetry; exact Hv |].
    apply Hlive. reflexivity.
Qed.

(* The book's earned chain from a start whose table holds only stale facts. *)
Theorem nec_s_stale_certification_provenance : forall s0 tr,
  nec_s_stale_table (core_of s0) -> chan (core_of s0) = None -> cert s0 = false ->
  cert (run tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post /\
    check_ok (core_of (run pre1 s0)) p c = true /\
    commit_ok (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) p c = true /\
    certify_ok (core_of (run (pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2) s0))
      = true /\
    ver (core_of (run pre1 s0)) c = ver (core_of (run (pre1 ++ CHECK p c :: mid1) s0)) c /\
    untouched (run (pre1 ++ [CHECK p c]) s0) mid1 c.
Proof.
  intros s0 tr Hst Hch Hc0 H1.
  destruct (cert_first s0 tr Hc0 H1) as [pre [post [-> [_ Hok]]]].
  pose proof Hok as Hset. unfold certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (chan (core_of (run pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (chan_origin s0 pre f Hch Hf) as [preC [p [c [mid2 [-> [Hcm _]]]]]].
  destruct (nec_s_stale_commitment_provenance s0 preC p c Hst Hcm)
    as [pre1 [mid1 [-> [Hck [_ [_ [Hv Hun]]]]]]].
  exists pre1, p, c, mid1, mid2, post.
  assert (Heq : (pre1 ++ CHECK p c :: mid1) ++ COMMIT p c :: mid2
                = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2)
    by (rewrite <- app_assoc; reflexivity).
  rewrite Heq in Hok.
  split; [rewrite Heq, <- app_assoc; simpl; rewrite <- app_assoc; reflexivity |].
  split; [exact Hck |]. split; [exact Hcm |]. split; [exact Hok |].
  split; [exact Hv | exact Hun].
Qed.

Theorem nec_s_stale_min_cost : forall s0 tr,
  nec_s_stale_table (core_of s0) -> chan (core_of s0) = None -> cert s0 = false ->
  cert (run tr s0) = true ->
  total_cost tr >= 3 /\ mu (run tr s0) >= mu s0 + 3.
Proof.
  intros s0 tr Hst Hch Hc0 H1.
  assert (Hc : total_cost tr >= 3).
  { destruct (nec_s_stale_certification_provenance s0 tr Hst Hch Hc0 H1)
      as [pre1 [p [c [mid1 [mid2 [post [-> _]]]]]]].
    rewrite total_cost_app. simpl. rewrite total_cost_app. simpl.
    rewrite total_cost_app. simpl. lia. }
  split; [exact Hc | rewrite mu_conservation_trace; lia].
Qed.

(* The repository's theorem is the special case of an empty table. *)
Corollary nec_s_clean_is_stale : forall s0, clean_start s0 -> nec_s_stale_table (core_of s0).
Proof. intros s0 [Hf _] f Hin. rewrite Hf in Hin. destruct Hin. Qed.

(* ================================================================= *)
(* 3. The exact condition for the floor of three.                     *)
(* ================================================================= *)

Definition nec_s_floor3 (s0 : state) : Prop :=
  forall tr, cert (run tr s0) = true -> total_cost tr >= 3.

(* A fact that is live or about a future version can be made live by
   increments and then committed and certified for a total of 2. *)
Lemma nec_s_nonstale_cheap : forall s0 f,
  err (core_of s0) = false -> In f (facts (core_of s0)) ->
  ver (core_of s0) (f_ctr f) <= f_ver f ->
  let tr := repeat (INC (f_ctr f)) (f_ver f - ver (core_of s0) (f_ctr f))
              ++ [COMMIT (f_prop f) (f_ctr f); CERTIFY] in
  cert (run tr s0) = true /\ total_cost tr = 2.
Proof.
  intros s0 [p c v] He Hin Hle. simpl in *. split.
  - rewrite run_app.
    destruct (nec_s_run_incs (v - ver (core_of s0) c) s0 c He)
      as [Hv [_ [_ [Hf [_ [He' _]]]]]].
    set (s1 := run (repeat (INC c) (v - ver (core_of s0) c)) s0) in *.
    assert (Hok : commit_ok (core_of s1) p c = true).
    { apply commit_ok_iff. split; [exact He' |].
      rewrite Hf. unfold claim. replace (ver (core_of s1) c) with v by lia. exact Hin. }
    simpl. unfold cexec at 1. rewrite He', Hok. simpl.
    unfold certify_ok. simpl. rewrite He'. simpl. apply orb_true_r.
  - rewrite total_cost_app, nec_s_total_cost_incs. reflexivity.
Qed.

Theorem nec_s_floor3_iff : forall s0,
  nec_s_floor3 s0 <->
  cert s0 = false /\
  (err (core_of s0) = true \/
   (chan (core_of s0) = None /\ nec_s_stale_table (core_of s0))).
Proof.
  intro s0. split.
  - intro H.
    assert (Hc0 : cert s0 = false).
    { destruct (cert s0) eqn:Hc; [| reflexivity].
      specialize (H [] Hc). simpl in H. lia. }
    split; [exact Hc0 |].
    destruct (err (core_of s0)) eqn:He; [left; reflexivity | right].
    split.
    + destruct (chan (core_of s0)) as [g |] eqn:Hch; [| reflexivity].
      exfalso. assert (Hr : cert (run [CERTIFY] s0) = true).
      { simpl. unfold certify_ok. rewrite He, Hch. apply orb_true_r. }
      specialize (H _ Hr). simpl in H. lia.
    + intros f Hin.
      destruct (lt_dec (f_ver f) (ver (core_of s0) (f_ctr f))) as [Hlt | Hge];
        [exact Hlt |].
      exfalso. destruct (nec_s_nonstale_cheap s0 f He Hin ltac:(lia)) as [Hr Hcst].
      specialize (H _ Hr). lia.
  - intros [Hc0 [He | [Hch Hst]]] tr H1.
    + destruct (nec_s_run_trapped tr s0 He) as [_ Hc]. congruence.
    + exact (proj1 (nec_s_stale_min_cost s0 tr Hst Hch Hc0 H1)).
Qed.

(* ================================================================= *)
(* 4. Every clean, untrapped start certifies for exactly 3, and a     *)
(*    clean start can certify at all exactly when it is untrapped.    *)
(* ================================================================= *)

Theorem nec_s_witness_from_every_clean_start : forall s0,
  clean_start s0 -> err (core_of s0) = false ->
  cert (run witness s0) = true /\ mu (run witness s0) = mu s0 + 3.
Proof.
  intros [[a b u v p fs ch e] m r] [Hf [Hch Hc]] He. simpl in *. subst. split.
  - simpl. unfold cexec, check_ok, commit_ok, certify_ok, claim, fact_eqb; simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. lia.
Qed.

Theorem nec_s_clean_certifiable_iff_untrapped : forall s0,
  clean_start s0 -> ((exists tr, cert (run tr s0) = true) <-> err (core_of s0) = false).
Proof.
  intros s0 H0. split.
  - intros [tr Htr]. destruct (err (core_of s0)) eqn:He; [| reflexivity].
    destruct (nec_s_run_trapped tr s0 He) as [_ Hc].
    destruct H0 as [_ [_ Hc0]]. congruence.
  - intro He. exists witness. apply (nec_s_witness_from_every_clean_start s0 H0 He).
Qed.

(* ================================================================= *)
(* 5. Checker soundness: what it really needs.                        *)
(* ================================================================= *)

(* Dropped-stronger: a sound start table suffices; the channel and the
   flag play no part. *)
Theorem nec_s_soundness_from_sound : forall s0 tr f,
  sound (core_of s0) ->
  let k := core_of (run tr s0) in
  In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f)).
Proof.
  intros s0 tr f Hs k Hin Hv. exact (proj2 (sound_run tr s0 Hs f Hin) Hv).
Qed.

Corollary nec_s_clean_is_sound : forall s0, clean_start s0 -> sound (core_of s0).
Proof. intros s0 [Hf _] g Hg. rewrite Hf in Hg. destruct Hg. Qed.

(* The live half of "sound" is needed: a live false fact at the start. *)
Definition nec_s_false_fact : state :=
  mkst (mkcore 5 0 0 0 1 [mkfact PZero CA 0] None false) 0 false.

Theorem nec_s_soundness_needs_live_half :
  ~ (forall s0 tr f, chan (core_of s0) = None -> cert s0 = false ->
       let k := core_of (run tr s0) in
       In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f))).
Proof.
  intro H. specialize (H nec_s_false_fact [] (mkfact PZero CA 0) eq_refl eq_refl).
  simpl in H. assert (Hh : 5 = 0) by (apply H; auto). discriminate.
Qed.

(* The other half of "sound" (no fact about a future version) is needed
   too: a future fact that is dead at the start becomes live and false. *)
Definition nec_s_future_fact : state :=
  mkst (mkcore 0 0 0 0 1 [mkfact PZero CA 1] None false) 0 false.

Theorem nec_s_soundness_needs_no_future_half :
  ~ (forall s0 tr f,
       (forall g, In g (facts (core_of s0)) -> f_ver g = ver (core_of s0) (f_ctr g) ->
                  holds (f_prop g) (val (core_of s0) (f_ctr g))) ->
       let k := core_of (run tr s0) in
       In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f))).
Proof.
  intro H.
  assert (Hpre : forall g, In g (facts (core_of nec_s_future_fact)) ->
            f_ver g = ver (core_of nec_s_future_fact) (f_ctr g) ->
            holds (f_prop g) (val (core_of nec_s_future_fact) (f_ctr g))).
  { intros g [<- | []]. simpl. discriminate. }
  specialize (H nec_s_future_fact [INC CA] (mkfact PZero CA 1) Hpre).
  simpl in H. assert (Hh : 1 = 0) by (apply H; auto). discriminate.
Qed.

(* "Sound" is sufficient but not necessary: a future fact whose property
   is true of every number never does harm. *)
Definition nec_s_harmless_future : state :=
  mkst (mkcore 0 0 0 0 1 [mkfact (PGe 0) CA 1] None false) 0 false.

Definition nec_s_sound_or_trivial (k : core) : Prop :=
  forall f, In f (facts k) ->
    f_prop f = PGe 0 \/
    (f_ver f <= ver k (f_ctr f) /\
     (f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f)))).

Lemma nec_s_sound_or_trivial_step : forall k i,
  nec_s_sound_or_trivial k -> nec_s_sound_or_trivial (cexec k i).
Proof.
  intros k i Hs f Hin.
  pose proof (ver_mono k i (f_ctr f)) as Hm.
  destruct (facts_step k i f Hin) as [Hold | [Hi [Hc Hf]]].
  - destruct (Hs f Hold) as [Htriv | [Hle Hlive]]; [left; exact Htriv | right].
    split; [lia |].
    intro Heq. assert (Hv : ver (cexec k i) (f_ctr f) = ver k (f_ctr f)) by lia.
    rewrite (ver_same_val k i _ Hv). apply Hlive. lia.
  - right. subst i. rewrite ver_check, val_check.
    rewrite Hf. simpl. split; [lia | intros _].
    unfold check_ok in Hc. apply andb_true_iff in Hc as [Hc _].
    apply andb_true_iff in Hc as [_ Hc]. apply eval_iff. exact Hc.
Qed.

Lemma nec_s_sound_or_trivial_run : forall tr s,
  nec_s_sound_or_trivial (core_of s) -> nec_s_sound_or_trivial (core_of (run tr s)).
Proof.
  induction tr as [| i tr IH]; intros s H; simpl; [exact H |].
  apply IH. simpl. apply nec_s_sound_or_trivial_step. exact H.
Qed.

Theorem nec_s_sound_not_necessary :
  ~ sound (core_of nec_s_harmless_future) /\
  (forall tr f,
     let k := core_of (run tr nec_s_harmless_future) in
     In f (facts k) -> f_ver f = ver k (f_ctr f) -> holds (f_prop f) (val k (f_ctr f))).
Proof.
  split.
  - intro Hs. destruct (Hs (mkfact (PGe 0) CA 1) (or_introl eq_refl)) as [Hle _].
    simpl in Hle. lia.
  - intros tr f k Hin Hv.
    assert (Hinv : nec_s_sound_or_trivial k).
    { apply nec_s_sound_or_trivial_run. intros g [<- | []]. left. reflexivity. }
    destruct (Hinv f Hin) as [Htriv | [_ Hlive]]; [| exact (Hlive Hv)].
    rewrite Htriv. simpl. lia.
Qed.

(* The live-version hypothesis is needed: from a clean start a stale fact
   can be false of its counter's current value, and COMMIT refuses it. *)
Theorem nec_s_stale_fact_false :
  let k := core_of (run [CHECK PZero CA; INC CA] (start 0 0)) in
  In (mkfact PZero CA 0) (facts k) /\ ~ holds PZero (val k CA) /\
  commit_ok k PZero CA = false.
Proof. vm_compute. split; [left; reflexivity | split; [discriminate | reflexivity]]. Qed.

Theorem nec_s_soundness_needs_live_version :
  ~ (forall s0 tr f, clean_start s0 ->
       In f (facts (core_of (run tr s0))) ->
       holds (f_prop f) (val (core_of (run tr s0)) (f_ctr f))).
Proof.
  intro H. destruct nec_s_stale_fact_false as [Hin [Hn _]].
  exact (Hn (H (start 0 0) _ _ (start_clean 0 0) Hin)).
Qed.

(* ================================================================= *)
(* 6. No forging holds exactly when the start table is empty.         *)
(* ================================================================= *)

Theorem nec_s_no_forging_iff : forall s0,
  (forall tr, no_forgery s0 tr) <-> facts (core_of s0) = [].
Proof.
  intro s0. split.
  - intro H. destruct (facts (core_of s0)) as [| f fs] eqn:Hf; [reflexivity |].
    exfalso. destruct (H [] f) as [pre [mid [Htr _]]].
    + simpl. rewrite Hf. left. reflexivity.
    + destruct pre; discriminate Htr.
  - intros Hf tr f Hin.
    destruct (nec_s_old_or_earned s0 tr f Hin) as [Hold | Hear]; [| exact Hear].
    rewrite Hf in Hold. destruct Hold.
Qed.

(* Earned commitment provenance needs only the empty table (or a stale
   one); with a live fact at the start it fails. *)
Theorem nec_s_commitment_provenance_needs_table :
  ~ (forall s0 pre p c, chan (core_of s0) = None -> cert s0 = false ->
       commit_ok (core_of (run pre s0)) p c = true ->
       exists pre1 mid, pre = pre1 ++ CHECK p c :: mid).
Proof.
  intro H. destruct (H nec_s_fact_set [] PZero CA eq_refl eq_refl eq_refl)
    as [pre1 [mid Htr]].
  destruct pre1; discriminate Htr.
Qed.

Print Assumptions nec_s_clean_conjuncts_each_buy_one.
Print Assumptions nec_s_floor_two.
Print Assumptions nec_s_min_cost_needs_flag_down.
Print Assumptions nec_s_min_cost_needs_empty_channel.
Print Assumptions nec_s_min_cost_needs_empty_table.
Print Assumptions nec_s_stale_commitment_provenance.
Print Assumptions nec_s_stale_certification_provenance.
Print Assumptions nec_s_stale_min_cost.
Print Assumptions nec_s_clean_is_stale.
Print Assumptions nec_s_floor3_iff.
Print Assumptions nec_s_witness_from_every_clean_start.
Print Assumptions nec_s_clean_certifiable_iff_untrapped.
Print Assumptions nec_s_soundness_from_sound.
Print Assumptions nec_s_clean_is_sound.
Print Assumptions nec_s_soundness_needs_live_half.
Print Assumptions nec_s_soundness_needs_no_future_half.
Print Assumptions nec_s_sound_not_necessary.
Print Assumptions nec_s_stale_fact_false.
Print Assumptions nec_s_soundness_needs_live_version.
Print Assumptions nec_s_no_forging_iff.
Print Assumptions nec_s_commitment_provenance_needs_table.
