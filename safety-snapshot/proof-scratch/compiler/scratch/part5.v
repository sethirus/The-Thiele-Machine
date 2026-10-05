(* ================================================================= *)
(* The converse direction, stated for the source program.              *)
(* ================================================================= *)

(* The source program reaches HEAD with the invariant at n while the
   driver has not halted before step n. *)
Lemma cg_x_reach_head : forall n,
  (forall m, m < n -> pm_next M (presented_run M s0 m) <> None) ->
  exists x, cg_inv_head M pc s0 n x /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (2, x).
Proof.
  induction n as [| n IH]; intros Hn.
  - exact (cg_x_prologue M pc s0).
  - destruct (IH (fun m Hm => Hn m ltac:(lia))) as (x & Hinv & Hx).
    destruct (pm_next M (presented_run M s0 n)) as [i |] eqn:E;
      [| exfalso; exact (Hn n ltac:(lia) E)].
    destruct (cg_x_step M pc s0 n x i Hinv E) as (x' & Hinv' & Hx').
    exists x'. split; [exact Hinv' | eapply sss_progress_trans; [exact Hx | exact Hx']].
Qed.

(* At HALTB the source program has no step. *)
Lemma cg_x_halted : forall x st,
  ~ sss_step (cg_xstep K R) (1, SRC) (cg_HALTB M pc, x) st.
Proof.
  intros x st (k0 & l & I & r0 & d & HP & Hst & Hs).
  assert (HI : (cg_HALTB M pc, [I]) <sc (1, SRC)).
  { rewrite HP. injection Hst as Hi _. rewrite Hi. exists l, r0. split; reflexivity. }
  rewrite (subcode_cons_inj HI (cg_sc_halt M pc)) in Hs. inversion Hs.
Qed.

(* If some run of the guest halts, the source program, from its start,
   reaches HALTB (where it has no step) with the invariant at some n. *)
Theorem cg_source_halts_of_guest :
  (exists N, P.pr_halted cg_guest (G.core_of (Yrun s0 N))) ->
  exists n x, cg_inv_head M pc s0 n x /\ pm_next M (presented_run M s0 n) = None /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (cg_HALTB M pc, x) /\
    forall st, ~ sss_step (cg_xstep K R) (1, SRC) (cg_HALTB M pc, x) st.
Proof.
  intros H. apply cg_guest_halting_iff in H. destruct H as [n Hn].
  destruct (cg_first_halt (S n)) as [Hb | (h & _ & E & Hb)];
    [exfalso; exact (Hb n ltac:(lia) Hn) |].
  destruct (cg_x_reach_head h Hb) as (x & Hinv & Hx).
  destruct (cg_x_stop M pc s0 h x Hinv E) as (x' & Hinv' & Hx').
  exists h, x'. split; [exact Hinv' |]. split; [exact E |].
  split; [eapply sss_progress_trans; [exact Hx | exact Hx'] | apply cg_x_halted].
Qed.

(* If some run of the guest raises the flag, the source program, from its
   start, reaches HEAD or HALTB with the certified flag of its record up. *)
Theorem cg_source_certifies_of_guest :
  (exists N, G.cert (Yrun s0 N) = true) ->
  exists n i x, (i = 2 \/ i = cg_HALTB M pc) /\ cg_inv_head M pc s0 n x /\
    cg_a_cert (snd x) = true /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (i, x).
Proof.
  intros H. apply cg_guest_flag_iff in H. destruct H as [n Hn].
  destruct (cg_first_halt n) as [Hb | (h & Hh & E & Hb)].
  - destruct (cg_x_reach_head n Hb) as (x & [He Ha] & Hx).
    exists n, 2, x. split; [left; reflexivity |]. split; [split; assumption |].
    split; [| exact Hx]. rewrite Ha. cbn [cg_a_cert].
    apply presented_mlatch_iff. exists n. auto.
  - destruct (cg_x_reach_head h Hb) as (x & Hinv & Hx).
    destruct (cg_x_stop M pc s0 h x Hinv E) as (x' & [He Ha] & Hx').
    exists h, (cg_HALTB M pc), x'. split; [right; reflexivity |]. split; [split; assumption |].
    split; [| eapply sss_progress_trans; [exact Hx | exact Hx']].
    rewrite Ha. cbn [cg_a_cert]. apply presented_mlatch_iff. exists h. split; [lia |].
    destruct (presented_halted_stable M s0 h n E ltac:(lia)) as [Hr _].
    rewrite <- Hr. exact Hn.
Qed.

