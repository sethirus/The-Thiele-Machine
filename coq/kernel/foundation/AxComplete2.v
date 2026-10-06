(** AxComplete2: what every Thiele-complete axis machine has.

    All of these are consequences of the definition in AxComplete, for every
    machine and every interface that witnesses it.

      ax_flag_view_complete       certification is one tap: the bit "the record
                                  has left the floor" gives a machine that is
                                  Thiele-complete in the book's sense.
      ax_tc_certificate_three     reaching any point not below the floor
                                  costs at least 3, and so does reaching any
                                  point that stands above such a point.
      ax_tc_every_point_priced    the same, stated for a point a.
      ax_tc_committed_claim_true  the claim a certificate stands on held when it
                                  was checked and when it was committed.
      ax_tc_collision             one clean start, two runs, the same window of
                                  the shadow: the record of one stands at the
                                  point of a true claim and the record of the
                                  other sits at the floor; ledgers differ by 3.
      ax_tc_independence          no function of the shadow gives the record,
                                  no function of the shadow gives the ledger.
      ax_tc_every_window_printed  every shadow state is the shadow of a state
                                  at the floor, one free move from a clean
                                  start.
      ax_tc_conservative          compiled counter instructions act on the
                                  shadow exactly as the counter machine does
                                  and leave the record and the ledger alone.
      ax_tc_no_verifier           no sound and complete verifier reads the bare
                                  transcript for "the record has reached a",
                                  for any point a that a true claim stands
                                  above and that is not below the floor. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxLatch AxComplete.
Require Minimal.ThieleComplete.
Require Minimal.ThieleCompleteWindow.
Require Minimal.VerifierSmall.
Module T := Minimal.ThieleComplete.
Module W := Minimal.ThieleCompleteWindow.
Module V := Minimal.VerifierSmall.

Section Cons.

Context {A : Type} {P : BPre A} {AM : amachine A P} (I : ax_interface AM).
Hypothesis HC : ax_tc_with I.

Local Notation rc := (am_rec AM).
Local Notation fl := (axi_floor I).

Definition ax_window (s : am_state AM) : T.cm_conf := T.ub_window (axi_base I) s.

Lemma flag_fn_Hr : forall s, ax_flag_fn I s = true <-> ~ bp_le P (rc s) fl.
Proof.
  intro s. unfold ax_flag_fn, bp_le.
  destruct (bp_leb A P (rc s) fl); simpl; split; intro H; try discriminate; try reflexivity.
  exfalso. apply H. reflexivity.
Qed.

Lemma flag_fn_false : forall s, ax_flag_fn I s = false -> bp_le P (rc s) fl.
Proof.
  intros s H. unfold ax_flag_fn in H. unfold bp_le.
  destruct (bp_leb A P (rc s) fl) eqn:E; [reflexivity |]. simpl in H. discriminate.
Qed.

(** Certification is one tap. *)
Theorem ax_flag_view_complete : T.thiele_complete_with (ax_ti_pt I (ax_flag_fn I)).
Proof. exact (ax_pt_view_complete I HC (ax_flag_fn I) flag_fn_Hr). Qed.

Lemma rm_eq : forall r tr, T.record_moves (ax_ti_pt I r) tr = ax_record_moves I tr.
Proof. intros r tr. induction tr as [| m tr IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Theorem ax_tc_certificate_three : forall s0 tr,
  axi_clean I s0 -> ~ bp_le P (rc (am_run AM tr s0)) fl ->
  ax_record_moves I tr >= 3 /\ axi_ledger I (am_run AM tr s0) >= axi_ledger I s0 + 3.
Proof.
  intros s0 tr Hcl Hn.
  assert (Hflag : T.m_record (am_pt AM (ax_flag_fn I)) (T.run (am_pt AM (ax_flag_fn I)) tr s0) = true).
  { simpl. rewrite run_pt. apply flag_fn_Hr. exact Hn. }
  pose proof (T.certificate_costs_three _ (ax_ti_pt I (ax_flag_fn I)) ax_flag_view_complete
                s0 tr Hcl Hflag) as [H1 H2].
  rewrite rm_eq in H1. simpl in H2. rewrite run_pt in H2. split; assumption.
Qed.

(** Every point not below the floor is priced at 3. *)
Theorem ax_tc_every_point_priced : forall a, ~ bp_le P a fl ->
  forall s0 tr, axi_clean I s0 -> bp_le P a (rc (am_run AM tr s0)) ->
  ax_record_moves I tr >= 3 /\ axi_ledger I (am_run AM tr s0) >= axi_ledger I s0 + 3.
Proof.
  intros a Ha s0 tr Hcl Hle. apply ax_tc_certificate_three; [exact Hcl |].
  intro H. apply Ha. eapply bp_le_trans; [exact Hle | exact H].
Qed.

(** The claim a certificate stands on held when it was checked and held again
    when it was committed. *)
Theorem ax_tc_committed_claim_true : forall s0 tr,
  axi_clean I s0 -> ~ bp_le P (rc (am_run AM tr s0)) fl ->
  exists pre c chk mid1 cmt rest,
    tr = pre ++ chk :: mid1 ++ cmt :: rest /\
    axi_kind I chk = T.KCheck c /\ axi_kind I cmt = T.KCommit c /\
    axi_meaning I c (am_run AM pre s0) /\
    axi_meaning I c (am_run AM (pre ++ chk :: mid1) s0).
Proof.
  intros s0 tr Hcl Hn.
  assert (Hflag : T.m_record (am_pt AM (ax_flag_fn I)) (T.run (am_pt AM (ax_flag_fn I)) tr s0) = true).
  { simpl. rewrite run_pt. apply flag_fn_Hr. exact Hn. }
  destruct (T.committed_claim_holds _ (ax_ti_pt I (ax_flag_fn I)) ax_flag_view_complete
              s0 tr Hcl Hflag) as [pre [c [chk [mid1 [cmt [rest [Htr [Hk1 [Hk2 [Hm1 Hm2]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, rest. rewrite !run_pt in *.
  split; [exact Htr |]. split; [exact Hk1 |]. split; [exact Hk2 |].
  split; [exact Hm1 | exact Hm2].
Qed.

(** ** The shadow and its fibres *)

Lemma ax_window_run : forall is s, T.ub_live (axi_base I) s ->
  ax_window (am_run AM (map (T.ub_compile (axi_base I)) is) s)
    = W.cm_runl is (ax_window s) /\
  T.ub_live (axi_base I) (am_run AM (map (T.ub_compile (axi_base I)) is) s).
Proof.
  intros is s Hl.
  pose proof (W.base_run_window (ax_ti_pt I (fun _ => false)) is s Hl) as H.
  rewrite run_pt in H. exact H.
Qed.

Lemma ax_base_moves_blind : forall tr : list (am_move AM),
  Forall (fun m => axi_kind I m = T.KBase) tr ->
  forall s, rc (am_run AM tr s) = rc s /\ axi_ledger I (am_run AM tr s) = axi_ledger I s.
Proof.
  destruct HC as [[Hk [_ [Hbase _]]] [_ [[Hcost Hled] _]]].
  induction tr as [| m tr IH]; intros Hf s; [split; reflexivity |].
  inversion Hf as [| ? ? Hm Hrest]; subst.
  rewrite am_run_cons. destruct (IH Hrest (am_step AM s m)) as [Hr Hl].
  rewrite Hr, Hl, (Hbase s m Hm), Hled, Hcost. unfold ax_record_move. rewrite Hm.
  split; [reflexivity | lia].
Qed.

Lemma ax_base_run_blind : forall is s,
  rc (am_run AM (map (T.ub_compile (axi_base I)) is) s) = rc s /\
  axi_ledger I (am_run AM (map (T.ub_compile (axi_base I)) is) s) = axi_ledger I s.
Proof.
  intros is s. apply ax_base_moves_blind.
  destruct HC as [[Hk _] _]. apply Forall_forall. intros m Hm.
  apply in_map_iff in Hm as [i [<- _]]. apply Hk.
Qed.

(** One clean start, two runs, the same window of the shadow. The record of the
    first stands at the point of a true claim; the second sat at the floor. *)
Theorem ax_tc_collision :
  exists c a b tr1 tr2,
    axi_clean I (ax_load I a b) /\
    ax_window (am_run AM tr1 (ax_load I a b)) = ax_window (am_run AM tr2 (ax_load I a b)) /\
    bp_le P (axi_point I c) (rc (am_run AM tr1 (ax_load I a b))) /\
    rc (am_run AM tr2 (ax_load I a b)) = fl /\
    ~ bp_le P (axi_point I c) fl /\
    axi_ledger I (am_run AM tr2 (ax_load I a b)) = axi_ledger I (ax_load I a b) /\
    axi_ledger I (ax_load I a b) + 3 <= axi_ledger I (am_run AM tr1 (ax_load I a b)).
Proof.
  pose proof HC as HC'.
  destruct HC' as [[Hk [Hclean [Hbase Hgrow]]] [[Hfl _] [[Hcost Hled] Hnv]]].
  destruct Hnv as [c [chk [cmt [crt [Hk1 [Hk2 [Hk3 [Hiff [Hyes0 Hno]]]]]]]]].
  destruct Hyes0 as [a [b Hyes]].
  pose proof (ax_witness_nontrivial I HC c chk cmt crt Hiff Hno) as Hnt.
  set (s0 := ax_load I a b).
  set (tr1 := [chk; cmt; crt]).
  assert (Hcl : axi_clean I s0) by apply Hclean.
  assert (Hup : bp_le P (axi_point I c) (rc (am_run AM tr1 s0))) by (apply Hiff; exact Hyes).
  assert (Hnf : ~ bp_le P (rc (am_run AM tr1 s0)) fl).
  { intro H. apply Hnt. eapply bp_le_trans; [exact Hup | exact H]. }
  destruct (ax_tc_certificate_three s0 tr1 Hcl Hnf) as [_ Hl3].
  destruct (ax_window (am_run AM tr1 s0)) as [pc [x y]] eqn:Hw.
  destruct (W.cm_reach (1, (a, b)) pc x y) as [is His].
  exists c, a, b, tr1, (map (T.ub_compile (axi_base I)) is).
  destruct (ax_window_run is s0 (T.ub_load_live (axi_base I) a b)) as [Hw2 _].
  destruct (ax_base_run_blind is s0) as [Hr2 Hl2].
  unfold s0 in *.
  split; [exact Hcl |]. split.
  - rewrite Hw, Hw2. unfold ax_window, s0, ax_load. rewrite T.ub_load_window.
    symmetry. exact His.
  - split; [exact Hup |]. split; [rewrite Hr2; exact (Hfl s0 Hcl) |].
    split; [exact Hnt |]. split; [exact Hl2 | exact Hl3].
Qed.

(** The record is not a function of the shadow. *)
Theorem ax_tc_independence :
  ~ exists f : T.cm_conf -> A, forall a b tr,
      rc (am_run AM tr (ax_load I a b)) = f (ax_window (am_run AM tr (ax_load I a b))).
Proof.
  intros [f Hf].
  destruct ax_tc_collision as [c [a [b [tr1 [tr2 [_ [Hw [Hup [Hfloor [Hnt _]]]]]]]]]].
  apply Hnt. rewrite <- Hfloor, (Hf a b tr2), <- Hw, <- (Hf a b tr1). exact Hup.
Qed.

(** Nor is the ledger. *)
Theorem ax_tc_ledger_independence :
  ~ exists f : T.cm_conf -> nat, forall a b tr,
      axi_ledger I (am_run AM tr (ax_load I a b)) = f (ax_window (am_run AM tr (ax_load I a b))).
Proof.
  intros [f Hf].
  destruct ax_tc_collision as [c [a [b [tr1 [tr2 [_ [Hw [_ [_ [_ [Hl2 Hl1]]]]]]]]]]].
  pose proof (Hf a b tr1) as e1. pose proof (Hf a b tr2) as e2.
  rewrite Hw in e1. lia.
Qed.

(** Every state of the shadow is the shadow of a state at the floor, reached
    from a clean start by one move that costs nothing. *)
Theorem ax_tc_every_window_printed : forall s : am_state AM,
  exists a b m,
    axi_clean I (ax_load I a b) /\ axi_kind I m = T.KBase /\ am_cost AM m = 0 /\
    ax_window (am_step AM (ax_load I a b) m) = ax_window s /\
    bp_le P (rc (am_step AM (ax_load I a b) m)) fl /\
    axi_ledger I (am_step AM (ax_load I a b) m) = axi_ledger I (ax_load I a b).
Proof.
  intro s.
  destruct (W.complete_every_window_printed _ (ax_ti_pt I (ax_flag_fn I)) ax_flag_view_complete s)
    as [a [b [m [Hc [Hk [H0 [Hw [Hr Hl]]]]]]]].
  exists a, b, m. split; [exact Hc |]. split; [exact Hk |]. split; [exact H0 |].
  split; [exact Hw |]. split; [| exact Hl].
  assert (Hr' : ax_flag_fn I (am_step AM (ax_load I a b) m) = false) by exact Hr.
  apply flag_fn_false. exact Hr'.
Qed.

(** Compiled counter instructions act on the shadow as the counter machine
    does and leave the record and the ledger alone: the part of the machine
    that does not move along the axis is the classical machine. *)
Theorem ax_tc_conservative : forall is s, T.ub_live (axi_base I) s ->
  ax_window (am_run AM (map (T.ub_compile (axi_base I)) is) s) = W.cm_runl is (ax_window s) /\
  T.ub_live (axi_base I) (am_run AM (map (T.ub_compile (axi_base I)) is) s) /\
  rc (am_run AM (map (T.ub_compile (axi_base I)) is) s) = rc s /\
  axi_ledger I (am_run AM (map (T.ub_compile (axi_base I)) is) s) = axi_ledger I s.
Proof.
  intros is s Hl. destruct (ax_window_run is s Hl) as [H1 H2].
  destruct (ax_base_run_blind is s) as [H3 H4]. auto.
Qed.

(** And every counter program is run by it, halting included. *)
Theorem ax_tc_halting_correspondence : forall Pg a b,
  (exists n, T.cm_step Pg (T.cm_run n Pg (1, (a, b))) = None) <->
  (exists n, T.prog_halted (axi_base I) Pg (T.prog_run (axi_base I) n Pg (T.ub_load (axi_base I) a b))).
Proof. intros. exact (T.base_halting_correspondence (am_bare AM) (axi_base I) Pg a b). Qed.

(** ** No verifier reads the bare transcript. *)

Definition ax_bare := (nat * nat * T.cm_conf)%type.

Definition ax_bare_explains (s : am_state AM) (t : ax_bare) : Prop :=
  let '(a, b, w) := t in
  exists tr, s = am_run AM tr (ax_load I a b) /\ ax_window s = w.

Theorem ax_tc_no_verifier :
  exists c, forall x, bp_le P x (axi_point I c) -> ~ bp_le P x fl ->
    ~ exists Vf : ax_bare -> bool,
        V.ver_sound (fun s => bp_le P x (rc s)) ax_bare_explains Vf /\
        V.ver_complete (fun s => bp_le P x (rc s)) ax_bare_explains Vf.
Proof.
  destruct ax_tc_collision as [c [a [b [tr1 [tr2 [_ [Hw [Hup [Hfloor [Hnt _]]]]]]]]]].
  exists c. intros x Hx Hxf.
  apply (V.ver_collision_blocks (fun s => bp_le P x (rc s)) ax_bare_explains
           (a, b, ax_window (am_run AM tr1 (ax_load I a b)))
           (am_run AM tr1 (ax_load I a b)) (am_run AM tr2 (ax_load I a b))).
  - exists tr1. split; reflexivity.
  - exists tr2. split; [reflexivity | symmetry; exact Hw].
  - eapply bp_le_trans; [exact Hx | exact Hup].
  - simpl. rewrite Hfloor. exact Hxf.
Qed.

End Cons.

Print Assumptions ax_flag_view_complete.
Print Assumptions ax_tc_certificate_three.
Print Assumptions ax_tc_every_point_priced.
Print Assumptions ax_tc_committed_claim_true.
Print Assumptions ax_tc_collision.
Print Assumptions ax_tc_independence.
Print Assumptions ax_tc_ledger_independence.
Print Assumptions ax_tc_every_window_printed.
Print Assumptions ax_tc_conservative.
Print Assumptions ax_tc_halting_correspondence.
Print Assumptions ax_tc_no_verifier.
