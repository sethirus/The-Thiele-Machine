(** SmFixedPoint.v: Kleene's recursion theorem for programs of the host
    machine, up to the record.

    SmKleene.v (sm_kleene) gives, for a map F of host programs computed by a
    host program T, a program e that computes the same partial function as
    F e. Its ledger, flag, fact table and channel are those of an evaluator,
    not of F e. Here the evaluator replays the record.

    The program e is VG of SmFixed.v with its own number loaded into
    register 2 (s-m-n, as in SmKleene.v). On x, VG runs five Minsky blocks,
    one for each of five numbers about the final record of the program
    F e on x (SmTally.v):

      m_0   register 0
      m_1   the number of facts
      m_2   the commits the replay pays for
      m_3   the certifies the replay pays for (0 or 1)
      m_4   1 if the trap latch is up, else 0

    Each block simulates F e on x on plain data inside the Minsky machine;
    T is simulated there too, as pure computation. Then VG pays: m_1
    successful CHECK moves, m_2 COMMIT moves, m_3 CERTIFY moves, writes m_0
    into register 0, and, if m_4 is 1, runs a CHECK that fails and traps.

    What is proved: the two programs agree, on every input on which either
    stops, on whether they stop, on register 0, on the trap latch, on the
    ledger exactly (surcharge 0), on the flag, on how many facts they hold
    and on whether the channel is empty [sm2_kleene_obs]. The record of e is
    earned by e's own CHECK, COMMIT, CERTIFY; no assumption is made about T
    (T may itself check, commit and certify: e does not run it, it
    simulates it).

    What is not proved, and is false in general: that e and F e agree on
    every register [sm2_no_exact] (SmNoExact.v), on the content of the
    facts, or on the order in which the record is built. e builds its record
    after it has computed everything.

    Dependencies: as SmFixed.v, SmTally.v, SmTallyL.v and SmKleene.v. No
    axioms, no Admitted.                                                   *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks Sm.SmHostRice Sm.SmCodes Sm.SmInterp Sm.SmLoops Sm.SmBlock
  Sm.SmKleene Sm.SmTally Sm.SmTallyL Sm.SmChain Sm.SmFixed.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation srel := (sm_srel (prop := UC.hprop)).

(* ================================================================= *)
(* The relation.                                                      *)
(* ================================================================= *)

(* What the two final states are compared on: register 0, the trap latch,
   the ledger, the flag, how many facts, and whether the channel is empty. *)
Definition sm2_obs (s t : hstate) : Prop :=
  M.vals (M.core_of s) 0 = M.vals (M.core_of t) 0 /\
  M.err (M.core_of s) = M.err (M.core_of t) /\
  M.mu s = M.mu t /\ M.cert s = M.cert t /\
  length (M.facts (M.core_of s)) = length (M.facts (M.core_of t)) /\
  (M.chan (M.core_of s) = None <-> M.chan (M.core_of t) = None).

(* Two programs agree: on every input both run forever, or both stop and
   their final states agree on sm2_obs. *)
Definition sm2_obs_equiv (P Q : list hinstr) : Prop :=
  forall x,
    (forall s, hends P x s -> exists t, hends Q x t /\ sm2_obs s t) /\
    (forall t, hends Q x t -> exists s, hends P x s /\ sm2_obs s t).

(* ================================================================= *)
(* The run of sm_spec c V, in terms of the run of V.                  *)
(* ================================================================= *)

Lemma sm2_spec_ends : forall c V x,
  (forall s, hends (sm_spec c V) x s ->
     exists n, M.halted V (M.core_of (hrun_prog n V (sm_at1 (sm_spec_s1 c V x)))) /\
       srel (fun _ => True) c (length V) (hrun_prog n V (sm_at1 (sm_spec_s1 c V x))) s) /\
  (forall n, M.halted V (M.core_of (hrun_prog n V (sm_at1 (sm_spec_s1 c V x)))) ->
     exists s, hends (sm_spec c V) x s /\
       srel (fun _ => True) c (length V) (hrun_prog n V (sm_at1 (sm_spec_s1 c V x))) s).
Proof.
  intros c V x.
  destruct (sm_spec_phase1 c V x) as (_ & _ & _ & _ & _ & Hp1 & _).
  set (s1 := sm_spec_s1 c V x) in *.
  assert (Hrel : forall n, srel (fun _ => True) c (length V) (hrun_prog n V (sm_at1 s1))
                              (hrun_prog (c + n) (sm_spec c V) (sm_hstart x))).
  { intro n. rewrite sm_run_add. fold (sm_spec_s1 c V x). fold s1.
    apply (sm_block_run_final UC.hprop_eqb UC.heval (fun _ => True) (sm_spec c V) V c
             (sm_spec_embeds c V) (sm_within_all V) (sm_spec_length c V)).
    apply sm_at1_rel. exact Hp1. }
  split.
  - intros s [N [-> HN]].
    set (m := N - c).
    assert (Es : hrun_prog (c + m) (sm_spec c V) (sm_hstart x) = hrun_prog N (sm_spec c V) (sm_hstart x))
      by (apply sm_halted_after; [unfold m; lia | exact HN]).
    pose proof (Hrel m) as Hr. rewrite Es in Hr.
    exists m. split; [| exact Hr].
    unfold M.halted. destruct (M.next_instr V (M.core_of (hrun_prog m V (sm_at1 s1)))) eqn:Hn;
      [| reflexivity].
    exfalso. apply (sm_block_not_halted UC.hprop_eqb UC.heval (fun _ => True) (sm_spec c V) V c _ _
                      (sm_spec_embeds c V) (sm_within_all V) Hr); [congruence | exact HN].
  - intros n Hh.
    exists (hrun_prog (c + n) (sm_spec c V) (sm_hstart x)). split.
    + exists (c + n). split; [reflexivity |].
      apply (sm_block_halted (fun _ => True) (sm_spec c V) V c (M.core_of (hrun_prog n V (sm_at1 s1))));
        [apply sm_spec_embeds | apply sm_spec_length | apply (Hrel n) | exact Hh].
    + apply Hrel.
Qed.

(* The state a run of V starts from, after the prefix of sm_spec c V. *)
Lemma sm2_spec_start : forall c V x,
  sm2_vgstart x c (sm_at1 (sm_spec_s1 c V x)).
Proof.
  intros c V x.
  destruct (sm_spec_phase1 c V x) as (Hv1 & Hw1 & Hf1 & Hc1 & He1 & Hp1 & Hm1 & Hk1).
  set (s1 := sm_spec_s1 c V x) in *.
  unfold sm2_vgstart, sm_at1, M.goto. cbn [M.core_of M.pc M.err M.vals M.facts M.chan M.mu M.cert].
  refine (conj eq_refl (conj He1 (conj Hv1 (conj Hf1 (conj Hc1 (conj Hm1 Hk1)))))).
Qed.

(* ================================================================= *)
(* The two numbers of the program that has stopped.                   *)
(* ================================================================= *)

Lemma sm2_obs_of_numbers : forall (se sg : hstate),
  M.vals (M.core_of se) 0 = sm2_rcomp 0 sg ->
  (M.err (M.core_of se) = true <-> sm2_rcomp 4 sg = 1) ->
  M.mu se = sm2_rcomp 1 sg + sm2_rcomp 2 sg + sm2_rcomp 3 sg + sm2_rcomp 4 sg ->
  (M.cert se = true <-> 1 <= sm2_rcomp 3 sg) ->
  length (M.facts (M.core_of se)) = sm2_rcomp 1 sg ->
  (M.chan (M.core_of se) = None <-> sm2_rcomp 2 sg = 0) ->
  forall P x, hends P x sg -> sm2_obs se sg.
Proof.
  intros se sg Hv Hee Hmu Hce Hfl Hch P x Hends.
  destruct (sm2_final_numbers P x sg Hends) as (H16 & Hfe1 & Hee' & Hmu' & Hce' & Hch' & _ & _ & Hr1 & Hv0).
  unfold sm2_obs. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - rewrite Hv. exact Hv0.
  - apply Bool.eq_true_iff_eq. rewrite Hee, Hee'. reflexivity.
  - rewrite Hmu, Hr1. symmetry. exact Hmu'.
  - apply Bool.eq_true_iff_eq. rewrite Hce, Hce'. reflexivity.
  - rewrite Hfl, Hr1. reflexivity.
  - rewrite Hch, Hch'. reflexivity.
Qed.

(* ================================================================= *)
(* The theorem.                                                       *)
(* ================================================================= *)

(* The relation of one block, for the transformation numbered t. *)
Definition sm2_Rk (t k : nat) : nat -> nat -> nat -> Prop :=
  fun x c m => exists n, sm2_ev k t n x c = Some m.

Section Core.

Variables (R0 R1 R2 R3 R4 : nat -> nat -> nat -> Prop).
Variable b0 : sm2_bint R0.
Variable b1 : sm2_bint R1.
Variable b2 : sm2_bint R2.
Variable b3 : sm2_bint R3.
Variable b4 : sm2_bint R4.

Local Notation VG := (sm2_VG R0 R1 R2 R3 R4 b0 b1 b2 b3 b4).

(* If a program P stops on x, then sm_spec c VG stops on x, with the same
   record, as soon as the five blocks, run on x and c, produce the five
   numbers of P's final state. *)
Lemma sm2_fwd_core : forall c x (P : list hinstr) sg,
  hends P x sg ->
  R0 x c (sm2_rcomp 0 sg) -> R1 x c (sm2_rcomp 1 sg) -> R2 x c (sm2_rcomp 2 sg) ->
  R3 x c (sm2_rcomp 3 sg) -> R4 x c (sm2_rcomp 4 sg) ->
  exists se, hends (sm_spec c VG) x se /\ sm2_obs se sg.
Proof.
  intros c x P sg Hsg H0 H1 H2 H3 H4.
  destruct (sm2_final_numbers P x sg Hsg) as (H16 & Hfe1 & Hee & Hmu & Hce & Hch & Hbn & Hcb & Hr1 & Hv0).
  destruct (sm2_spec_ends c VG x) as [HendsA HendsB].
  assert (Hstart : sm2_vgstart x c (sm_at1 (sm_spec_s1 c VG x))) by apply sm2_spec_start.
  destruct (sm2_VG_forward R0 R1 R2 R3 R4 b0 b1 b2 b3 b4 x c (sm2_rcomp 0 sg) (sm2_rcomp 1 sg) (sm2_rcomp 2 sg)
              (sm2_rcomp 3 sg) (sm2_rcomp 4 sg) _ Hstart H0 H1 H2 H3 H4
              ltac:(rewrite Hr1; exact H16) Hfe1 (fun Hb => ltac:(rewrite Hr1; exact (Hbn Hb))) Hcb)
    as (u' & Rr & Hh & Vo & Ee & Mu & Ce & Fl & Ch).
  destruct (sm2_RR_run _ _ _ Rr) as [N HN].
  assert (HhN : M.halted VG (M.core_of (hrun_prog N VG (sm_at1 (sm_spec_s1 c VG x)))))
    by (rewrite HN; exact Hh).
  destruct (HendsB N HhN) as (se & Hse & Hrel).
  exists se. split; [exact Hse |].
  destruct Hrel as ((Hv & _ & Hf & Hc & He & _) & Hm & Hk').
  rewrite HN in Hv, Hf, Hc, He, Hm, Hk'.
  apply (sm2_obs_of_numbers se sg) with (P := P) (x := x); try exact Hsg.
  - rewrite <- Hv. exact Vo.
  - rewrite <- He. exact Ee.
  - rewrite <- Hm. exact Mu.
  - rewrite <- Hk'. exact Ce.
  - rewrite <- Hf. exact Fl.
  - rewrite <- Hc. exact Ch.
Qed.

(* If sm_spec c VG stops on x, then the first block computes something. *)
Lemma sm2_bwd_core : forall c x se,
  hends (sm_spec c VG) x se -> exists m, R0 x c m.
Proof.
  intros c x se Hse.
  destruct (sm2_spec_ends c VG x) as [HendsA HendsB].
  destruct (HendsA se Hse) as (n & Hh & Hrel).
  exact (sm2_VG_halt R0 R1 R2 R3 R4 b0 b1 b2 b3 b4 x c _ (sm2_spec_start c VG x) n Hh).
Qed.

End Core.

Theorem sm2_kleene_obs : forall (F : list hinstr -> list hinstr) (T : list hinstr),
  sm_computes_map T F -> exists e, sm2_obs_equiv e (F e).
Proof.
  intros F T HT.
  set (t := sm_hcode T).
  assert (HB : forall k, inhabited (sm2_bint (sm2_Rk t k))).
  { intro k. apply sm2_bint_of_MMA. exact (sm2_ev_MMA k t). }
  destruct (HB 0) as [b0]. destruct (HB 1) as [b1]. destruct (HB 2) as [b2].
  destruct (HB 3) as [b3]. destruct (HB 4) as [b4].
  pose (VG := sm2_VG (sm2_Rk t 0) (sm2_Rk t 1) (sm2_Rk t 2) (sm2_Rk t 3) (sm2_Rk t 4) b0 b1 b2 b3 b4).
  pose (c0 := sm_hcode VG).
  assert (HVG : sm_hdecode c0 = VG) by (unfold c0; apply sm_hdecode_hcode).
  pose (e := sm_spec c0 VG).
  assert (Hcode : sm_kspec c0 = sm_hcode e) by (rewrite sm_kspec_code, HVG; reflexivity).
  assert (Hchar : forall k x m, sm2_Rk t k x c0 m <->
                    exists s, hends (F e) x s /\ m = sm2_rcomp k s).
  { intros k x m. unfold sm2_Rk. rewrite sm2_ev_spec. unfold t. rewrite sm_hdecode_hcode, Hcode.
    split.
    - intros [d [Hd [s [Hs Hm]]]].
      rewrite (sm_hfun_det UC.hprop_eqb UC.heval T _ d _ Hd (HT e)) in Hs.
      rewrite sm_hdecode_hcode in Hs. exists s. split; assumption.
    - intros [s [Hs Hm]]. exists (sm_hcode (F e)). split; [exact (HT e) |].
      rewrite sm_hdecode_hcode. exists s. split; assumption. }
  assert (Hfwd : forall x sg, hends (F e) x sg -> exists se, hends e x se /\ sm2_obs se sg).
  { intros x sg Hsg.
    assert (Hk : forall k, sm2_Rk t k x c0 (sm2_rcomp k sg))
      by (intro k; apply Hchar; exists sg; split; [exact Hsg | reflexivity]).
    exact (sm2_fwd_core (sm2_Rk t 0) (sm2_Rk t 1) (sm2_Rk t 2) (sm2_Rk t 3) (sm2_Rk t 4) b0 b1 b2 b3 b4
             c0 x (F e) sg Hsg (Hk 0) (Hk 1) (Hk 2) (Hk 3) (Hk 4)). }
  exists e. intro x. split.
  - intros se Hse.
    destruct (sm2_bwd_core (sm2_Rk t 0) (sm2_Rk t 1) (sm2_Rk t 2) (sm2_Rk t 3) (sm2_Rk t 4)
                b0 b1 b2 b3 b4 c0 x se Hse) as [m Hm].
    destruct ((proj1 (Hchar 0 x m)) Hm) as (sg & Hsg & _).
    destruct (Hfwd x sg Hsg) as (se' & Hse' & Hobs).
    rewrite (sm_hends_unique UC.hprop_eqb UC.heval e x se' se Hse' Hse) in Hobs.
    exists sg. split; assumption.
  - intros sg Hsg. destruct (Hfwd x sg Hsg) as (se & Hse & Hobs). exists se. split; assumption.
Qed.

(* The new fixed point is a fixed point of the partial function too, so it
   gives sm_kleene back. *)
Corollary sm2_kleene_fun : forall (F : list hinstr -> list hinstr) (T : list hinstr),
  sm_computes_map T F -> exists e, forall x y, hfun e x y <-> hfun (F e) x y.
Proof.
  intros F T HT. destruct (sm2_kleene_obs F T HT) as [e He]. exists e. intros x y.
  destruct (He x) as [H1 H2]. split.
  - intros [s [Hs Hy]]. destruct (H1 s Hs) as (t & Ht & Hobs & _). exists t. split; [exact Ht |].
    rewrite <- Hobs. exact Hy.
  - intros [t [Ht Hy]]. destruct (H2 t Ht) as (s & Hs & Hobs & _). exists s. split; [exact Hs |].
    rewrite Hobs. exact Hy.
Qed.

Print Assumptions sm2_kleene_obs.
Print Assumptions sm2_kleene_fun.
