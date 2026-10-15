(** UMachInOrderUP.v: the IN-ORDER form of clause (2) for U_P.

    UP_in_order: for every computably presented machine Mp, presentation pc
    and start s0 there is ONE function f with f n < f (S n) for every n,
    such that, for every n the driver reaches without having stopped before,
    at host time f n counter RB of the host decodes to the state of Mp after
    n steps, the host ledger is Mp's ledger plus the surcharge of
    Presented.v, and the host flag is Mp's latch.

    The chain is two-level: Mp's step n -> the compiled guest's run length
    N_n (CompilerGuestRun's cg_ypoint, strictly increasing because each
    phase is a progress) -> U_P's host time for guest length N_n
    (UniversalPSim's pu_rel, strictly increasing because each guest step is
    at least one host step).

    UP_meets_strong: U_P meets UMachDef.universal_thiele (in-order rendering)
    with surcharge bound 3.                                                *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatPresented.
Require Import Kernel.UMachMeetsUP.
Require Import Kernel.UMachInOrderGen.
Require Import Kernel.UMachInOrderU.
Require Import Kernel.UniversalPCodes.
Require Import Kernel.UniversalPBridge.
Require Import Kernel.UniversalPLayout.
Require Import Kernel.UniversalPPhases.
Require Import Kernel.UniversalPSim.
Require Import Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal.
Require Import Kernel.CompilerGuest.
Require Import Kernel.CompilerGuestRun.
Require Import Kernel.CompilerChecker.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Section UP.
Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.
Variable s0 : T.cs_state (pm_sys Mp).

Local Notation Q := (cg_guest Mp pc).
Local Notation b := (pu_guest_b Mp pc s0).
Local Notation Y N := (pu_grun (cg_guest Mp pc) 0 (pu_guest_b Mp pc s0) N).
Local Notation Hh t := (pu_host_at Mp pc s0 t).

(* One driver step is a positive number of guest steps. *)
Lemma ystep : forall n N, cg_ypoint Mp pc s0 n N ->
  pm_next Mp (presented_run Mp s0 n) <> None ->
  exists q, 0 < q /\ cg_ypoint Mp pc s0 (S n) (N + q).
Proof.
  intros n N (x & Hinv & Hpc & Hsim) Hn.
  destruct (pm_next Mp (presented_run Mp s0 n)) as [i |] eqn:E; [| congruence].
  destruct (cg_x_step Mp pc s0 n x i Hinv E) as (x' & Hinv' & Hx).
  destruct (cg_y_phase Mp pc 2 x 2 x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
  exists q. split; [exact Hq |]. exists x'. split; [exact Hinv' |].
  rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma ypoint_live : forall n N, cg_ypoint Mp pc s0 n N -> ~ E.halted Q (E.core_of (Y N)).
Proof. intros n N H. exact (cg_point_live Mp pc s0 n N H). Qed.

(* Before a matching length, the guest has not stopped. *)
Lemma before_live : forall N q, ~ E.halted Q (E.core_of (Y (N + q))) ->
  forall j, j <= q -> ~ E.halted Q (E.core_of (Y (N + j))).
Proof.
  intros N q Hq j Hj Hh. apply Hq.
  assert (E : Y (N + q) = Y (N + j)).
  { unfold pu_grun. apply cg_run_prog_stay; [exact Hh | lia]. }
  rewrite E. exact Hh.
Qed.

(* q live guest steps are at least q host steps, and keep the relation. *)
Lemma host_steps : forall q N t,
  pu_rel Q (Y N) (Hh t) ->
  (forall j, j <= q -> ~ E.halted Q (E.core_of (Y (N + j)))) ->
  exists t', t + q <= t' /\ pu_rel Q (Y (N + q)) (Hh t').
Proof.
  induction q as [| q IH]; intros N t R Hl.
  - exists t. replace (N + 0) with N by lia. split; [lia | exact R].
  - destruct (IH N t R (fun j Hj => Hl j ltac:(lia))) as (t1 & Ht1 & R1).
    destruct (pu_U_step _ _ _ R1) as [[Hhalt _] | [_ (n & h' & Hr & Hres)]].
    + exfalso. exact (Hl q ltac:(lia) Hhalt).
    + assert (Hg : Y (N + S q) = E.step Q (Y (N + q))).
      { replace (N + S q) with (S (N + q)) by lia. unfold pu_grun. apply pu_grun_succ. }
      assert (Ht : Hh (t1 + S n) = h').
      { unfold pu_host_at. rewrite pu_hrun_add. exact Hr. }
      destruct Hres as [R' | [He _]].
      * exists (t1 + S n). split; [lia |]. rewrite Hg, Ht. exact R'.
      * exfalso. apply (Hl (S q) ltac:(lia)). rewrite Hg. apply pu_ghalted_trap. exact He.
Qed.

(* ---------------------------------------------------------------- *)
(* The ingredients of UMachInOrderGen.                                    *)
(* ---------------------------------------------------------------- *)

Definition iP : pinst := existT _ Mp (pc, s0).

Definition Lp (n : nat) : Prop := live_before (C:=presented_class) iP n.

Definition codeq (o : option (T.cs_state (pm_sys Mp))) (s : T.cs_state (pm_sys Mp)) : bool :=
  match o with Some s' => Nat.eqb (pm_scode Mp s') (pm_scode Mp s) | None => false end.

Lemma codeq_iff : forall o s, codeq o s = true <-> o = Some s.
Proof.
  intros [s' |] s; simpl; [| split; discriminate].
  rewrite Nat.eqb_eq. split; [intros H; f_equal; apply presented_scode_inj; exact H |].
  intros H. injection H as ->. reflexivity.
Qed.

Definition Dp (n t : nat) : Prop :=
  codeq (pu_decode Mp (hv (Hh t) pu_RB)) (presented_run Mp s0 n) = true /\
  M.mu (Hh t) = mledger Mp s0 n + surcharge Mp s0 n /\
  M.cert (Hh t) = mlatch Mp s0 n.

Lemma Dp_dec : forall n t, {Dp n t} + {~ Dp n t}.
Proof.
  intros n t. unfold Dp.
  destruct (Bool.bool_dec (codeq (pu_decode Mp (hv (Hh t) pu_RB)) (presented_run Mp s0 n)) true);
  destruct (Nat.eq_dec (M.mu (Hh t)) (mledger Mp s0 n + surcharge Mp s0 n));
  destruct (Bool.bool_dec (M.cert (Hh t)) (mlatch Mp s0 n)); (left; auto; fail) || (right; tauto).
Defined.

Definition Rp (n t : nat) : Prop :=
  exists N, cg_ypoint Mp pc s0 n N /\ pu_rel Q (Y N) (Hh t).

Lemma Lp_next : forall n, Lp (S n) -> pm_next Mp (presented_run Mp s0 n) <> None.
Proof.
  intros n Hl X. apply (Hl n); [lia |]. unfold UMachDef.grun. simpl gnext.
  rewrite (pgr iP n). exact X.
Qed.

Lemma Lp_all : forall n, Lp n -> forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None.
Proof.
  intros n Hl m Hm X. apply (Hl m Hm). unfold UMachDef.grun. simpl gnext.
  rewrite (pgr iP m). exact X.
Qed.

Lemma Rp_D : forall n t, Lp n -> Rp n t -> Dp n t.
Proof.
  intros n t _ (N & Hp & [sg [rho R]]).
  destruct (cg_point_facts Mp pc s0 n N Hp) as (_ & _ & Hd & Hmu & Hc & _).
  unfold Dp. rewrite (pu_R_rb _ _ _ _ _ R), (pu_rw_mu _ _ _ _ _ R), (pu_rw_cert _ _ _ _ _ R).
  split; [| split].
  - apply codeq_iff. unfold pu_decode. exact Hd.
  - exact Hmu.
  - exact Hc.
Qed.

Lemma Rp_0 : Lp 0 -> exists t, Rp 0 t.
Proof.
  intros _. destruct (cg_y_head Mp pc s0 0 (fun m Hm => ltac:(lia))) as (N & _ & Hp).
  destruct (host_steps N 0 0 (ex_intro _ [] (ex_intro _ None (pu_hload_rel Q 0 b))))
    as (t & _ & R).
  - intros j Hj. exact (before_live 0 N (ypoint_live 0 N Hp) j Hj).
  - exists t, N. split; [exact Hp | exact R].
Qed.

Lemma Rp_S : forall n t, Lp (S n) -> Rp n t -> exists t', t < t' /\ Rp (S n) t'.
Proof.
  intros n t Hl (N & Hp & R).
  destruct (ystep n N Hp (Lp_next n Hl)) as (q & Hq & Hp').
  destruct (host_steps q N t R (before_live N q (ypoint_live (S n) (N + q) Hp')))
    as (t' & Ht' & R').
  exists t'. split; [lia |]. exists (N + q). split; [exact Hp' | exact R'].
Qed.

Theorem UP_in_order :
  exists f : nat -> nat, (forall n, f n < f (S n)) /\
    (forall n, (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
       pu_decode Mp (hv (Hh (f n)) pu_RB) = Some (presented_run Mp s0 n) /\
       M.mu (Hh (f n)) = mledger Mp s0 n + surcharge Mp s0 n /\
       M.cert (Hh (f n)) = mlatch Mp s0 n).
Proof.
  destruct (in_order Lp (fun n => live_dec presented_class iP n)
              (fun n => live_prev presented_class iP n) Dp Dp_dec Rp Rp_D Rp_0 Rp_S)
    as (f & Hinc & HD).
  exists f. split; [exact Hinc |]. intros n Hn.
  assert (Hl : Lp n).
  { intros m Hm X. apply (Hn m Hm). unfold UMachDef.grun in X. simpl gnext in X.
    rewrite (pgr iP m) in X. exact X. }
  destruct (HD n Hl) as (Hd & Hmu & Hc). split; [apply codeq_iff; exact Hd |]. auto.
Qed.

End UP.

(* ================================================================= *)
(* U_P meets the in-order rendering of the plain definition, K = 3.   *)
(* ================================================================= *)

Theorem UP_meets_strong :
  universal_thiele presented_class UP_host
    (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3.
Proof.
  exists U_P, (fun i => pu_host_start (projT1 i) (fst (projT2 i)) (snd (projT2 i))),
         (fun i h => pu_decode (projT1 i) (hv h pu_RB)).
  intros [Mp [pc s0]]. split; [| split].
  - (* clause (1), as in UMachMeetsUP *)
    unfold clause1. simpl fst; simpl snd; simpl projT1. split.
    + intros [n Hn]. simpl in Hn. rewrite UP_hr in Hn.
      destruct (proj1 (presented_universal_halting Mp pc s0) (ex_intro _ n Hn)) as [m Hm].
      exists m. unfold UMachDef.grun. simpl. rewrite pgr. exact Hm.
    + intros [m Hm]. unfold UMachDef.grun in Hm. simpl in Hm.
      rewrite (pgr (existT _ Mp (pc, s0))) in Hm.
      destruct (proj2 (presented_universal_halting Mp pc s0) (ex_intro _ m Hm)) as [n Hn].
      exists n. simpl. rewrite UP_hr. exact Hn.
  - destruct (UP_in_order Mp pc s0) as (f & Hinc & Hpts).
    exists f. split; [intros m _; apply Hinc |].
    intros m Hl.
    assert (Hl' : forall k, k < m -> pm_next Mp (presented_run Mp s0 k) <> None).
    { intros k Hk. pose proof (Hl k Hk) as X. unfold UMachDef.grun in X. simpl in X.
      rewrite (pgr (existT _ Mp (pc, s0))) in X. exact X. }
    destruct (Hpts m Hl') as (Hd & Hmu & Hc).
    unfold match_at. simpl hP in *. rewrite UP_hr.
    pose proof (UP_hl U_P (f m) (pu_host_start Mp pc s0)) as Hh.
    unfold pu_host_at, pu_hrun in Hd, Hmu, Hc. fold (pu_host_start Mp pc s0) in Hd, Hmu, Hc.
    split; [| split].
    + simpl. rewrite Hd. unfold pobs. unfold UMachDef.grun. simpl.
      rewrite (pgr (existT _ Mp (pc, s0))). reflexivity.
    + simpl. rewrite Hc. symmetry. apply (pglat (existT _ Mp (pc, s0))).
    + exists (surcharge Mp s0 m). split.
      * unfold surcharge. destruct (mlatch Mp s0 m); lia.
      * unfold gledger. simpl gstart. rewrite (pgl (existT _ Mp (pc, s0))).
        assert (H0 : M.mu (pu_host_start Mp pc s0) = 0) by reflexivity. simpl in *. lia.
  - intros n. apply clause3_free.
Qed.

Print Assumptions UP_in_order.
Print Assumptions UP_meets_strong.
