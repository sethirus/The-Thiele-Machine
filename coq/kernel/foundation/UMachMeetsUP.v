(** UMachMeetsUP.v: U_P meets the weak (order-free) rendering of
    the plain definition with surcharge bound 3, from the
    presented_universal theorems of PresentedUniversal.v.                                          *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatPresented.
Require Import Kernel.UniversalPCodes.
Require Import Kernel.UniversalPBridge.
Require Import Kernel.UniversalPLayout.
Require Import Kernel.UniversalPSim.
Require Import Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Definition UP_host : host :=
  mk_host (@M.pu_state pu_hprop) (@M.pu_instr pu_hprop) (M.pu_exec pu_hprop_eqb pu_heval)
    (@M.pu_cost pu_hprop) (@M.cert pu_hprop)
    (fun s i => M.pu_multi_a2 pu_hprop_eqb pu_heval s i)
    (list (@M.pu_instr pu_hprop)) (fun P s => M.pu_next_instr P (M.core_of s)).

Lemma UP_hr : forall Q n s,
  hr (H:=UP_host) Q s n = M.pu_run_prog pu_hprop_eqb pu_heval n Q s.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [reflexivity |].
  simpl. unfold M.pu_step. destruct (M.pu_next_instr Q (M.core_of s)) eqn:E.
  - apply IH.
  - symmetry. apply M.pu_multi_run_prog_halted. exact E.
Qed.

Lemma UP_hl : forall Q n s,
  M.mu (M.pu_run_prog pu_hprop_eqb pu_heval n Q s) = M.mu s + hl (H:=UP_host) Q s n.
Proof.
  intros Q n. induction n as [| n IH]; intros s; [simpl; lia |].
  simpl. unfold M.pu_step. destruct (M.pu_next_instr Q (M.core_of s)) eqn:E.
  - rewrite IH. simpl. lia.
  - rewrite M.pu_multi_run_prog_halted by exact E. lia.
Qed.

Section Inst.
Variable i : pinst.
Local Notation Mp := (projT1 i).
Local Notation s0 := (snd (projT2 i)).

Lemma pgr : forall n s, gr (C:=presented_class) (i:=i) s n = presented_run Mp s n.
Proof.
  induction n as [| n IH]; intros s; [reflexivity |].
  simpl. destruct (pm_next (projT1 i) s); [apply IH | reflexivity].
Qed.

Lemma pgl : forall n s, gl (C:=presented_class) (i:=i) s n = mledger Mp s n.
Proof.
  induction n as [| n IH]; intros s; [reflexivity |].
  simpl. destruct (pm_next (projT1 i) s); [rewrite IH; reflexivity | reflexivity].
Qed.

Lemma glatch_iff : forall n s,
  glatch (C:=presented_class) (i:=i) s n = true <->
  exists m, m <= n /\ T.cs_cert (pm_sys Mp) (gr (C:=presented_class) (i:=i) s m) = true.
Proof.
  induction n as [| n IH]; intros s.
  - simpl. split; [intros H; exists 0; split; [lia | exact H] |].
    intros [m [Hm H]]. replace m with 0 in H by lia. exact H.
  - change (glatch s (S n)) with (glatch s n || gread presented_class i (gr s (S n))).
    rewrite orb_true_iff, IH. split.
    + intros [[m [Hm H]] | H].
      * exists m. split; [lia | exact H].
      * exists (S n). split; [lia | exact H].
    + intros [m [Hm H]]. destruct (Nat.eq_dec m (S n)) as [-> | Hne]; [right; exact H |].
      left. exists m. split; [lia | exact H].
Qed.

Lemma pglat : forall n, glat (C:=presented_class) i n = mlatch Mp s0 n.
Proof.
  intros n. apply Bool.eq_true_iff_eq. unfold glat. rewrite glatch_iff, presented_mlatch_iff.
  simpl gstart. split; intros [m [Hm H]]; exists m; (split; [exact Hm |]).
  - rewrite <- pgr. exact H.
  - rewrite pgr. exact H.
Qed.

End Inst.

Theorem UP_meets_weak :
  universal_thiele_weak presented_class UP_host
    (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 3.
Proof.
  exists U_P, (fun i => pu_host_start (projT1 i) (fst (projT2 i)) (snd (projT2 i))),
         (fun i h => pu_decode (projT1 i) (hv h pu_RB)).
  intros [Mp [pc s0]]. split; [| split].
  - unfold clause1. simpl fst; simpl snd; simpl projT1. split.
    + intros [n Hn]. simpl in Hn. rewrite UP_hr in Hn.
      destruct (proj1 (presented_universal_halting Mp pc s0) (ex_intro _ n Hn)) as [m Hm].
      exists m. unfold grun. simpl. rewrite pgr. exact Hm.
    + intros [m Hm]. unfold grun in Hm. simpl in Hm.
      rewrite (pgr (existT _ Mp (pc, s0))) in Hm.
      destruct (proj2 (presented_universal_halting Mp pc s0) (ex_intro _ m Hm)) as [n Hn].
      exists n. simpl. rewrite UP_hr. exact Hn.
  - intros m Hl.
    assert (Hl' : forall k, k < m -> pm_next Mp (presented_run Mp s0 k) <> None).
    { intros k Hk. pose proof (Hl k Hk) as X. unfold grun in X. simpl in X.
      rewrite (pgr (existT _ Mp (pc, s0))) in X. exact X. }
    destruct (presented_universal_points Mp pc s0 m Hl') as (t & Hd & Hmu & Hc).
    exists t. unfold match_at. simpl hP in *. rewrite UP_hr.
    pose proof (UP_hl U_P t (pu_host_start Mp pc s0)) as Hh.
    unfold pu_host_at, pu_hrun in Hd, Hmu, Hc. fold (pu_host_start Mp pc s0) in Hd, Hmu, Hc.
    split; [| split].
    + simpl. rewrite Hd. unfold pobs. unfold grun. simpl. rewrite (pgr (existT _ Mp (pc, s0))). reflexivity.
    + simpl. rewrite Hc. symmetry. apply (pglat (existT _ Mp (pc, s0))).
    + exists (surcharge Mp s0 m). split.
      * unfold surcharge. destruct (mlatch Mp s0 m); lia.
      * unfold gledger. simpl gstart. rewrite (pgl (existT _ Mp (pc, s0))).
        assert (H0 : M.mu (pu_host_start Mp pc s0) = 0) by reflexivity. simpl in *. lia.
  - intros n. apply clause3_free.
Qed.

Print Assumptions UP_meets_weak.
