(** AxDgPhase: the run of the program of AxDgPre.v, phase by phase.

    From the state the s-m-n prefix leaves (x in register 1, c in register 2,
    program counter 1, nothing else), the program

      A   moves x out of register 1 into RX;
      B   runs the MMA program, which leaves a bit in register 0 and its
          working counters dirty;
      C   empties registers 1 .. N-1;
      D   moves RX back into register 1;
      E   chooses.

    Each phase is a lemma about clean states (AxDgLoops.v).  The last lemma,
    [ax_dg_prelude], joins them.  It needs only the output of the MMA
    program: from the vector (0, 0, c, 0, ...) it computes the bit. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the multi-register host machine (the phases of the diagonal program), built for
   the content diagonal of AxDgFixed.v. That file connects it to the axis
   (AxCore.v); the host machine's link to the abstract record lives in
   UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmMMAHost Kernel.SmNoExact
  Kernel.SmHostRice Kernel.SmKleene.
From Minimal Require Import AxDgBlock.
From Kernel Require Import AxDgLoops AxDgPre.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

Section Phases.

Variable nn : nat.
Variable Pm : list (mm_instr (pos (S (S (S nn))))).
Variable yes no : list hinstr.

Local Notation V := (ax_dg_V nn Pm yes no).
Local Notation N := (ax_dg_N nn).
Local Notation RX := (ax_dg_RX nn).
Local Notation lp := (ax_dg_lp nn Pm).
Local Notation base := (ax_dg_base nn Pm).
Local Notation Ld := (ax_dg_Ld nn Pm).
Local Notation Le := (ax_dg_Le nn Pm).
Local Notation offN := (ax_dg_offN nn Pm).
Local Notation offY := (ax_dg_offY nn Pm no).

Lemma ax_dg_N_ge : 3 <= N.
Proof. unfold ax_dg_N. lia. Qed.

(** * Phase A: move x out of register 1 *)

Definition ax_dg_vA (x c : nat) : nat -> nat :=
  fun r => if Nat.eqb r 1 then 0 else if Nat.eqb r RX then x else if Nat.eqb r 2 then c else 0.

Lemma ax_dg_phaseA : forall x c s,
  ax_dg_clean s 1 (sm_in2 x c) ->
  exists n, ax_dg_clean (hrun_prog n V s) 4 (ax_dg_vA x c).
Proof.
  intros x c s Hs.
  pose proof ax_dg_N_ge as HN.
  assert (Hrx : RX <> 1) by (unfold ax_dg_RX; lia).
  assert (Hrx2 : RX <> 2) by (unfold ax_dg_RX; lia).
  assert (F1 : M.fetch V 1 = Some (M.INC RX)).
  { rewrite (ax_dg_fetch_A nn Pm yes no 1) by lia. reflexivity. }
  assert (F2 : M.fetch V 2 = Some (M.DEC 1 1)).
  { rewrite (ax_dg_fetch_A nn Pm yes no 2) by lia. reflexivity. }
  assert (F3 : M.fetch V 3 = Some (M.DEC RX 4)).
  { rewrite (ax_dg_fetch_A nn Pm yes no 3) by lia. reflexivity. }
  destruct (ax_dg_move V 1 1 RX (not_eq_sym Hrx) F1 F2 F3 _ s Hs) as [n Hn].
  exists n. refine (ax_dg_clean_ext _ _ _ _ _ Hn).
  intro r. unfold ax_dg_vA, M.upd, sm_in2.
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
    subst; try congruence; try lia.
Qed.

(** * Phase B: the MMA program *)

Definition ax_dg_vec (c : nat) : Vector.t nat (S (S (S nn))) :=
  Vector.append
    (Vector.cons nat 0 2 (Vector.cons nat 0 1 (Vector.cons nat c 0 (Vector.nil nat))))
    (Vector.const 0 nn).

Lemma ax_dg_phaseB : forall c x bit sA,
  ax_dg_clean sA 4 (ax_dg_vA x c) ->
  (exists c' (v' : Vector.t nat (2 + nn)),
     sss_output (@mma_sss (S (S (S nn)))) (1, Pm) (1, ax_dg_vec c)
       (c', Vector.cons nat bit (2 + nn) v')) ->
  exists n vB, ax_dg_clean (hrun_prog n V sA) (S base) vB /\ vB 0 = bit /\
               (forall r, N <= r -> vB r = ax_dg_vA x c r).
Proof.
  intros c x bit sA HsA Hout.
  pose proof ax_dg_N_ge as HN.
  pose proof HsA as (He & Hp & Hv & Hf & Hc & Hm & Hk).
  pose proof Hf as Hf0. pose proof Hc as Hc0.
  set (spre := M.mkst (M.mkcore (M.vals (M.core_of sA)) (M.vers (M.core_of sA)) 1 [] None false) 0 false : hstate).
  assert (HPre : forall i, In i (ax_dg_Pre nn Pm) -> M.plain i = true).
  { intros i Hi. destruct (ax_dg_mma_instr _ Pm i Hi) as (r & j & [-> | ->] & _); reflexivity. }
  (* the vector the program starts from *)
  assert (Hpos : forall p : pos (S (S (S nn))),
            M.vals (M.core_of spre) (pos2nat p) = vec_pos (ax_dg_vec c) p).
  { intro p. unfold ax_dg_vec. rewrite sm_v0_pos. simpl. rewrite Hv.
    pose proof (pos2nat_prop p) as Hlt. revert Hlt. generalize (pos2nat p). intros q Hlt.
    unfold ax_dg_vA, sm_in2.
    destruct (Nat.eqb_spec q 1) as [-> | H1]; [reflexivity |].
    destruct (Nat.eqb_spec q RX) as [E | H2]; [unfold ax_dg_RX, ax_dg_N in E; lia |].
    destruct (Nat.eqb_spec q 2); reflexivity. }
  pose proof (ax_dg_mma_out (S (S nn)) Pm (M.core_of spre) (ax_dg_vec c) bit eq_refl eq_refl Hpos) as Hmma.
  apply Hmma in Hout. clear Hmma.
  destruct Hout as [n0 [Hh0 Hv0]].
  rewrite <- sm_core_run in Hh0, Hv0.
  change (M.halted (ax_dg_Pre nn Pm) (M.core_of (hrun_prog n0 (ax_dg_Pre nn Pm) spre))) in Hh0.
  change (M.vals (M.core_of (hrun_prog n0 (ax_dg_Pre nn Pm) spre)) 0 = bit) in Hv0.
  (* the first stop *)
  assert (Hd : forall n, M.halted (ax_dg_Pre nn Pm) (M.core_of (hrun_prog n (ax_dg_Pre nn Pm) spre)) \/
                         ~ M.halted (ax_dg_Pre nn Pm) (M.core_of (hrun_prog n (ax_dg_Pre nn Pm) spre))).
  { intro n. unfold M.halted.
    destruct (M.next_instr (ax_dg_Pre nn Pm) (M.core_of (hrun_prog n (ax_dg_Pre nn Pm) spre))) eqn:E;
      [right; discriminate | left; reflexivity]. }
  destruct (sm_least _ Hd n0 Hh0) as [nh [Hnh Hmin]].
  assert (Hvh : M.vals (M.core_of (hrun_prog nh (ax_dg_Pre nn Pm) spre)) 0 = bit).
  { assert (Hle : nh <= n0).
    { destruct (le_lt_dec nh n0) as [H | H]; [exact H | exfalso; exact (Hmin n0 H Hh0)]. }
    pose proof (sm_halted_after UC.hprop_eqb UC.heval nh n0 (ax_dg_Pre nn Pm) spre Hle Hnh) as E.
    rewrite E in Hv0. exact Hv0. }
  assert (Hrel : sm_srel (fun _ => False) 3 (length (ax_dg_Pre nn Pm)) spre sA).
  { unfold sm_srel, sm_crel. simpl.
    refine (conj (conj _ (conj _ (conj _ (conj _ (conj _ _))))) (conj _ _)).
    - intro r. reflexivity.
    - intros r [].
    - symmetry. exact Hf.
    - symmetry. exact Hc.
    - symmetry. exact He.
    - rewrite Hp, ax_dg_rj_one. reflexivity.
    - symmetry. exact Hm.
    - symmetry. exact Hk. }
  pose proof (sm_block_run_mid UC.hprop_eqb UC.heval (fun _ => False) V (ax_dg_Pre nn Pm) 3
                (ax_dg_embeds_pre nn Pm yes no) (sm_mma_plain (S (S (S nn))) Pm _) nh spre sA Hrel
                (fun m Hm => Hmin m Hm)) as Hrun.
  destruct Hrun as ((Hv1 & _ & Hf1 & Hc1 & He1 & Hp1) & Hm1 & Hk1).
  destruct (ax_dg_plain_run _ HPre nh spre) as (Pf & Pc & Pe & Pm' & Pk).
  assert (Hpe : M.err (M.core_of (hrun_prog nh (ax_dg_Pre nn Pm) spre)) = false)
    by (rewrite Pe; reflexivity).
  pose proof (ax_dg_halted_out _ _ HPre Hnh Hpe) as Hout'.
  assert (Hpc : M.pc (M.core_of (hrun_prog nh V sA)) = S base).
  { rewrite Hp1, sm_rj_out by exact Hout'. rewrite ax_dg_lp_len. unfold ax_dg_base. lia. }
  exists nh, (fun r => M.vals (M.core_of (hrun_prog nh V sA)) r). split; [| split].
  - refine (conj _ (conj Hpc (conj (fun r => eq_refl) (conj _ (conj _ (conj _ _)))))).
    + rewrite <- He1. exact Hpe.
    + rewrite <- Hf1, Pf. reflexivity.
    + rewrite <- Hc1, Pc. reflexivity.
    + rewrite <- Hm1, Pm'. reflexivity.
    + rewrite <- Hk1, Pk. reflexivity.
  - simpl. rewrite <- Hv1. exact Hvh.
  - intros r Hr. rewrite <- Hv1.
    rewrite (sm2_prog_frame (ax_dg_Pre nn Pm) r).
    + simpl. rewrite Hv. reflexivity.
    + intros i Hi. destruct (ax_dg_mma_instr _ Pm i Hi) as (r' & j & [-> | ->] & Hr').
      * simpl. apply Nat.eqb_neq. unfold ax_dg_N in Hr. lia.
      * simpl. apply Nat.eqb_neq. unfold ax_dg_N in Hr. lia.
Qed.

(** * Phase C: empty registers 1 .. N-1 *)

Definition ax_dg_vC (vB : nat -> nat) : nat -> nat :=
  fun r => if (1 <=? r) && (r <=? N - 1) then 0 else vB r.

Lemma ax_dg_phaseC : forall s vB,
  ax_dg_clean s (S base) vB ->
  exists n, ax_dg_clean (hrun_prog n V s) Ld (ax_dg_vC vB).
Proof.
  intros s vB Hs. pose proof ax_dg_N_ge as HN.
  destruct (ax_dg_clears (N - 1) V base (fun i Hi => ax_dg_fetch_Cl nn Pm yes no i Hi) vB s Hs) as [n Hn].
  exists n. refine (ax_dg_clean_pc _ _ _ _ _ Hn). unfold ax_dg_Ld. lia.
Qed.

(** * Phase D: move RX back into register 1 *)

Definition ax_dg_vD (vC : nat -> nat) : nat -> nat :=
  M.upd (M.upd vC RX 0) 1 (vC 1 + vC RX).

Lemma ax_dg_phaseD : forall s vC,
  ax_dg_clean s Ld vC ->
  exists n, ax_dg_clean (hrun_prog n V s) Le (ax_dg_vD vC).
Proof.
  intros s vC Hs.
  assert (Hrx : RX <> 1) by (unfold ax_dg_RX, ax_dg_N; lia).
  assert (F1 : M.fetch V Ld = Some (M.INC 1)).
  { rewrite <- (Nat.add_0_r Ld). rewrite (ax_dg_fetch_D nn Pm yes no) by lia. reflexivity. }
  assert (F2 : M.fetch V (S Ld) = Some (M.DEC RX Ld)).
  { replace (S Ld) with (Ld + 1) by lia. rewrite (ax_dg_fetch_D nn Pm yes no) by lia. reflexivity. }
  assert (F3 : M.fetch V (S (S Ld)) = Some (M.DEC 1 (S (S (S Ld))))).
  { replace (S (S (S Ld))) with (Ld + 3) by lia.
    replace (S (S Ld)) with (Ld + 2) by lia. rewrite (ax_dg_fetch_D nn Pm yes no) by lia. reflexivity. }
  destruct (ax_dg_move V Ld RX 1 Hrx F1 F2 F3 vC s Hs) as [n Hn].
  exists n. refine (ax_dg_clean_pc _ _ _ _ _ Hn). unfold ax_dg_Le. lia.
Qed.

Lemma ax_dg_vD_eval : forall x c vB bit,
  vB 0 = bit -> (forall r, N <= r -> vB r = ax_dg_vA x c r) ->
  forall r, ax_dg_vD (ax_dg_vC vB) r = if Nat.eqb r 0 then bit else if Nat.eqb r 1 then x else 0.
Proof.
  intros x c vB bit H0 Hhi r. pose proof ax_dg_N_ge as HN.
  assert (HRXge : N <= RX) by (unfold ax_dg_RX; lia).
  assert (HC1 : ax_dg_vC vB 1 = 0).
  { unfold ax_dg_vC. replace ((1 <=? 1) && (1 <=? N - 1)) with true; [reflexivity |].
    symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia. }
  assert (HCRX : ax_dg_vC vB RX = x).
  { unfold ax_dg_vC. replace ((1 <=? RX) && (RX <=? N - 1)) with false.
    - rewrite (Hhi RX HRXge). unfold ax_dg_vA.
      destruct (Nat.eqb_spec RX 1); [unfold ax_dg_RX, ax_dg_N in *; lia |].
      rewrite Nat.eqb_refl. reflexivity.
    - symmetry. apply andb_false_iff. right. apply Nat.leb_gt. lia. }
  unfold ax_dg_vD, M.upd at 1. rewrite HC1, HCRX.
  destruct (Nat.eqb_spec r 1) as [-> | Hr1].
  - reflexivity.
  - unfold M.upd at 1. destruct (Nat.eqb_spec r RX) as [-> | Hr2].
    + destruct (Nat.eqb_spec RX 0); [unfold ax_dg_RX, ax_dg_N in *; lia |].
      destruct (Nat.eqb_spec RX 1); [congruence | reflexivity].
    + destruct (Nat.eqb_spec r 0) as [-> | Hr0].
      * unfold ax_dg_vC. simpl. exact H0.
      * unfold ax_dg_vC.
        destruct (le_lt_dec r (N - 1)) as [Hle | Hgt].
        -- replace ((1 <=? r) && (r <=? N - 1)) with true.
           ++ reflexivity.
           ++ symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
        -- replace ((1 <=? r) && (r <=? N - 1)) with false.
           ++ rewrite (Hhi r) by lia. unfold ax_dg_vA.
              destruct (Nat.eqb_spec r 1); [congruence |].
              destruct (Nat.eqb_spec r RX); [congruence |].
              destruct (Nat.eqb_spec r 2); [lia | reflexivity].
           ++ symmetry. apply andb_false_iff. right. apply Nat.leb_gt. lia.
Qed.

(** * Phase E: choose *)

Lemma ax_dg_phaseE0 : forall s v,
  ax_dg_clean s Le v -> v 0 = 0 ->
  ax_dg_clean (hstep V s) (S Le) v.
Proof.
  intros s v Hs H0. apply (ax_dg_step_dec_zero V s 0 (S offY) Le v Hs); [| exact H0].
  exact (ax_dg_fetch_E nn Pm yes no).
Qed.

Lemma ax_dg_phaseE1 : forall s v u,
  ax_dg_clean s Le v -> v 0 = S u ->
  ax_dg_clean (hstep V s) (S offY) (M.upd v 0 u).
Proof.
  intros s v u Hs H0. apply (ax_dg_step_dec_pos V s 0 (S offY) Le v u Hs); [| exact H0].
  exact (ax_dg_fetch_E nn Pm yes no).
Qed.

(** * The prelude *)

Theorem ax_dg_prelude : forall c x bit s0,
  (bit = 0 \/ bit = 1) ->
  (exists c' (v' : Vector.t nat (2 + nn)),
     sss_output (@mma_sss (S (S (S nn)))) (1, Pm) (1, ax_dg_vec c)
       (c', Vector.cons nat bit (2 + nn) v')) ->
  ax_dg_clean s0 1 (sm_in2 x c) ->
  exists n, ax_dg_clean (hrun_prog n V s0) (if Nat.eqb bit 0 then S offN else S offY) (sm_hin x).
Proof.
  intros c x bit s0 Hbit Hout H0.
  set (Rfin := fun s : hstate => ax_dg_clean s (if Nat.eqb bit 0 then S offN else S offY) (sm_hin x)).
  change (exists n, Rfin (hrun_prog n V s0)).
  apply (ax_dg_seq V s0 (fun s => ax_dg_clean s 4 (ax_dg_vA x c)) Rfin).
  { apply ax_dg_phaseA. exact H0. }
  intros sA HA.
  apply (ax_dg_seq V sA (fun s => exists vB, ax_dg_clean s (S base) vB /\ vB 0 = bit /\
                                      (forall r, N <= r -> vB r = ax_dg_vA x c r)) Rfin).
  { destruct (ax_dg_phaseB c x bit sA HA Hout) as (n & vB & H1 & H2 & H3). exists n, vB. auto. }
  intros sB (vB & HB & HB0 & HBhi).
  apply (ax_dg_seq V sB (fun s => ax_dg_clean s Ld (ax_dg_vC vB)) Rfin).
  { apply ax_dg_phaseC. exact HB. }
  intros sC HC.
  apply (ax_dg_seq V sC (fun s => ax_dg_clean s Le (ax_dg_vD (ax_dg_vC vB))) Rfin).
  { apply ax_dg_phaseD. exact HC. }
  intros sD HD.
  pose proof (ax_dg_vD_eval x c vB bit HB0 HBhi) as Hev.
  destruct Hbit as [-> | ->].
  - exists 1. unfold Rfin. simpl. refine (ax_dg_clean_ext _ _ _ _ _ (ax_dg_phaseE0 sD _ HD _)).
    + intro r. rewrite Hev. unfold sm_hin.
      destruct (Nat.eqb_spec r 0) as [-> | Hr0]; [reflexivity |].
      destruct (Nat.eqb r 1); reflexivity.
    + rewrite Hev. reflexivity.
  - exists 1. unfold Rfin. simpl. refine (ax_dg_clean_ext _ _ _ _ _ (ax_dg_phaseE1 sD _ 0 HD _)).
    + intro r. unfold M.upd. rewrite Hev. unfold sm_hin.
      destruct (Nat.eqb_spec r 0) as [-> | Hr0]; [reflexivity |].
      destruct (Nat.eqb r 1); reflexivity.
    + rewrite Hev. reflexivity.
Qed.

End Phases.
