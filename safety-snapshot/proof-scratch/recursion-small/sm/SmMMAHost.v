(** SmMMAHost.v: a program of the vendored alternate Minsky machine is a
    host program.

    The vendored alternate Minsky machine (MMA, Larchey-Wendling) with N
    counters has two instructions: INC x, and DEC x k, which decrements
    counter x and jumps to k when x is positive and otherwise falls
    through. Its program counter starts at 1, and it stops when the program
    counter leaves the program. The host machine has the same INC and the
    same DEC, on registers. So an MMA program P is the host program
    sm_mma_host P that names counter x as register x, instruction for
    instruction.

    [sm_mma_host_out]: started from a host core that holds the MMA start
    vector in registers 0 .. N-1 (and 0 above them), with the program
    counter at 1 and no trap, the host program stops with m in register 0
    exactly when the MMA program computes, from that vector, a final vector
    whose counter 0 holds m.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (MMA, DLW vectors and small-step semantics), EarnedCore.v,
    EarnedGeneric.v, EarnedMulti.v, UniversalCodes.v, SmHostBlocks.v,
    SmCodes.v and SmInterp.v. No axioms, no Admitted.                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks Sm.SmCodes Sm.SmInterp.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hcstep := (sm_cstep UC.hprop_eqb UC.heval).

Section MMAHost.

Variable N : nat.

Definition sm_mma_ki (i : mm_instr (pos N)) : sm_ki :=
  match i with
  | mm_inc x => sm_KInc (pos2nat x)
  | mm_dec x k => sm_KDec (pos2nat x) k
  end.

Definition sm_mma_prog (P : list (mm_instr (pos N))) : list sm_ki := map sm_mma_ki P.

Definition sm_mma_host (P : list (mm_instr (pos N))) : list hinstr := map sm_of_ki (sm_mma_prog P).

(* A host core holds the MMA state (i, v). *)
Definition sm_mmatch (k : hcore) (st : nat * Vector.t nat N) : Prop :=
  M.err k = false /\ M.pc k = fst st /\
  (forall p : pos N, M.vals k (pos2nat p) = vec_pos (snd st) p) /\
  (forall r, N <= r -> M.vals k r = 0).

Variable P : list (mm_instr (pos N)).

Local Notation VG := (sm_mma_host P).

Lemma sm_mma_fetch : forall i, M.fetch VG i = option_map (fun x => sm_of_ki (sm_mma_ki x)) (M.fetch P i).
Proof.
  intros [| i]; [reflexivity |]. simpl. unfold sm_mma_host, sm_mma_prog.
  rewrite map_map, nth_error_map. reflexivity.
Qed.

Lemma sm_write_match : forall k i v x n j,
  sm_mmatch k (i, v) ->
  sm_mmatch (M.write k (pos2nat x) n j) (j, vec_change v x n).
Proof.
  intros k i v x n j (He & Hp & Hv & Hz). unfold sm_mmatch. simpl. repeat split.
  - exact He.
  - intro p. unfold M.upd. destruct (pos_eq_dec x p) as [-> | Hne].
    + rewrite Nat.eqb_refl, vec_change_eq; reflexivity.
    + rewrite vec_change_neq by exact Hne.
      replace (Nat.eqb (pos2nat p) (pos2nat x)) with false.
      * apply Hv.
      * symmetry. apply Nat.eqb_neq. intro E. apply Hne. symmetry. apply pos2nat_inj, E.
  - intros r Hr. unfold M.upd. pose proof (pos2nat_prop x).
    replace (Nat.eqb r (pos2nat x)) with false by (symmetry; apply Nat.eqb_neq; lia).
    apply Hz, Hr.
Qed.

(* One MMA step inside the program is one host step. *)
Lemma sm_mma_step : forall k i v,
  sm_mmatch k (i, v) -> 1 <= i < 1 + length P ->
  exists st', sss_step (@mma_sss N) (1, P) (i, v) st' /\ sm_mmatch (hcstep VG k) st' /\
              M.next_instr VG k <> None.
Proof.
  intros k i v Hm Hi. pose proof Hm as (He & Hp & Hv & Hz). simpl in Hp, Hv.
  destruct i as [| i']; [lia |].
  assert (Hlt : i' < length P) by lia.
  destruct (nth_error P i') as [rho |] eqn:Hrho; [| apply nth_error_None in Hrho; lia].
  destruct (nth_error_split P i' Hrho) as [l [r [HP Hl]]].
  assert (Hf : M.fetch VG (M.pc k) = Some (sm_of_ki (sm_mma_ki rho))).
  { rewrite Hp, sm_mma_fetch. simpl. rewrite Hrho. reflexivity. }
  assert (Hn : M.next_instr VG k = Some (sm_of_ki (sm_mma_ki rho))).
  { unfold M.next_instr. rewrite He, Hf. destruct rho; reflexivity. }
  assert (Hstep : forall st', mma_sss rho (S i', v) st' -> sss_step (@mma_sss N) (1, P) (S i', v) st').
  { intros st' H. rewrite HP. apply in_sss_step; [simpl; lia | exact H]. }
  unfold sm_cstep. rewrite Hn. unfold M.cexec. rewrite He.
  destruct rho as [x | x j]; cbn [sm_mma_ki sm_of_ki].
  - exists (1 + S i', vec_change v x (S (vec_pos v x))). split; [apply Hstep; constructor |].
    split; [| congruence].
    rewrite (Hv x). rewrite Hp. apply (sm_write_match k (S i') v x). exact Hm.
  - rewrite (Hv x). destruct (vec_pos v x) as [| u] eqn:Ex.
    + exists (1 + S i', v). split; [apply Hstep; constructor; exact Ex |].
      split; [| congruence].
      unfold M.goto, sm_mmatch. simpl. rewrite Hp. repeat split; auto.
    + exists (j, vec_change v x u). split; [apply Hstep; constructor; exact Ex |].
      split; [| congruence].
      apply (sm_write_match k (S i') v x). exact Hm.
Qed.

(* Outside the program the host has stopped. *)
Lemma sm_mma_out_halted : forall k i v,
  sm_mmatch k (i, v) -> out_code i (1, P) -> M.halted VG k.
Proof.
  intros k i v (He & Hp & _) Hout. simpl in Hp.
  unfold M.halted, M.next_instr. rewrite He, Hp, sm_mma_fetch.
  unfold out_code, code_start, code_end in Hout. simpl in Hout.
  destruct i as [| i]; [reflexivity |]. simpl.
  replace (nth_error P i) with (@None (mm_instr (pos N))); [reflexivity |].
  symmetry. apply nth_error_None. lia.
Qed.

Lemma sm_mma_forward : forall n st st', sss_steps (@mma_sss N) (1, P) n st st' ->
  forall k, sm_mmatch k st -> sm_mmatch (sm_crun n VG k) st'.
Proof.
  intros n st st' H. induction H as [st | n st1 st2 st3 H12 H23 IH]; intros k Hk; [exact Hk |].
  destruct st1 as [i v].
  assert (Hin : 1 <= i < 1 + length P).
  { apply sss_step_in_code in H12. unfold in_code, code_start, code_end in H12. simpl in H12. lia. }
  destruct (sm_mma_step k i v Hk Hin) as [st'' [H12' [Hm _]]].
  assert (st'' = st2) as ->.
  { eapply sss_step_fun; [apply mma_sss_fun | exact H12' | exact H12]. }
  simpl. apply IH, Hm.
Qed.

Lemma sm_crun_halted : forall n (Q : list hinstr) k, M.halted Q k -> sm_crun n Q k = k.
Proof.
  induction n as [| n IH]; intros Q k H; [reflexivity |].
  simpl. unfold sm_cstep. unfold M.halted in H. rewrite H. apply IH, H.
Qed.

Lemma sm_mma_backward : forall n k st, sm_mmatch k st -> M.halted VG (sm_crun n VG k) ->
  exists st', sss_compute (@mma_sss N) (1, P) st st' /\ out_code (fst st') (1, P) /\ sm_mmatch (sm_crun n VG k) st'.
Proof.
  induction n as [| n IH]; intros k [i v] Hk Hh.
  - exists (i, v). split; [exists 0; constructor |]. split; [| exact Hk].
    unfold out_code, code_start, code_end. simpl.
    destruct (le_lt_dec 1 i) as [H1 | H1]; [destruct (le_lt_dec (1 + length P) i) as [H2 | H2] |];
      try lia.
    exfalso. destruct (sm_mma_step k i v Hk (conj H1 H2)) as [_ [_ [_ Hn]]]. exact (Hn Hh).
  - destruct (le_lt_dec 1 i) as [H1 | H1]; [destruct (le_lt_dec (1 + length P) i) as [H2 | H2] |].
    + exists (i, v). split; [exists 0; constructor |].
      assert (Hout : out_code i (1, P)) by (unfold out_code, code_start, code_end; simpl; lia).
      split; [exact Hout |].
      rewrite sm_crun_halted by exact (sm_mma_out_halted k i v Hk Hout). exact Hk.
    + destruct (sm_mma_step k i v Hk (conj H1 H2)) as [st2 [H12 [Hm _]]].
      simpl in Hh. destruct (IH (hcstep VG k) st2 Hm Hh) as [st' [Hc [Ho Hm']]].
      exists st'. split; [| split; [exact Ho | exact Hm']].
      destruct Hc as [q Hq]. exists (S q). econstructor; eauto.
    + exists (i, v). split; [exists 0; constructor |].
      assert (Hout : out_code i (1, P)) by (unfold out_code, code_start, code_end; simpl; lia).
      split; [exact Hout |].
      rewrite sm_crun_halted by exact (sm_mma_out_halted k i v Hk Hout). exact Hk.
Qed.

End MMAHost.

Theorem sm_mma_host_out : forall N' (P : list (mm_instr (pos (S N')))) (k : hcore) v0 m,
  sm_mmatch (S N') k (1, v0) ->
  ((exists c (v' : Vector.t nat N'), sss_output (@mma_sss (S N')) (1, P) (1, v0) (c, Vector.cons nat m N' v')) <->
   (exists n, M.halted (sm_mma_host (S N') P) (sm_crun n (sm_mma_host (S N') P) k) /\
              M.vals (sm_crun n (sm_mma_host (S N') P) k) 0 = m)).
Proof.
  intros N' P k v0 m Hk. split.
  - intros [c [v' [[n Hn] Hout]]].
    pose proof (sm_mma_forward (S N') P n _ _ Hn k Hk) as Hm.
    exists n. split.
    + exact (sm_mma_out_halted (S N') P _ c _ Hm Hout).
    + destruct Hm as (_ & _ & Hv & _). specialize (Hv pos0).
      rewrite pos2nat_fst in Hv. rewrite Hv. reflexivity.
  - intros [n [Hh Hv0]].
    destruct (sm_mma_backward (S N') P n k (1, v0) Hk Hh) as [[c w] [Hc [Ho Hm]]].
    exists c, (vec_tail w).
    destruct Hm as (_ & _ & Hv & _). specialize (Hv pos0).
    rewrite pos2nat_fst, vec_pos0 in Hv.
    assert (Em : m = vec_head w) by (rewrite <- Hv0; exact Hv).
    rewrite Em, <- vec_head_tail. split; [exact Hc | exact Ho].
Qed.

Print Assumptions sm_mma_host_out.
