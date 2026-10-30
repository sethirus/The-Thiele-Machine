(** SmMMAOff.v: a Minsky program in the middle of a bigger host program,
    working on a window of registers.

    SmMMAHost.v reads a program of the vendored alternate Minsky machine
    (MMA) with N counters as a host program that names counter x as register
    x. Here the program is shifted: counter x is register base + x, so the
    program works in the window of registers base .. base + N - 1 and
    leaves every other register, every version outside the window, the fact
    table, the channel, the trap latch, the ledger and the flag alone. The
    program is also placed inside a bigger program Q at an offset off, as a
    relocated block (SmHostBlocks.v).

    What is proved:
      1. [sm2_mma_ctx]: if the MMA program computes m from the start vector
         v0, and the window of a host state u at the start line of the block
         holds v0, then Q runs from u, with no earlier stop, to a state at the
         line after the block, with m in register base and the rest of the
         state as described above.
      2. [sm2_mma_ctx_loop]: if the MMA program computes nothing from v0,
         Q never stops while it is in the block.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedMulti.v, UniversalCodes.v, SmHostBlocks.v, SmHostRice.v,
    SmCodes.v, SmLoops.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here a Minsky program working in a window of registers inside a program of the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Kernel.SmHostRice Minimal.SmCodes Minimal.SmLoops.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation srel := (sm_srel (prop := UC.hprop)).

(* ================================================================= *)
(* Lifting a run of a block into the bigger program.                  *)
(* ================================================================= *)

Lemma sm2_RR_lift : forall Sr Q B off, sm_embeds Q B off -> sm_within Sr B ->
  forall s s', sm2_RR B s s' -> forall u, srel Sr off (length B) s u ->
  exists u', sm2_RR Q u u' /\ srel Sr off (length B) s' u'.
Proof.
  intros Sr Q B off Hemb Hwin s s' H. induction H as [s | s s'' Hn H IH]; intros u Hu.
  - exists u. split; [apply sm2_RR_refl | exact Hu].
  - destruct (M.next_instr B (M.core_of s)) as [i |] eqn:Hi; [| congruence].
    destruct (sm_block_step UC.hprop_eqb UC.heval Sr Q B off s u i Hemb Hwin Hu Hi) as [Hn' Hs'].
    destruct (IH _ Hs') as (u' & R & Hu').
    exists u'. split; [| exact Hu'].
    eapply sm2_RR_step; [congruence | exact R].
Qed.

(* ================================================================= *)
(* The program in a window of registers.                              *)
(* ================================================================= *)

Section Window.

Variable N : nat.
Variable base : nat.

Definition sm2_mma_ki (i : mm_instr (pos N)) : sm_ki :=
  match i with
  | mm_inc x => sm_KInc (base + pos2nat x)
  | mm_dec x k => sm_KDec (base + pos2nat x) k
  end.

Definition sm2_mma_host (P : list (mm_instr (pos N))) : list hinstr :=
  map (fun i => sm_of_ki (sm2_mma_ki i)) P.

(* A host state holds the MMA state (i, v). *)
Definition sm2_mmatch (s : hstate) (st : nat * Vector.t nat N) : Prop :=
  M.err (M.core_of s) = false /\ M.pc (M.core_of s) = fst st /\
  (forall p : pos N, M.vals (M.core_of s) (base + pos2nat p) = vec_pos (snd st) p).

(* The state t is the state s outside the window. *)
Definition sm2_mmfr (s t : hstate) : Prop :=
  (forall q, (q < base \/ base + N <= q) ->
     M.vals (M.core_of t) q = M.vals (M.core_of s) q /\ M.vers (M.core_of t) q = M.vers (M.core_of s) q) /\
  sm2_pfe s t.

Lemma sm2_mmfr_refl : forall s, sm2_mmfr s s.
Proof. intro s. split; [intros q _; split; reflexivity | apply sm2_pfe_refl]. Qed.

Lemma sm2_mmfr_trans : forall s t u, sm2_mmfr s t -> sm2_mmfr t u -> sm2_mmfr s u.
Proof.
  intros s t u (A & B) (A' & B'). split.
  - intros q Hq. destruct (A' q Hq) as [X Y], (A q Hq) as [X' Y']. split; congruence.
  - eapply sm2_pfe_trans; eauto.
Qed.

Variable P : list (mm_instr (pos N)).

Local Notation VG := (sm2_mma_host P).

Lemma sm2_mma_fetch : forall i,
  M.fetch VG i = option_map (fun x => sm_of_ki (sm2_mma_ki x)) (M.fetch P i).
Proof.
  intros [| i]; [reflexivity |]. simpl. unfold sm2_mma_host.
  rewrite nth_error_map. reflexivity.
Qed.

Lemma sm2_pos_outside : forall (x : pos N) q, (q < base \/ base + N <= q) -> q <> base + pos2nat x.
Proof. intros x q Hq. pose proof (pos2nat_prop x). lia. Qed.

(* One MMA step inside the program is one host step. *)
Lemma sm2_mma_step : forall s i v,
  sm2_mmatch s (i, v) -> 1 <= i < 1 + length P ->
  exists st', sss_step (@mma_sss N) (1, P) (i, v) st' /\ sm2_mmatch (hstep VG s) st' /\
              M.next_instr VG (M.core_of s) <> None /\ sm2_mmfr s (hstep VG s).
Proof.
  intros s i v Hm Hi. pose proof Hm as (He & Hp & Hv). simpl in Hp, Hv.
  destruct i as [| i']; [lia |].
  assert (Hlt : i' < length P) by lia.
  destruct (nth_error P i') as [rho |] eqn:Hrho; [| apply nth_error_None in Hrho; lia].
  destruct (nth_error_split P i' Hrho) as [l [r [HP Hl]]].
  assert (Hf : M.fetch VG (M.pc (M.core_of s)) = Some (sm_of_ki (sm2_mma_ki rho))).
  { rewrite Hp, sm2_mma_fetch. simpl. rewrite Hrho. reflexivity. }
  assert (Hstep : forall st', mma_sss rho (S i', v) st' -> sss_step (@mma_sss N) (1, P) (S i', v) st').
  { intros st' H. rewrite HP. apply in_sss_step; [simpl; lia | exact H]. }
  destruct rho as [x | x j]; cbn [sm2_mma_ki sm_of_ki] in Hf.
  - destruct (sm2_step_inc VG s _ He Hf) as (N1 & P1 & V1 & W1 & E1).
    exists (1 + S i', vec_change v x (S (vec_pos v x))). split; [apply Hstep; constructor |].
    refine (conj _ (conj N1 _)).
    + unfold sm2_mmatch. cbn [fst snd]. refine (conj _ (conj _ _)).
      * destruct E1 as (_ & _ & C & _). rewrite <- C. exact He.
      * rewrite P1, Hp. lia.
      * intro p. rewrite V1. destruct (pos_eq_dec x p) as [-> | Hne].
        -- rewrite Nat.eqb_refl. rewrite vec_change_eq by reflexivity. rewrite Hv. reflexivity.
        -- rewrite vec_change_neq by exact Hne.
           replace (Nat.eqb (base + pos2nat p) (base + pos2nat x)) with false.
           ++ apply Hv.
           ++ symmetry. apply Nat.eqb_neq. intro E. apply Hne. symmetry. apply pos2nat_inj. lia.
    + split.
      * intros q Hq. rewrite V1. rewrite (proj2 (Nat.eqb_neq _ _) (sm2_pos_outside x q Hq)).
        split; [reflexivity | apply W1]. apply sm2_pos_outside; exact Hq.
      * exact E1.
  - destruct (vec_pos v x) as [| u] eqn:Ex.
    + destruct (sm2_step_dec_zero VG s _ j He Hf (eq_trans (Hv x) Ex)) as (N1 & P1 & V1 & W1 & E1).
      exists (1 + S i', v). split; [apply Hstep; constructor; exact Ex |].
      refine (conj _ (conj N1 _)).
      * unfold sm2_mmatch. cbn [fst snd]. refine (conj _ (conj _ _)).
        -- destruct E1 as (_ & _ & C & _). rewrite <- C. exact He.
        -- rewrite P1, Hp. lia.
        -- intro p. rewrite V1. apply Hv.
      * split.
        -- intros q Hq. rewrite V1, W1. split; reflexivity.
        -- exact E1.
    + destruct (sm2_step_dec_pos VG s _ j u He Hf (eq_trans (Hv x) Ex)) as (N1 & P1 & V1 & W1 & E1).
      exists (j, vec_change v x u). split; [apply Hstep; constructor; exact Ex |].
      refine (conj _ (conj N1 _)).
      * unfold sm2_mmatch. cbn [fst snd]. refine (conj _ (conj _ _)).
        -- destruct E1 as (_ & _ & C & _). rewrite <- C. exact He.
        -- exact P1.
        -- intro p. rewrite V1. destruct (pos_eq_dec x p) as [-> | Hne].
           ++ rewrite Nat.eqb_refl. rewrite vec_change_eq by reflexivity. reflexivity.
           ++ rewrite vec_change_neq by exact Hne.
              replace (Nat.eqb (base + pos2nat p) (base + pos2nat x)) with false.
              ** apply Hv.
              ** symmetry. apply Nat.eqb_neq. intro E. apply Hne. symmetry. apply pos2nat_inj. lia.
      * split.
        -- intros q Hq. rewrite V1. rewrite (proj2 (Nat.eqb_neq _ _) (sm2_pos_outside x q Hq)).
           split; [reflexivity | apply W1]. apply sm2_pos_outside; exact Hq.
        -- exact E1.
Qed.

(* Outside the program the host has stopped. *)
Lemma sm2_mma_out_halted : forall s i v,
  sm2_mmatch s (i, v) -> out_code i (1, P) -> M.halted VG (M.core_of s).
Proof.
  intros s i v (He & Hp & _) Hout. simpl in Hp.
  unfold M.halted, M.next_instr. rewrite He, Hp, sm2_mma_fetch.
  unfold out_code, code_start, code_end in Hout. simpl in Hout.
  destruct i as [| i]; [reflexivity |]. simpl.
  replace (nth_error P i) with (@None (mm_instr (pos N))); [reflexivity |].
  symmetry. apply nth_error_None. lia.
Qed.

Lemma sm2_mma_forward : forall n st st', sss_steps (@mma_sss N) (1, P) n st st' ->
  forall s, sm2_mmatch s st ->
  exists s', sm2_RR VG s s' /\ sm2_mmatch s' st' /\ sm2_mmfr s s'.
Proof.
  intros n st st' H. induction H as [st | m st1 st2 st3 H12 H23 IH]; intros s Hs.
  - exists s. split; [apply sm2_RR_refl | split; [exact Hs | apply sm2_mmfr_refl]].
  - destruct st1 as [i v].
    assert (Hin : 1 <= i < 1 + length P).
    { apply sss_step_in_code in H12. unfold in_code, code_start, code_end in H12. simpl in H12. lia. }
    destruct (sm2_mma_step s i v Hs Hin) as [st'' [H12' [Hm [Hn Hfr]]]].
    assert (st'' = st2) as ->.
    { eapply sss_step_fun; [apply mma_sss_fun | exact H12' | exact H12]. }
    destruct (IH _ Hm) as (s' & R & Hm' & Hfr').
    exists s'. split; [eapply sm2_RR_step; [exact Hn | exact R] |].
    split; [exact Hm' | eapply sm2_mmfr_trans; [exact Hfr | exact Hfr']].
Qed.

Lemma sm2_mma_backward : forall n s st, sm2_mmatch s st ->
  M.halted VG (M.core_of (hrun_prog n VG s)) ->
  exists st', sss_compute (@mma_sss N) (1, P) st st' /\ out_code (fst st') (1, P) /\
              sm2_mmatch (hrun_prog n VG s) st'.
Proof.
  induction n as [| n IH]; intros s [i v] Hk Hh.
  - exists (i, v). split; [exists 0; constructor |]. split; [| exact Hk].
    unfold out_code, code_start, code_end. simpl.
    destruct (le_lt_dec 1 i) as [H1 | H1]; [destruct (le_lt_dec (1 + length P) i) as [H2 | H2] |];
      try lia.
    exfalso. destruct (sm2_mma_step s i v Hk (conj H1 H2)) as [_ [_ [_ [Hn _]]]]. exact (Hn Hh).
  - destruct (le_lt_dec 1 i) as [H1 | H1]; [destruct (le_lt_dec (1 + length P) i) as [H2 | H2] |].
    + exists (i, v). split; [exists 0; constructor |].
      assert (Hout : out_code i (1, P)) by (unfold out_code, code_start, code_end; simpl; lia).
      split; [exact Hout |].
      assert (Hh0 : M.next_instr VG (M.core_of s) = None) by exact (sm2_mma_out_halted s i v Hk Hout).
      rewrite (sm_halted_stay UC.hprop_eqb UC.heval (S n) VG s Hh0). exact Hk.
    + destruct (sm2_mma_step s i v Hk (conj H1 H2)) as [st2 [H12 [Hm _]]].
      rewrite sm_run_succ in Hh.
      destruct (IH (hstep VG s) st2 Hm Hh) as [st' [Hc [Ho Hm']]].
      exists st'. split; [| split; [exact Ho | ]].
      * destruct Hc as [q Hq]. exists (S q). econstructor; eauto.
      * rewrite sm_run_succ. exact Hm'.
    + exists (i, v). split; [exists 0; constructor |].
      assert (Hout : out_code i (1, P)) by (unfold out_code, code_start, code_end; simpl; lia).
      split; [exact Hout |].
      assert (Hh0 : M.next_instr VG (M.core_of s) = None) by exact (sm2_mma_out_halted s i v Hk Hout).
      rewrite (sm_halted_stay UC.hprop_eqb UC.heval (S n) VG s Hh0). exact Hk.
Qed.

End Window.

(* ================================================================= *)
(* The program as a block in a bigger program.                        *)
(* ================================================================= *)

Theorem sm2_mma_ctx : forall N' base off Q (P : list (mm_instr (pos (S N')))) (u : hstate) v0 m,
  sm_embeds Q (sm2_mma_host (S N') base P) off ->
  M.pc (M.core_of u) = S off -> M.err (M.core_of u) = false ->
  (forall p : pos (S N'), M.vals (M.core_of u) (base + pos2nat p) = vec_pos v0 p) ->
  (exists c (v' : Vector.t nat N'),
     sss_output (@mma_sss (S N')) (1, P) (1, v0) (c, Vector.cons nat m N' v')) ->
  exists u', sm2_RR Q u u' /\ M.pc (M.core_of u') = S (off + length P) /\
    M.err (M.core_of u') = false /\ M.vals (M.core_of u') base = m /\
    (forall q, (q < base \/ base + S N' <= q) ->
       M.vals (M.core_of u') q = M.vals (M.core_of u) q /\
       M.vers (M.core_of u') q = M.vers (M.core_of u) q) /\
    sm2_pfe u u'.
Proof.
  intros N' base off Q P u v0 m Hemb Hp He Hv [c [v' [[n Hn] Hout]]].
  set (B := sm2_mma_host (S N') base P).
  assert (HlenB : length B = length P) by (unfold B, sm2_mma_host; apply map_length).
  set (s := sm_at1 u).
  assert (Hrel : srel (fun _ => True) off (length B) s u) by (apply sm_at1_rel; exact Hp).
  assert (Hms : sm2_mmatch (S N') base s (1, v0)).
  { unfold sm2_mmatch, s, sm_at1, M.goto. cbn [M.err M.pc M.vals M.core_of fst snd].
    refine (conj He (conj eq_refl _)). exact Hv. }
  destruct (sm2_mma_forward (S N') base P n _ _ Hn s Hms) as (s' & R & Hm' & Hfr).
  destruct (sm2_RR_lift (fun _ => True) Q B off Hemb (sm_within_all B) s s' R u Hrel)
    as (u' & R' & Hrel').
  exists u'. destruct Hrel' as ((Hv' & Hw' & Hf' & Hc' & He' & Hp') & Hm'' & Hk').
  destruct Hm' as (He2 & Hp2 & Hv2). cbn [fst snd] in Hp2, Hv2.
  assert (Hout' : ~ (1 <= c < 1 + length P)).
  { unfold out_code, code_start, code_end in Hout. simpl in Hout. lia. }
  destruct Hfr as (Hfr1 & Hfr2).
  refine (conj R' (conj _ (conj _ (conj _ (conj _ _))))).
  - rewrite Hp', Hp2. rewrite HlenB. rewrite sm_rj_out by lia. lia.
  - rewrite <- He'. exact He2.
  - rewrite <- Hv'. specialize (Hv2 pos0). rewrite pos2nat_fst in Hv2. rewrite Nat.add_0_r in Hv2.
    rewrite Hv2. apply vec_pos0.
  - intros q Hq. rewrite <- Hv', <- (Hw' q I). destruct (Hfr1 q Hq) as [A1 A2].
    destruct Hrel as ((Hv0 & Hw0 & _) & _). rewrite A1, A2. unfold s, sm_at1, M.goto. simpl.
    split; [apply Hv0 | apply Hw0; exact I].
  - destruct Hfr2 as (F1 & F2 & F3 & F4 & F5).
    destruct Hrel as ((_ & _ & Hf0 & Hc0 & He0 & _) & Hm0 & Hk0).
    unfold sm2_pfe. refine (conj _ (conj _ (conj _ (conj _ _)))).
    + rewrite <- Hf'. rewrite <- F1. exact Hf0.
    + rewrite <- Hc'. rewrite <- F2. exact Hc0.
    + rewrite <- He'. rewrite <- F3. exact He0.
    + rewrite <- Hm''. rewrite <- F4. exact Hm0.
    + rewrite <- Hk'. rewrite <- F5. exact Hk0.
Qed.

Lemma sm2_bsearch : forall (H : nat -> Prop), (forall m, H m \/ ~ H m) ->
  forall n, (forall m, m <= n -> ~ H m) \/ (exists m, m <= n /\ H m).
Proof.
  intros H Hdec n. induction n as [| n IH].
  - destruct (Hdec 0) as [H0 | H0].
    + right. exists 0. split; [lia | exact H0].
    + left. intros m Hm. assert (m = 0) as -> by lia. exact H0.
  - destruct IH as [IH | [m [Hm Hh]]].
    + destruct (Hdec (S n)) as [H1 | H1].
      * right. exists (S n). split; [lia | exact H1].
      * left. intros m Hm. destruct (Nat.eq_dec m (S n)) as [-> | Hne]; [exact H1 | apply IH; lia].
    + right. exists m. split; [lia | exact Hh].
Qed.

Lemma sm2_next_dec : forall (P : list hinstr) k,
  M.next_instr P k = None \/ ~ M.next_instr P k = None.
Proof.
  intros P k. destruct (M.next_instr P k) as [i |]; [right; intro Hx; discriminate Hx | left; reflexivity].
Qed.

(* If the program stops while it is in the block, the block's MMA program
   computes something. *)
Theorem sm2_mma_ctx_halt : forall N' base off Q (P : list (mm_instr (pos (S N')))) (u : hstate) v0,
  sm_embeds Q (sm2_mma_host (S N') base P) off ->
  M.pc (M.core_of u) = S off -> M.err (M.core_of u) = false ->
  (forall p : pos (S N'), M.vals (M.core_of u) (base + pos2nat p) = vec_pos v0 p) ->
  forall n, M.next_instr Q (M.core_of (hrun_prog n Q u)) = None ->
  exists c (w : Vector.t nat (S N')), sss_output (@mma_sss (S N')) (1, P) (1, v0) (c, w).
Proof.
  intros N' base off Q P u v0 Hemb Hp He Hv n Hn.
  set (B := sm2_mma_host (S N') base P).
  set (s := sm_at1 u).
  assert (Hrel : srel (fun _ => True) off (length B) s u) by (apply sm_at1_rel; exact Hp).
  assert (Hms : sm2_mmatch (S N') base s (1, v0)).
  { unfold sm2_mmatch, s, sm_at1, M.goto. cbn [M.err M.pc M.vals M.core_of fst snd].
    refine (conj He (conj eq_refl _)). exact Hv. }
  destruct (sm2_bsearch (fun m => M.next_instr B (M.core_of (hrun_prog m B s)) = None)
              (fun m => sm2_next_dec B (M.core_of (hrun_prog m B s))) n)
    as [Hno | [m [Hmn Hm]]].
  - exfalso.
    assert (Hrun : forall m, m < n -> M.next_instr B (M.core_of (hrun_prog m B s)) <> None)
      by (intros m Hm Hx; exact (Hno m ltac:(lia) Hx)).
    pose proof (sm_block_run_mid UC.hprop_eqb UC.heval (fun _ => True) Q B off Hemb (sm_within_all B)
      n s u Hrel Hrun) as Hrn.
    exact (sm_block_not_halted UC.hprop_eqb UC.heval (fun _ => True) Q B off _ _ Hemb (sm_within_all B)
             Hrn (Hno n (le_n n)) Hn).
  - destruct (sm2_mma_backward (S N') base P m s (1, v0) Hms Hm) as (st' & Hc & Ho & _).
    exists (fst st'), (snd st'). destruct st' as [c w]. cbn [fst snd]. split; assumption.
Qed.

Print Assumptions sm2_mma_ctx.
Print Assumptions sm2_mma_ctx_halt.
