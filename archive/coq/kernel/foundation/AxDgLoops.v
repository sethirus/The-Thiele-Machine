(** AxDgLoops: counter loops of the host machine and an MMA program run with
    other registers present.

    A state of the host machine that has done nothing but move counters is
    described by its program counter and the values of its registers: no
    facts, no channel, no trap, ledger 0, flag down.  [ax_dg_clean s pc v].
    The versions are left out on purpose: the block lemma of AxDgBlock.v does
    not need them.

    Results (all closed):

      ax_dg_move      three lines  INC dst; DEC src L; DEC dst (L+3)  move the
                      content of src onto dst and leave the state clean at
                      L+3, for any two different registers;
      ax_dg_clear     the one line  DEC r L  at line L empties r;
      ax_dg_clears    one such line for each of the registers 1 .. cnt, on
                      consecutive lines, empties them all;
      ax_dg_mma_out   the output relation of an MMA program, run as a host
                      program from a core that has the start vector in
                      registers 0 .. N-1, no matter what registers N and above
                      hold (SmMMAHost.v needs them to be 0). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the multi-register host machine (counting loops and register moves), built for
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
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmMMAHost Kernel.SmNoExact.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

(** * 1. Clean states *)

Definition ax_dg_clean (s : hstate) (pc : nat) (v : nat -> nat) : Prop :=
  M.err (M.core_of s) = false /\ M.pc (M.core_of s) = pc /\
  (forall r, M.vals (M.core_of s) r = v r) /\
  M.facts (M.core_of s) = [] /\ M.chan (M.core_of s) = None /\
  M.mu s = 0 /\ M.cert s = false.

Lemma ax_dg_clean_ext : forall s pc v w,
  (forall r, v r = w r) -> ax_dg_clean s pc v -> ax_dg_clean s pc w.
Proof.
  intros s pc v w Hvw (He & Hp & Hv & Hf & Hc & Hm & Hk).
  repeat split; auto. intro r. rewrite Hv. apply Hvw.
Qed.

Lemma ax_dg_clean_pc : forall s pc pc' v,
  pc = pc' -> ax_dg_clean s pc v -> ax_dg_clean s pc' v.
Proof. intros s pc pc' v <- H. exact H. Qed.

(** The step of a clean state on an INC, a DEC on a positive register and a
    DEC on an empty register. *)
Lemma ax_dg_step_inc : forall Q s r pc v,
  ax_dg_clean s pc v -> M.fetch Q pc = Some (M.INC r) ->
  ax_dg_clean (hstep Q s) (S pc) (M.upd v r (S (v r))).
Proof.
  intros Q s r pc v (He & Hp & Hv & Hf & Hc & Hm & Hk) Hfe.
  assert (Hn : M.next_instr Q (M.core_of s) = Some (M.INC r))
    by (apply sm_next_intro; [exact He | rewrite Hp; exact Hfe | discriminate]).
  unfold M.step. rewrite Hn. unfold ax_dg_clean, M.exec, M.cexec. rewrite He. simpl.
  repeat split; auto.
  all: try (intro q; unfold M.upd; rewrite !Hv; reflexivity).
  all: try (rewrite ?Hm, ?Hk; reflexivity).
Qed.

Lemma ax_dg_step_dec_pos : forall Q s r j pc v u,
  ax_dg_clean s pc v -> M.fetch Q pc = Some (M.DEC r j) -> v r = S u ->
  ax_dg_clean (hstep Q s) j (M.upd v r u).
Proof.
  intros Q s r j pc v u (He & Hp & Hv & Hf & Hc & Hm & Hk) Hfe Hr.
  assert (Hn : M.next_instr Q (M.core_of s) = Some (M.DEC r j))
    by (apply sm_next_intro; [exact He | rewrite Hp; exact Hfe | discriminate]).
  unfold M.step. rewrite Hn. unfold ax_dg_clean, M.exec, M.cexec. rewrite He. simpl.
  rewrite Hv, Hr. simpl.
  repeat split; auto.
  all: try (intro q; unfold M.upd; rewrite ?Hv; reflexivity).
  all: try (rewrite ?Hm, ?Hk; reflexivity).
Qed.

Lemma ax_dg_step_dec_zero : forall Q s r j pc v,
  ax_dg_clean s pc v -> M.fetch Q pc = Some (M.DEC r j) -> v r = 0 ->
  ax_dg_clean (hstep Q s) (S pc) v.
Proof.
  intros Q s r j pc v (He & Hp & Hv & Hf & Hc & Hm & Hk) Hfe Hr.
  assert (Hn : M.next_instr Q (M.core_of s) = Some (M.DEC r j))
    by (apply sm_next_intro; [exact He | rewrite Hp; exact Hfe | discriminate]).
  unfold M.step. rewrite Hn. unfold ax_dg_clean, M.exec, M.cexec. rewrite He. simpl.
  rewrite Hv, Hr. simpl.
  repeat split; auto.
  all: try (rewrite ?Hm, ?Hk; reflexivity).
Qed.

Ltac ax_dg_cases :=
  unfold M.upd;
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
  subst; try congruence; try lia.

(** * 2. Moving a counter *)

Lemma ax_dg_move_gen : forall (Q : list hinstr) L src dst, src <> dst ->
  M.fetch Q L = Some (M.INC dst) ->
  M.fetch Q (S L) = Some (M.DEC src L) ->
  M.fetch Q (S (S L)) = Some (M.DEC dst (S (S (S L)))) ->
  forall k v s, v src = k -> ax_dg_clean s L v ->
  exists n, ax_dg_clean (hrun_prog n Q s) (S (S (S L)))
              (M.upd (M.upd v src 0) dst (v dst + k)).
Proof.
  intros Q L src dst Hne F1 F2 F3 k. induction k as [| k IH]; intros v s Hk Hs.
  - (* the source is empty: INC dst, DEC src falls, DEC dst jumps on *)
    pose proof (ax_dg_step_inc Q s dst L v Hs F1) as S1.
    assert (Hv1 : M.upd v dst (S (v dst)) src = 0).
    { unfold M.upd. replace (Nat.eqb src dst) with false by (symmetry; apply Nat.eqb_neq; exact Hne).
      exact Hk. }
    pose proof (ax_dg_step_dec_zero Q _ src L (S L) _ S1 F2 Hv1) as S2.
    assert (Hv2 : M.upd v dst (S (v dst)) dst = S (v dst)).
    { unfold M.upd. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (ax_dg_step_dec_pos Q _ dst (S (S (S L))) (S (S L)) _ (v dst) S2 F3 Hv2) as S3.
    exists 3. simpl. refine (ax_dg_clean_ext _ _ _ _ _ S3).
    intro q. ax_dg_cases.
  - pose proof (ax_dg_step_inc Q s dst L v Hs F1) as S1.
    assert (Hv1 : M.upd v dst (S (v dst)) src = S k).
    { unfold M.upd. replace (Nat.eqb src dst) with false by (symmetry; apply Nat.eqb_neq; exact Hne).
      exact Hk. }
    pose proof (ax_dg_step_dec_pos Q _ src L (S L) _ k S1 F2 Hv1) as S2.
    destruct (IH (M.upd (M.upd v dst (S (v dst))) src k) (hstep Q (hstep Q s))) as [n Hn].
    { unfold M.upd. replace (Nat.eqb src src) with true by (symmetry; apply Nat.eqb_refl). reflexivity. }
    { exact S2. }
    exists (S (S n)). rewrite sm_run_succ. rewrite sm_run_succ. simpl.
    refine (ax_dg_clean_ext _ _ _ _ _ Hn).
    intro q. ax_dg_cases.
Qed.

Lemma ax_dg_move : forall (Q : list hinstr) L src dst, src <> dst ->
  M.fetch Q L = Some (M.INC dst) ->
  M.fetch Q (S L) = Some (M.DEC src L) ->
  M.fetch Q (S (S L)) = Some (M.DEC dst (S (S (S L)))) ->
  forall v s, ax_dg_clean s L v ->
  exists n, ax_dg_clean (hrun_prog n Q s) (S (S (S L)))
              (M.upd (M.upd v src 0) dst (v dst + v src)).
Proof. intros Q L src dst Hne F1 F2 F3 v s Hs. apply (ax_dg_move_gen Q L src dst Hne F1 F2 F3 (v src) v s eq_refl Hs). Qed.

(** * 3. Emptying counters *)

Lemma ax_dg_clear_gen : forall (Q : list hinstr) L r,
  M.fetch Q L = Some (M.DEC r L) ->
  forall k v s, v r = k -> ax_dg_clean s L v ->
  exists n, ax_dg_clean (hrun_prog n Q s) (S L) (M.upd v r 0).
Proof.
  intros Q L r F k. induction k as [| k IH]; intros v s Hk Hs.
  - exists 1. simpl. pose proof (ax_dg_step_dec_zero Q s r L L v Hs F Hk) as S1.
    refine (ax_dg_clean_ext _ _ _ _ _ S1).
    intro q. unfold M.upd. destruct (Nat.eqb_spec q r) as [-> | Hq]; [exact Hk | reflexivity].
  - pose proof (ax_dg_step_dec_pos Q s r L L v k Hs F Hk) as S1.
    destruct (IH (M.upd v r k) (hstep Q s)) as [n Hn].
    { unfold M.upd. rewrite Nat.eqb_refl. reflexivity. }
    { exact S1. }
    exists (S n). rewrite sm_run_succ.
    refine (ax_dg_clean_ext _ _ _ _ _ Hn).
    intro q. unfold M.upd. destruct (Nat.eqb q r); reflexivity.
Qed.

Lemma ax_dg_clear : forall (Q : list hinstr) L r,
  M.fetch Q L = Some (M.DEC r L) ->
  forall v s, ax_dg_clean s L v ->
  exists n, ax_dg_clean (hrun_prog n Q s) (S L) (M.upd v r 0).
Proof. intros Q L r F v s Hs. apply (ax_dg_clear_gen Q L r F (v r) v s eq_refl Hs). Qed.

(** The registers 1 .. cnt, one line each, at the lines L+1 .. L+cnt. *)
Lemma ax_dg_clears : forall cnt (Q : list hinstr) L,
  (forall i, 1 <= i <= cnt -> M.fetch Q (L + i) = Some (M.DEC i (L + i))) ->
  forall v s, ax_dg_clean s (S L) v ->
  exists n, ax_dg_clean (hrun_prog n Q s) (S (L + cnt))
              (fun r => if (1 <=? r) && (r <=? cnt) then 0 else v r).
Proof.
  induction cnt as [| cnt IH]; intros Q L HF v s Hs.
  - exists 0. simpl. refine (ax_dg_clean_ext _ _ _ _ _ (ax_dg_clean_pc _ _ _ _ (eq_sym (Nat.add_0_r _)) Hs)).
    intro r. destruct r; reflexivity.
  - destruct (IH Q L (fun i Hi => HF i (conj (proj1 Hi) (le_S _ _ (proj2 Hi)))) v s Hs) as [n1 H1].
    assert (Hf : M.fetch Q (S (L + cnt)) = Some (M.DEC (S cnt) (S (L + cnt)))).
    { pose proof (HF (S cnt) (conj (le_n_S _ _ (Nat.le_0_l _)) (le_n _))) as H. rewrite <- plus_n_Sm in H. exact H. }
    destruct (ax_dg_clear Q (S (L + cnt)) (S cnt) Hf _ _ H1) as [n2 H2].
    exists (n1 + n2). rewrite sm_run_add.
    replace (S (L + S cnt)) with (S (S (L + cnt))) by lia.
    refine (ax_dg_clean_ext _ _ _ _ _ H2).
    intro r. unfold M.upd.
    destruct (Nat.eqb_spec r (S cnt)) as [-> | Hne].
    + replace ((1 <=? S cnt) && (S cnt <=? S cnt)) with true.
      * reflexivity.
      * symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
    + destruct (le_lt_dec 1 r) as [Ha | Ha]; destruct (le_lt_dec r cnt) as [Hb | Hb].
      * replace ((1 <=? r) && (r <=? S cnt)) with true.
        -- replace ((1 <=? r) && (r <=? cnt)) with true; [reflexivity |].
           symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
        -- symmetry. apply andb_true_iff. split; apply Nat.leb_le; lia.
      * replace ((1 <=? r) && (r <=? S cnt)) with false.
        -- replace ((1 <=? r) && (r <=? cnt)) with false; [reflexivity |].
           symmetry. apply andb_false_iff. right. apply Nat.leb_gt. lia.
        -- symmetry. apply andb_false_iff. right. apply Nat.leb_gt. lia.
      * replace ((1 <=? r) && (r <=? S cnt)) with false.
        -- replace ((1 <=? r) && (r <=? cnt)) with false; [reflexivity |].
           symmetry. apply andb_false_iff. left. apply Nat.leb_gt. lia.
        -- symmetry. apply andb_false_iff. left. apply Nat.leb_gt. lia.
      * replace ((1 <=? r) && (r <=? S cnt)) with false.
        -- replace ((1 <=? r) && (r <=? cnt)) with false; [reflexivity |].
           symmetry. apply andb_false_iff. left. apply Nat.leb_gt. lia.
        -- symmetry. apply andb_false_iff. left. apply Nat.leb_gt. lia.
Qed.

(** * 4. An MMA program with other registers present *)

Lemma ax_dg_mma_instr : forall N (P : list (mm_instr (pos N))) i,
  In i (sm_mma_host N P) -> exists r j, (i = M.INC r \/ i = M.DEC r j) /\ r < N.
Proof.
  intros N P i Hin. unfold sm_mma_host, sm_mma_prog in Hin. rewrite map_map in Hin.
  apply in_map_iff in Hin. destruct Hin as [[x | x j] [<- _]]; simpl.
  - exists (pos2nat x), 0. split; [left; reflexivity | apply pos2nat_prop].
  - exists (pos2nat x), j. split; [right; reflexivity | apply pos2nat_prop].
Qed.

(** Two cores that agree below N, where the second is empty from N up. *)
Definition ax_dg_xrel (N : nat) (k k0 : hcore) : Prop :=
  M.err k = M.err k0 /\ M.pc k = M.pc k0 /\
  (forall r, r < N -> M.vals k r = M.vals k0 r) /\
  (forall r, N <= r -> M.vals k0 r = 0).

Lemma ax_dg_xstep : forall N (Q : list hinstr) k k0,
  (forall i, In i Q -> exists r j, (i = M.INC r \/ i = M.DEC r j) /\ r < N) ->
  ax_dg_xrel N k k0 ->
  ax_dg_xrel N (sm_cstep UC.hprop_eqb UC.heval Q k) (sm_cstep UC.hprop_eqb UC.heval Q k0).
Proof.
  intros N Q k k0 HQ Hrel. pose proof Hrel as (He & Hp & Hv & Hz).
  assert (Hn : M.next_instr Q k = M.next_instr Q k0)
    by (unfold M.next_instr; rewrite He, Hp; reflexivity).
  unfold sm_cstep. rewrite Hn.
  destruct (M.next_instr Q k0) as [i |] eqn:Hi; [| exact Hrel].
  destruct (sm_next_some Q k0 i Hi) as (Ek0 & _ & _).
  assert (Ek : M.err k = false) by congruence.
  destruct (HQ i (sm2_next_in Q k0 i Hi)) as (r & j & [-> | ->] & Hr).
  - unfold M.cexec. rewrite Ek, Ek0. unfold ax_dg_xrel. simpl. repeat split; auto.
    + intros q Hq. unfold M.upd. destruct (Nat.eqb_spec q r) as [-> | Hne];
        [rewrite (Hv r Hr); reflexivity | apply Hv; exact Hq].
    + intros q Hq. unfold M.upd. destruct (Nat.eqb_spec q r) as [-> | Hne]; [lia | apply Hz; exact Hq].
  - unfold M.cexec. rewrite Ek, Ek0. unfold ax_dg_xrel.
    rewrite (Hv r Hr). destruct (M.vals k0 r) as [| u]; simpl; repeat split; auto.
    + intros q Hq. unfold M.upd. destruct (Nat.eqb_spec q r) as [-> | Hne];
        [reflexivity | apply Hv; exact Hq].
    + intros q Hq. unfold M.upd. destruct (Nat.eqb_spec q r) as [-> | Hne]; [lia | apply Hz; exact Hq].
Qed.

Lemma ax_dg_xrun : forall N (Q : list hinstr) n k k0,
  (forall i, In i Q -> exists r j, (i = M.INC r \/ i = M.DEC r j) /\ r < N) ->
  ax_dg_xrel N k k0 ->
  ax_dg_xrel N (sm_crun n Q k) (sm_crun n Q k0).
Proof.
  intros N Q n. induction n as [| n IH]; intros k k0 HQ H; [exact H |].
  simpl. apply IH; [exact HQ | apply ax_dg_xstep; assumption].
Qed.

Theorem ax_dg_mma_out : forall N' (P : list (mm_instr (pos (S N')))) (k : hcore) v0 m,
  M.err k = false -> M.pc k = 1 ->
  (forall p : pos (S N'), M.vals k (pos2nat p) = vec_pos v0 p) ->
  ((exists c (v' : Vector.t nat N'), sss_output (@mma_sss (S N')) (1, P) (1, v0) (c, Vector.cons nat m N' v')) <->
   (exists n, M.halted (sm_mma_host (S N') P) (sm_crun n (sm_mma_host (S N') P) k) /\
              M.vals (sm_crun n (sm_mma_host (S N') P) k) 0 = m)).
Proof.
  intros N' P k v0 m He Hp Hv.
  set (k0 := M.mkcore (fun r => if r <? S N' then M.vals k r else 0) (M.vers k) (M.pc k)
               (M.facts k) (M.chan k) (M.err k) : hcore).
  assert (Hm : sm_mmatch (S N') k0 (1, v0)).
  { unfold sm_mmatch. simpl. repeat split; auto.
    - intro p. pose proof (pos2nat_prop p) as Hlt.
      replace (pos2nat p <? S N') with true by (symmetry; apply Nat.ltb_lt; exact Hlt). apply Hv.
    - intros r Hr. replace (r <? S N') with false by (symmetry; apply Nat.ltb_ge; exact Hr). reflexivity. }
  assert (Hx : ax_dg_xrel (S N') k k0).
  { unfold ax_dg_xrel. simpl. repeat split; auto.
    - intros r Hr. replace (r <? S N') with true by (symmetry; apply Nat.ltb_lt; exact Hr). reflexivity.
    - intros r Hr. replace (r <? S N') with false by (symmetry; apply Nat.ltb_ge; exact Hr). reflexivity. }
  rewrite (sm_mma_host_out N' P k0 v0 m Hm).
  split; intros [n [Hh Hv0]]; exists n.
  - destruct (ax_dg_xrun (S N') (sm_mma_host (S N') P) n k k0 (ax_dg_mma_instr _ P) Hx) as (E1 & E2 & E3 & _).
    split.
    + unfold M.halted, M.next_instr in *. rewrite E1, E2. exact Hh.
    + rewrite E3 by lia. exact Hv0.
  - destruct (ax_dg_xrun (S N') (sm_mma_host (S N') P) n k k0 (ax_dg_mma_instr _ P) Hx) as (E1 & E2 & E3 & _).
    split.
    + unfold M.halted, M.next_instr in *. rewrite <- E1, <- E2. exact Hh.
    + rewrite <- E3 by lia. exact Hv0.
Qed.

Print Assumptions ax_dg_move.
Print Assumptions ax_dg_clear.
Print Assumptions ax_dg_clears.
Print Assumptions ax_dg_mma_out.
