(** UniversalPBridge.v: a run of an alternate Minsky machine program is a
    run of the host machine of EarnedMultiPriced.v.

    This file is the priced counterpart of UniversalBridge.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    The vendored library (MinskyMachines/MMA.v) defines the alternate Minsky
    machine: n counters indexed by pos n, two instructions

      mm_inc x       x := x + 1, go to the next instruction
      mm_dec x j     if x > 0 then x := x - 1 and go to j,
                     else go to the next instruction

    and its semantics mma_sss on states (pc, vector of n numbers). Its
    library MinskyMachines/Util/MMA_pairing.v proves specifications for
    small programs built from these two instructions (JMP, JZ, ZERO, MOVE,
    MOVE2, PACK, HALF, UNPACK).

    The host instructions INC r and DEC r j of EarnedMultiPriced.v behave the same
    way. A renaming rho : pos n -> nat says which host register each
    counter lives in; lift rho turns a counter instruction into a host
    instruction. When the renaming is injective, a block of counter
    instructions placed inside a host program (the library's subcode
    relation, with the host program starting at address 1) runs on the
    host exactly as it runs on the alternate Minsky machine:

      pu_lift_cexec       one counter step is one host step, with the same
                       next pc and the same counter values; the version
                       of a register goes up by exactly 1 when its value
                       changes and stays put otherwise.
      pu_lift_steps       k counter steps are k host steps, every one of
                       them an instruction of the lifted block.
      pu_mma_compute_host the main lemma: a library computation from (i, v)
                       to (j, w) gives a host run from pc i with the
                       registers reading v to pc j with the registers
                       reading w. The fact table, channel, trap latch,
                       ledger and flag are unchanged. A register the
                       block never mentions keeps its value and version.
                       Versions never go down, and a register whose value
                       changed has a strictly larger version.
      pu_mma_compute_host_regs the same lemma for the standard renaming
                       pos2nat: counters below n are host registers below n,
                       and every register from n on is left alone.
      pu_mma_block_host   the form used by the block library: the renaming
                       is a vector of distinct register numbers, the run
                       starts at the block's first address, and every
                       register outside the vector keeps value and version.

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, and EarnedMultiPriced.v. No axioms, no Admitted.                     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
Require Minimal.EarnedMultiPriced.

Module M := Minimal.EarnedMultiPriced.

(* Shorthands for the parts of a host state. *)
Notation hv s r := (M.vals (M.core_of s) r).
Notation hver s r := (M.vers (M.core_of s) r).
Notation hpc s := (M.pc (M.core_of s)).
Notation herr s := (M.err (M.core_of s)).

(* ================================================================= *)
(* Renamings, lifting, agreement.                                     *)
(* ================================================================= *)

(* Host registers of a block, as a vector of distinct register numbers,
   are injective as a renaming. *)
Lemma pu_vec_pos_inj : forall n (rs : vec nat n), NoDup (vec_list rs) ->
  forall p q, vec_pos rs p = vec_pos rs q -> p = q.
Proof.
  induction rs as [| r n rs IH]; intros Hnd p q H.
  - exact (Fin.case0 (fun z => z = q) p).
  - simpl in Hnd. inversion Hnd as [| ? ? Hnin Hnd']. subst.
    revert H.
    refine (Fin.caseS' p (fun z => vec_pos (r ## rs) z = vec_pos (r ## rs) q -> z = q) _ _).
    + refine (Fin.caseS' q
        (fun z => vec_pos (r ## rs) Fin.F1 = vec_pos (r ## rs) z -> Fin.F1 = z) _ _).
      * intros _. reflexivity.
      * intros q' H. simpl in H. exfalso. apply Hnin. rewrite H. apply vec_list_In.
    + intros p'.
      refine (Fin.caseS' q
        (fun z => vec_pos (r ## rs) (Fin.FS p') = vec_pos (r ## rs) z -> Fin.FS p' = z) _ _).
      * intros H. simpl in H. exfalso. apply Hnin. rewrite <- H. apply vec_list_In.
      * intros q' H. simpl in H. f_equal. apply IH; assumption.
Qed.

Lemma pu_vec_pos_not_in : forall n (rs : vec nat n) r,
  ~ In r (vec_list rs) -> forall p, vec_pos rs p <> r.
Proof. intros n rs r H p E. apply H. rewrite <- E. apply vec_list_In. Qed.

Section Bridge.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

Local Notation instr := (@M.pu_instr prop).
Local Notation state := (@M.pu_state prop).
Local Notation core := (@M.pu_core prop).
Local Notation exec := (M.pu_exec prop_eqb eval).
Local Notation cexec := (M.pu_cexec prop_eqb eval).
Local Notation step := (M.pu_step prop_eqb eval).
Local Notation run := (M.pu_run prop_eqb eval).
Local Notation run_prog := (M.pu_run_prog prop_eqb eval).
Local Notation trace_of := (M.pu_trace_of prop_eqb eval).

(* A counter instruction as a host instruction. *)
Definition pu_lift {n} (rho : pos n -> nat) (i : mm_instr (pos n)) : instr :=
  match i with
  | mm_inc x => M.INC (rho x)
  | mm_dec x j => M.DEC (rho x) j
  end.

(* The host registers named by rho read the counter vector v. *)
Definition pu_agree {n} (rho : pos n -> nat) (k : core) (v : vec nat n) : Prop :=
  forall p, M.vals k (rho p) = vec_pos v p.

(* The counter vector read off the host registers named by rho. *)
Definition pu_hvec {n} (rho : pos n -> nat) (k : core) : vec nat n :=
  vec_set_pos (fun p => M.vals k (rho p)).

Lemma pu_agree_hvec : forall n (rho : pos n -> nat) k, pu_agree rho k (pu_hvec rho k).
Proof. intros n rho k p. unfold pu_hvec. rewrite vec_pos_set. reflexivity. Qed.

(* Fact table, channel, trap latch, ledger and flag are the same. *)
Definition pu_same_sub (s s' : state) : Prop :=
  M.facts (M.core_of s') = M.facts (M.core_of s) /\
  M.chan (M.core_of s') = M.chan (M.core_of s) /\
  herr s' = herr s /\ M.mu s' = M.mu s /\ M.cert s' = M.cert s.

(* Program Ph takes s to s' in some number of steps, every executed
   instruction an INC or a DEC. *)
Definition pu_hrun (Ph : list instr) (s s' : state) : Prop :=
  exists m, run_prog m Ph s = s' /\
            Forall (fun i => M.pu_plain i = true) (trace_of m Ph s).

(* Every register outside rs keeps its value and its version. *)
Definition pu_hframe (rs : list nat) (s s' : state) : Prop :=
  forall r, ~ In r rs -> hv s' r = hv s r /\ hver s' r = hver s r.

(* ================================================================= *)
(* Runs.                                                              *)
(* ================================================================= *)

Lemma pu_trace_of_halted : forall m P s,
  M.pu_halted P (M.core_of s) -> trace_of m P s = [].
Proof.
  intros [| m] P s H; [reflexivity |]. unfold M.pu_halted in H.
  simpl. rewrite H. reflexivity.
Qed.

Lemma pu_trace_of_add : forall n m P s,
  trace_of (n + m) P s = trace_of n P s ++ trace_of m P (run_prog n P s).
Proof.
  induction n as [| n IH]; intros m P s; [reflexivity |].
  simpl. unfold M.pu_step. destruct (M.pu_next_instr P (M.core_of s)) eqn:H.
  - simpl. f_equal. apply IH.
  - simpl. rewrite (M.pu_multi_run_prog_halted prop_eqb eval n P s H).
    rewrite pu_trace_of_halted by exact H. reflexivity.
Qed.

Lemma pu_run_vers_mono : forall tr s r, hver s r <= hver (run tr s) r.
Proof.
  induction tr as [| i tr IH]; intros s r; simpl; [lia |].
  pose proof (M.pu_multi_ver_mono prop_eqb eval (M.core_of s) i r) as H1.
  specialize (IH (exec s i) r). simpl in IH. lia.
Qed.

Lemma pu_run_same_ver_same_val : forall tr s r,
  hver (run tr s) r = hver s r -> hv (run tr s) r = hv s r.
Proof.
  induction tr as [| i tr IH]; intros s r H; simpl in *; [reflexivity |].
  pose proof (M.pu_multi_ver_mono prop_eqb eval (M.core_of s) i r) as H1.
  pose proof (pu_run_vers_mono tr (exec s i) r) as H2. simpl in H2.
  assert (E1 : M.vers (cexec (M.core_of s) i) r = hver s r) by lia.
  rewrite IH by (simpl; lia). simpl.
  apply M.pu_multi_ver_same_val. exact E1.
Qed.

Lemma pu_hrun_refl : forall Ph s, pu_hrun Ph s s.
Proof. intros Ph s. exists 0. split; [reflexivity | constructor]. Qed.

Lemma pu_hrun_trans : forall Ph s1 s2 s3, pu_hrun Ph s1 s2 -> pu_hrun Ph s2 s3 -> pu_hrun Ph s1 s3.
Proof.
  intros Ph s1 s2 s3 [m1 [E1 F1]] [m2 [E2 F2]]. exists (m1 + m2). split.
  - rewrite (M.pu_multi_run_prog_add prop_eqb eval), E1. exact E2.
  - rewrite pu_trace_of_add, E1. apply Forall_app. auto.
Qed.

Lemma pu_hrun_same_sub : forall Ph s s', pu_hrun Ph s s' -> pu_same_sub s s'.
Proof.
  intros Ph s s' [m [E F]]. subst s'.
  rewrite (M.pu_multi_run_prog_trace prop_eqb eval).
  apply (M.pu_multi_plain_run prop_eqb eval). apply Forall_forall. exact F.
Qed.

Lemma pu_hrun_vers_mono : forall Ph s s', pu_hrun Ph s s' -> forall r, hver s r <= hver s' r.
Proof.
  intros Ph s s' [m [E _]] r. subst s'.
  rewrite (M.pu_multi_run_prog_trace prop_eqb eval). apply pu_run_vers_mono.
Qed.

Lemma pu_hrun_val_moved : forall Ph s s', pu_hrun Ph s s' ->
  forall r, hv s' r <> hv s r -> hver s r < hver s' r.
Proof.
  intros Ph s s' [m [E _]] r Hne. subst s'.
  rewrite (M.pu_multi_run_prog_trace prop_eqb eval) in *.
  pose proof (pu_run_vers_mono (trace_of m Ph s) s r).
  destruct (Nat.eq_dec (hver (run (trace_of m Ph s) s) r) (hver s r)) as [Heq | Hne'].
  - exfalso. apply Hne. apply pu_run_same_ver_same_val. exact Heq.
  - lia.
Qed.

Lemma pu_hframe_refl : forall rs s, pu_hframe rs s s.
Proof. intros rs s r _. auto. Qed.

Lemma pu_hframe_trans : forall rs1 rs2 s1 s2 s3,
  pu_hframe rs1 s1 s2 -> pu_hframe rs2 s2 s3 -> pu_hframe (rs1 ++ rs2) s1 s3.
Proof.
  intros rs1 rs2 s1 s2 s3 H1 H2 r Hr.
  assert (N1 : ~ In r rs1) by (intro; apply Hr, in_or_app; auto).
  assert (N2 : ~ In r rs2) by (intro; apply Hr, in_or_app; auto).
  destruct (H1 r N1), (H2 r N2). split; congruence.
Qed.

Lemma pu_hframe_incl : forall rs rs' s s', incl rs rs' -> pu_hframe rs s s' -> pu_hframe rs' s s'.
Proof. intros rs rs' s s' Hi H r Hr. apply H. intro. apply Hr, Hi. assumption. Qed.

(* ================================================================= *)
(* Fetching from a block placed inside a host program.                *)
(* ================================================================= *)

Lemma pu_subcode_fetch : forall (o : nat) (l Ph : list instr) q i,
  subcode (o, l) (1, Ph) -> nth_error l q = Some i -> M.pu_fetch Ph (o + q) = Some i.
Proof.
  intros o l Ph q i Hsc H. simpl in Hsc. destruct Hsc as [pre [post [E Ho]]].
  subst Ph o. replace (1 + length pre + q) with (S (length pre + q)) by lia. simpl.
  rewrite nth_error_app2 by lia. replace (length pre + q - length pre) with q by lia.
  rewrite nth_error_app1; [exact H |]. apply nth_error_Some. congruence.
Qed.

Lemma pu_host_step_fetch : forall Ph s i,
  M.pu_fetch Ph (hpc s) = Some i -> herr s = false -> i <> M.HALT ->
  step Ph s = exec s i.
Proof.
  intros Ph s i Hf He Hh. unfold M.pu_step, M.pu_next_instr. rewrite He, Hf.
  destruct i; try reflexivity. congruence.
Qed.

(* One host step at a single instruction placed at the current pc. *)
Lemma pu_host_step_at : forall Ph s o i,
  subcode (o, [i]) (1, Ph) -> hpc s = o -> herr s = false -> i <> M.HALT ->
  run_prog 1 Ph s = exec s i.
Proof.
  intros Ph s o i Hsc Hpc He Hh. simpl. apply pu_host_step_fetch; [| exact He | exact Hh].
  rewrite Hpc, <- (Nat.add_0_r o). apply (pu_subcode_fetch o [i]); [exact Hsc | reflexivity].
Qed.

Lemma pu_host_trace_at : forall Ph s o i,
  subcode (o, [i]) (1, Ph) -> hpc s = o -> herr s = false -> i <> M.HALT ->
  trace_of 1 Ph s = [i].
Proof.
  intros Ph s o i Hsc Hpc He Hh. simpl. unfold M.pu_next_instr. rewrite He.
  rewrite Hpc, <- (Nat.add_0_r o), (pu_subcode_fetch o [i] Ph 0 i Hsc eq_refl).
  destruct i; try reflexivity. congruence.
Qed.

(* ================================================================= *)
(* One counter step is one host step.                                 *)
(* ================================================================= *)

Lemma pu_lift_plain : forall n (rho : pos n -> nat) i, M.pu_plain (pu_lift rho i) = true.
Proof. intros n rho []; reflexivity. Qed.

Lemma pu_lift_not_halt : forall n (rho : pos n -> nat) i, pu_lift rho i <> M.HALT.
Proof. intros n rho []; discriminate. Qed.

Lemma pu_lift_mentions_out : forall n (rho : pos n -> nat) i r,
  (forall p, rho p <> r) -> M.pu_mentions (pu_lift rho i) r = false.
Proof. intros n rho [x | x j] r H; simpl; apply Nat.eqb_neq; apply H. Qed.

Theorem pu_lift_cexec : forall n (rho : pos n -> nat),
  (forall p q, rho p = rho q -> p = q) ->
  forall ins i v j w (k : core),
  mma_sss ins (i, v) (j, w) ->
  M.pc k = i -> M.err k = false -> pu_agree rho k v ->
  let k' := cexec k (pu_lift rho ins) in
  M.pc k' = j /\ M.err k' = false /\ pu_agree rho k' w /\
  (forall r, M.vers k' r =
     if Nat.eqb (M.vals k' r) (M.vals k r) then M.vers k r else S (M.vers k r)).
Proof.
  intros n rho Hinj ins i v j w k H Hpc Herr Hag k'.
  assert (Hk : k' = match ins with
                    | mm_inc x => M.pu_write k (rho x) (S (M.vals k (rho x))) (S (M.pc k))
                    | mm_dec x q =>
                        match M.vals k (rho x) with
                        | 0 => M.pu_goto k (S (M.pc k))
                        | S u => M.pu_write k (rho x) u q
                        end
                    end)
    by (unfold k', M.pu_cexec; rewrite Herr; destruct ins; reflexivity).
  clearbody k'. subst k'.
  inversion H as [i0 x v0 E1 E2 E3 | i0 x q v0 Hz E1 E2 E3 | i0 x q v0 u Hu E1 E2 E3];
    subst; cbn [pu_lift].
  - (* INC *)
    split; [reflexivity |]. split; [exact Herr |]. split.
    + intro p. rewrite M.pu_multi_val_write.
      destruct (pos_eq_dec x p) as [<- | Hne].
      * rewrite Nat.eqb_refl, vec_change_eq by reflexivity. rewrite Hag. reflexivity.
      * rewrite vec_change_neq by exact Hne.
        destruct (Nat.eqb_spec (rho x) (rho p)) as [E | _]; [exfalso; apply Hne, Hinj, E |].
        apply Hag.
    + intro r. rewrite M.pu_multi_ver_write, M.pu_multi_val_write.
      destruct (Nat.eqb_spec (rho x) r) as [<- | _].
      * destruct (Nat.eqb_spec (S (M.vals k (rho x))) (M.vals k (rho x))); [lia | reflexivity].
      * rewrite Nat.eqb_refl. reflexivity.
  - (* DEC on zero *)
    rewrite (Hag x), Hz. simpl. split; [reflexivity |]. split; [exact Herr |]. split.
    + exact Hag.
    + intro r. rewrite Nat.eqb_refl. reflexivity.
  - (* DEC on a successor *)
    rewrite (Hag x), Hu. split; [reflexivity |]. split; [exact Herr |]. split.
    + intro p. rewrite M.pu_multi_val_write.
      destruct (pos_eq_dec x p) as [<- | Hne].
      * rewrite Nat.eqb_refl, vec_change_eq by reflexivity. reflexivity.
      * rewrite vec_change_neq by exact Hne.
        destruct (Nat.eqb_spec (rho x) (rho p)) as [E | _]; [exfalso; apply Hne, Hinj, E |].
        apply Hag.
    + intro r. rewrite M.pu_multi_ver_write, M.pu_multi_val_write.
      destruct (Nat.eqb_spec (rho x) r) as [<- | _].
      * rewrite (Hag x), Hu.
        destruct (Nat.eqb_spec u (S u)); [lia | reflexivity].
      * rewrite Nat.eqb_refl. reflexivity.
Qed.

(* ================================================================= *)
(* Many counter steps are as many host steps.                         *)
(* ================================================================= *)

Theorem pu_lift_steps : forall n (rho : pos n -> nat),
  (forall p q, rho p = rho q -> p = q) ->
  forall o B (Ph : list instr), subcode (o, map (pu_lift rho) B) (1, Ph) ->
  forall m st st', sss_steps (@mma_sss n) (o, B) m st st' ->
  forall s, hpc s = fst st -> herr s = false -> pu_agree rho (M.core_of s) (snd st) ->
  hpc (run_prog m Ph s) = fst st' /\ herr (run_prog m Ph s) = false /\
  pu_agree rho (M.core_of (run_prog m Ph s)) (snd st') /\
  Forall (fun i => In i (map (pu_lift rho) B)) (trace_of m Ph s) /\
  length (trace_of m Ph s) = m.
Proof.
  intros n rho Hinj o B Ph Hsc m st st' H.
  induction H as [st | m st1 st2 st3 H1 H2 IH]; intros s Hpc Herr Hag.
  - simpl. repeat split; auto.
  - destruct H1 as (k0 & L & ins & R & d & HP & Hst & Hone).
    inversion HP; subst. destruct st2 as (j, w). simpl in Hpc, Hag.
    assert (Hf : M.pu_fetch Ph (hpc s) = Some (pu_lift rho ins)).
    { rewrite Hpc. apply (pu_subcode_fetch k0 (map (pu_lift rho) (L ++ ins :: R)) Ph (length L)); [exact Hsc |].
      rewrite map_app. simpl. rewrite nth_error_app2 by (rewrite map_length; lia).
      rewrite map_length, Nat.sub_diag. reflexivity. }
    assert (Hn : M.pu_next_instr Ph (M.core_of s) = Some (pu_lift rho ins)).
    { unfold M.pu_next_instr. rewrite Herr, Hf. destruct ins; reflexivity. }
    destruct (pu_lift_cexec n rho Hinj ins (k0 + length L) d j w (M.core_of s) Hone Hpc Herr Hag)
      as [Hpc' [Herr' [Hag' _]]].
    specialize (IH (exec s (pu_lift rho ins)) Hpc' Herr' Hag').
    destruct IH as [I1 [I2 [I3 [I4 I5]]]].
    simpl. unfold M.pu_step. rewrite Hn.
    split; [exact I1 |]. split; [exact I2 |]. split; [exact I3 |]. split.
    + constructor; [| exact I4]. apply in_map. apply in_or_app. right. left. reflexivity.
    + simpl. rewrite I5. reflexivity.
Qed.

(* ================================================================= *)
(* The main lemma.                                                    *)
(* ================================================================= *)

Theorem pu_mma_compute_host : forall n (rho : pos n -> nat),
  (forall p q, rho p = rho q -> p = q) ->
  forall o B (Ph : list instr) i v j w s,
  subcode (o, map (pu_lift rho) B) (1, Ph) ->
  sss_compute (@mma_sss n) (o, B) (i, v) (j, w) ->
  hpc s = i -> herr s = false -> pu_agree rho (M.core_of s) v ->
  exists m,
    hpc (run_prog m Ph s) = j /\
    pu_agree rho (M.core_of (run_prog m Ph s)) w /\
    pu_same_sub s (run_prog m Ph s) /\
    pu_hrun Ph s (run_prog m Ph s) /\
    Forall (fun ins => In ins (map (pu_lift rho) B)) (trace_of m Ph s) /\
    (forall r, (forall ins, In ins B -> M.pu_mentions (pu_lift rho ins) r = false) ->
       hv (run_prog m Ph s) r = hv s r /\ hver (run_prog m Ph s) r = hver s r) /\
    (forall r, hver s r <= hver (run_prog m Ph s) r) /\
    (forall r, hv (run_prog m Ph s) r <> hv s r -> hver s r < hver (run_prog m Ph s) r).
Proof.
  intros n rho Hinj o B Ph i v j w s Hsc [m Hm] Hpc Herr Hag.
  destruct (pu_lift_steps n rho Hinj o B Ph Hsc m (i, v) (j, w) Hm s Hpc Herr Hag)
    as [H1 [_ [H3 [H4 _]]]].
  assert (Hr : pu_hrun Ph s (run_prog m Ph s)).
  { exists m. split; [reflexivity |].
    eapply Forall_impl; [| exact H4]. simpl. intros a Ha.
    apply in_map_iff in Ha as [ins [<- _]]. apply pu_lift_plain. }
  exists m. split; [exact H1 |]. split; [exact H3 |].
  split; [eapply pu_hrun_same_sub; exact Hr |]. split; [exact Hr |]. split; [exact H4 |].
  split; [| split].
  - intros r Hr'. rewrite (M.pu_multi_run_prog_trace prop_eqb eval).
    apply (M.pu_multi_frame_run prop_eqb eval). intros a Ha.
    rewrite Forall_forall in H4. apply H4 in Ha.
    apply in_map_iff in Ha as [ins [<- Hin]]. apply Hr', Hin.
  - apply (pu_hrun_vers_mono Ph s _ Hr).
  - apply (pu_hrun_val_moved Ph s _ Hr).
Qed.

(* The standard renaming: counter p lives in host register pos2nat p. *)
Corollary pu_mma_compute_host_regs : forall n o B (Ph : list instr) i v j w s,
  subcode (o, map (pu_lift (@pos2nat n)) B) (1, Ph) ->
  sss_compute (@mma_sss n) (o, B) (i, v) (j, w) ->
  hpc s = i -> herr s = false ->
  (forall p, hv s (pos2nat p) = vec_pos v p) ->
  exists m,
    hpc (run_prog m Ph s) = j /\
    (forall p, hv (run_prog m Ph s) (pos2nat p) = vec_pos w p) /\
    pu_same_sub s (run_prog m Ph s) /\
    pu_hrun Ph s (run_prog m Ph s) /\
    (forall r, n <= r -> hv (run_prog m Ph s) r = hv s r /\
                         hver (run_prog m Ph s) r = hver s r).
Proof.
  intros n o B Ph i v j w s Hsc Hc Hpc Herr Hag.
  destruct (pu_mma_compute_host n (@pos2nat n) (@pos2nat_inj n) o B Ph i v j w s Hsc Hc Hpc Herr Hag)
    as [m [H1 [H2 [H3 [H4 [_ [H6 _]]]]]]].
  exists m. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [exact H4 |].
  intros r Hr. apply H6. intros ins _. apply pu_lift_mentions_out.
  intros p E. pose proof (pos2nat_prop p). lia.
Qed.

(* The block form: the registers of the block are a vector of distinct
   host register numbers, and the run starts at the block's first
   address with the counters read off the host. *)
Theorem pu_mma_block_host : forall n (rs : vec nat n), NoDup (vec_list rs) ->
  forall o B (Ph : list instr) s j w,
  subcode (o, map (pu_lift (vec_pos rs)) B) (1, Ph) ->
  hpc s = o -> herr s = false ->
  sss_compute (@mma_sss n) (o, B) (o, pu_hvec (vec_pos rs) (M.core_of s)) (j, w) ->
  exists s', pu_hrun Ph s s' /\ hpc s' = j /\
    (forall p, hv s' (vec_pos rs p) = vec_pos w p) /\
    pu_hframe (vec_list rs) s s'.
Proof.
  intros n rs Hnd o B Ph s j w Hsc Hpc Herr Hc.
  destruct (pu_mma_compute_host n (vec_pos rs) (pu_vec_pos_inj n rs Hnd) o B Ph o _ j w s
              Hsc Hc Hpc Herr (pu_agree_hvec n _ _))
    as [m [H1 [H2 [_ [H4 [_ [H6 _]]]]]]].
  exists (run_prog m Ph s). split; [exact H4 |]. split; [exact H1 |]. split; [exact H2 |].
  intros r Hr. apply H6. intros ins _. apply pu_lift_mentions_out.
  apply pu_vec_pos_not_in. exact Hr.
Qed.

End Bridge.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_vec_pos_inj.
Print Assumptions pu_lift_cexec.
Print Assumptions pu_lift_steps.
Print Assumptions pu_mma_compute_host.
Print Assumptions pu_mma_compute_host_regs.
Print Assumptions pu_mma_block_host.
Print Assumptions pu_hrun_trans.
Print Assumptions pu_hrun_same_sub.
Print Assumptions pu_hrun_val_moved.
Print Assumptions pu_host_step_at.
