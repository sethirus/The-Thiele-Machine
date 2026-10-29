(** CmpHost.v: the fourth compiler stage, from counter-machine programs to
    programs of the multi-register host machine of minimal/EarnedMulti.v.

    The host machine has INC r (add 1 to register r) and DEC r j (when
    register r is positive, subtract 1 and go to j; when it is 0, go on to
    the next instruction), HALT, and the record instructions CHECK, COMMIT
    and CERTIFY. The counter machine of the vendored library has the other
    DEC: it goes on when the register is positive and goes to j when it is 0.
    One counter machine instruction becomes

      INC x                 INC x
      DEC x j  (at host address a)
                            DEC x (a + 3)      positive: subtract, go on
                            INC 0              zero: register 0 up to 1 ...
                            DEC 0 j            ... and back to 0, jump to j

    The host program has no record instruction, so a run of it leaves the
    facts, the commitment channel, the trap latch, the ledger and the
    certified flag as they were at the start (multi_plain_step of
    EarnedMulti.v). Register 0 is only used between the two last
    instructions, and holds the same value after them as before, so the
    translation does not need register 0 to be 0.

    cmp_hi is the host instruction with only INC and DEC, as a plain type;
    cmp_hconv maps it to the host instruction of EarnedMulti.v over any
    property language. The semantics cmp_hstep of cmp_hi acts on registers
    only. The first part of the file compiles counter machine programs to
    cmp_hi programs with the vendored compiler theory (sound and complete);
    the second part ties the host machine's own runner (run_prog of
    EarnedMulti.v) to cmp_hstep.

      cmp_host_output       a counter machine run that leaves the program is
                            matched by a run of the host program that leaves
                            it (halts), with the same registers
      cmp_host_output_conv  the converse
      cmp_host_run_fwd / cmp_host_run_bwd
                            a cmp_hstep run that leaves the program is run_prog
                            of EarnedMulti.v reaching a halted state with the
                            same pc and registers, and the converse; the
                            facts, channel, latch, ledger and flag of that
                            state are those of the start

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, minimal/EarnedMulti.v and the Cmp files before this one. No
    axioms and no unfinished proofs.                                                   *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports the Coq standard library, the vendored coq-undecidability
   library, minimal/EarnedMulti.v and the Cmp files. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedMulti.
Require Import Kernel.CmpLang Kernel.CmpBlocks.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

(* ================================================================= *)
(* Plain host instructions and their register semantics.              *)
(* ================================================================= *)

Inductive cmp_hi : Set :=
| HInc (r : nat)
| HDec (r : nat) (j : nat).

Definition cmp_hconv {prop : Type} (i : cmp_hi) : @Minimal.EarnedMulti.instr prop :=
  match i with
  | HInc r => Minimal.EarnedMulti.INC r
  | HDec r j => Minimal.EarnedMulti.DEC r j
  end.

Inductive cmp_hstep : cmp_hi -> (nat * (nat -> nat)) -> (nat * (nat -> nat)) -> Prop :=
| HSInc : forall r i e, cmp_hstep (HInc r) (i, e) (S i, cmp_upd e r (S (e r)))
| HSDec0 : forall r j i e, e r = 0 -> cmp_hstep (HDec r j) (i, e) (S i, e)
| HSDecS : forall r j i e u, e r = S u -> cmp_hstep (HDec r j) (i, e) (j, cmp_upd e r u).

Lemma cmp_hstep_fun : forall I st st1 st2, cmp_hstep I st st1 -> cmp_hstep I st st2 -> st1 = st2.
Proof.
  intros I st st1 st2 H1 H2. inversion H1; subst; inversion H2; subst; congruence.
Qed.

(* ================================================================= *)
(* The instruction compiler.                                          *)
(* ================================================================= *)

Definition cmp_hlen (I : cmp_mi) : nat := match I with mm_inc _ => 1 | mm_dec _ _ => 3 end.

Definition cmp_hcomp (lnk : nat -> nat) (i : nat) (I : cmp_mi) : list cmp_hi :=
  match I with
  | mm_inc x => [HInc x]
  | mm_dec x j => [HDec x (lnk (S i)); HInc 0; HDec 0 (lnk j)]
  end.

Lemma cmp_hcomp_length : forall lnk i I, length (cmp_hcomp lnk i I) = cmp_hlen I.
Proof. intros lnk i [x | x j]; reflexivity. Qed.

(* The registers agree at every register. *)
Definition cmp_hsim (v w : nat -> nat) : Prop := forall r, v r = w r.

Local Notation hsteps := (sss_steps cmp_hstep).

Lemma cmp_hprog_one : forall (i : cmp_hi) a e st2 P, (a, [i]) <sc P -> cmp_hstep i (a, e) st2 ->
  sss_step cmp_hstep P (a, e) st2.
Proof.
  intros i a e st2 P Hs Hst.
  eapply subcode_sss_step with (P := (a, [i])); [exact Hs |].
  apply in_sss_step with (l := []); [simpl; lia | exact Hst].
Qed.

Theorem cmp_hcomp_sound : instruction_compiler_sound cmp_hcomp mmstep cmp_hstep cmp_hsim.
Proof.
  intros lnk I i1 v1 i2 v2 w1 Hs Hl Hsim.
  inversion Hs as [i0 x0 v0 Eq1 | i0 x0 k0 v0 Hz Eq2 | i0 x0 k0 v0 u0 Hp Eq3]; subst.
  - (* INC x *)
    assert (E : lnk (S i1) = S (lnk i1)) by (cbn in Hl; lia).
    exists (cmp_upd w1 x0 (S (w1 x0))). split.
    + exists 1. split; [lia |]. apply sss_steps_1. rewrite E.
      apply (cmp_hprog_one (HInc x0) (lnk i1) w1); [apply subcode_refl | apply HSInc].
    + intros r. rewrite cmp_set_env. unfold cmp_upd. rewrite cmp_get_env.
      destruct (Nat.eqb r x0); [rewrite Hsim; reflexivity | apply Hsim].
  - (* DEC x k, register zero: jump to k, through register 0 *)
    rewrite cmp_get_env in Hz. assert (Hw : w1 x0 = 0) by (rewrite <- Hsim; exact Hz).
    set (c := [HDec x0 (lnk (S i1)); HInc 0; HDec 0 (lnk i2)]).
    set (P := (lnk i1, c)).
    set (w2 := cmp_upd w1 0 (S (w1 0))).
    assert (E2 : w2 0 = S (w1 0)) by (unfold w2; apply cmp_upd_same).
    assert (Ec : forall r, cmp_upd w2 0 (w1 0) r = w1 r).
    { intros r. unfold w2, cmp_upd. destruct (Nat.eqb r 0) eqn:E; [apply Nat.eqb_eq in E; subst; reflexivity | reflexivity]. }
    exists (cmp_upd w2 0 (w1 0)). split.
    + exists 3. split; [lia |].
      assert (H1 : (lnk i1, [HDec x0 (lnk (S i1))]) <sc P) by (eapply cmp_ins_at with (k := 0); [apply subcode_refl | reflexivity | lia]).
      assert (H2 : (S (lnk i1), [HInc 0]) <sc P) by (eapply cmp_ins_at with (k := 1); [apply subcode_refl | reflexivity | lia]).
      assert (H3 : (S (S (lnk i1)), [HDec 0 (lnk i2)]) <sc P) by (eapply cmp_ins_at with (k := 2); [apply subcode_refl | reflexivity | lia]).
      eapply in_sss_steps_S with (st2 := (S (lnk i1), w1)).
      { apply (cmp_hprog_one (HDec x0 (lnk (S i1))) (lnk i1) w1); [exact H1 | apply HSDec0; exact Hw]. }
      eapply in_sss_steps_S with (st2 := (S (S (lnk i1)), w2)).
      { apply (cmp_hprog_one (HInc 0) (S (lnk i1)) w1); [exact H2 | apply HSInc]. }
      apply sss_steps_1.
      apply (cmp_hprog_one (HDec 0 (lnk i2)) (S (S (lnk i1))) w2); [exact H3 | apply HSDecS; exact E2].
    + intros r. rewrite Ec. apply Hsim.
  - (* DEC x k, register positive: subtract and go on *)
    rewrite cmp_get_env in Hp. assert (Hw : w1 x0 = S u0) by (rewrite <- Hsim; exact Hp).
    exists (cmp_upd w1 x0 u0). split.
    + exists 1. split; [lia |]. apply sss_steps_1.
      replace (S i1) with (1 + i1) by lia.
      apply (cmp_hprog_one (HDec x0 (lnk (1 + i1))) (lnk i1) w1).
      * eapply cmp_ins_at with (k := 0); [apply subcode_refl | reflexivity | lia].
      * apply HSDecS. exact Hw.
    + intros r. rewrite cmp_set_env. unfold cmp_upd.
      destruct (Nat.eqb r x0); [reflexivity | apply Hsim].
Qed.


(* ================================================================= *)
(* Whole programs, with the vendored linker.                          *)
(* ================================================================= *)

Lemma cmp_mm_total : forall I st, exists st2, mmstep I st st2.
Proof. intros I st. destruct (mm_sss_env_total eq_nat_dec I st) as (t & H). exists t. exact H. Qed.

Lemma cmp_mm_fun2 : forall I st st1 st2, mmstep I st st1 -> mmstep I st st2 -> st1 = st2.
Proof. intros I st st1 st2 H1 H2. exact (mm_sss_env_fun H1 H2). Qed.

Definition cmp_herr (Px : nat * list cmp_mi) (iQ : nat) : nat := iQ + length_compiler cmp_hlen (snd Px).
Definition cmp_hlink (Px : nat * list cmp_mi) (iQ : nat) : nat -> nat :=
  linker cmp_hlen Px iQ (cmp_herr Px iQ).
Definition cmp_hcode (Px : nat * list cmp_mi) (iQ : nat) : list cmp_hi :=
  compiler cmp_hcomp cmp_hlen Px iQ (cmp_herr Px iQ).

Lemma cmp_hcode_length : forall Px iQ, length (cmp_hcode Px iQ) = length_compiler cmp_hlen (snd Px).
Proof. intros. unfold cmp_hcode. apply compiler_length, cmp_hcomp_length. Qed.

Lemma cmp_hlink_start : forall Px iQ, cmp_hlink Px iQ (fst Px) = iQ.
Proof. intros. unfold cmp_hlink. apply (linker_code_start cmp_hlen Px). Qed.

Lemma cmp_hlink_out : forall Px iQ j, out_code j Px -> cmp_hlink Px iQ j = iQ + length_compiler cmp_hlen (snd Px).
Proof.
  intros Px iQ j H. unfold cmp_hlink.
  rewrite (@linker_out_err _ cmp_hlen Px iQ (cmp_herr Px iQ) j); [reflexivity | | exact H].
  unfold cmp_herr. lia.
Qed.

Lemma cmp_hsubcode : forall Px iQ i rho,
  (i, [rho]) <sc Px ->
  (cmp_hlink Px iQ i, cmp_hcomp (cmp_hlink Px iQ) i rho) <sc (iQ, cmp_hcode Px iQ) /\
  cmp_hlink Px iQ (1 + i) = cmp_hlen rho + cmp_hlink Px iQ i.
Proof.
  intros Px iQ i rho H.
  exact (compiler_subcode cmp_hcomp cmp_hlen cmp_hcomp_length Px iQ (cmp_herr Px iQ) i rho H).
Qed.

Theorem cmp_host_sound : forall Px iQ i1 v1 i2 v2 w1,
  cmp_hsim v1 w1 -> sss_compute mmstep Px (i1, v1) (i2, v2) ->
  exists w2, cmp_hsim v2 w2 /\
    sss_compute cmp_hstep (iQ, cmp_hcode Px iQ) (cmp_hlink Px iQ i1, w1) (cmp_hlink Px iQ i2, w2).
Proof.
  intros Px iQ i1 v1 i2 v2 w1 Hs Hc.
  exact (compiler_sound cmp_hlen cmp_hcomp_length cmp_hcomp_sound
           (cmp_hlink Px iQ) (iQ, cmp_hcode Px iQ) (cmp_hsubcode Px iQ) w1 (conj Hs Hc)).
Qed.

Theorem cmp_host_complete : forall Px iQ i1 v1 w1 st,
  cmp_hsim v1 w1 -> sss_output cmp_hstep (iQ, cmp_hcode Px iQ) (cmp_hlink Px iQ i1, w1) st ->
  exists i2 v2 w2, cmp_hsim v2 w2 /\ sss_output mmstep Px (i1, v1) (i2, v2) /\
    sss_output cmp_hstep (iQ, cmp_hcode Px iQ) (cmp_hlink Px iQ i2, w2) st.
Proof.
  intros Px iQ i1 v1 w1 st Hs Ho.
  exact (compiler_complete' cmp_hlen cmp_hcomp_length cmp_mm_total cmp_hstep_fun
           cmp_hcomp_sound (cmp_hlink Px iQ) Px (cmp_hsubcode Px iQ) i1 v1 (conj Hs Ho)).
Qed.

Theorem cmp_host_output : forall Px iQ v1 i2 v2 w1,
  cmp_hsim v1 w1 -> sss_output mmstep Px (fst Px, v1) (i2, v2) ->
  exists w2, cmp_hsim v2 w2 /\
    sss_output cmp_hstep (iQ, cmp_hcode Px iQ) (iQ, w1) (iQ + length (cmp_hcode Px iQ), w2).
Proof.
  intros Px iQ v1 i2 v2 w1 Hs [Hc Hout].
  destruct (cmp_host_sound Px iQ _ _ _ _ w1 Hs Hc) as (w2 & Hs2 & Hc2).
  rewrite cmp_hlink_start, (cmp_hlink_out Px iQ i2 Hout) in Hc2.
  exists w2. split; [exact Hs2 |]. split.
  - rewrite cmp_hcode_length. exact Hc2.
  - unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl.
Qed.

Theorem cmp_host_output_conv : forall Px iQ v1 j w1 w2,
  cmp_hsim v1 w1 ->
  sss_output cmp_hstep (iQ, cmp_hcode Px iQ) (iQ, w1) (j, w2) ->
  exists i2 v2, cmp_hsim v2 w2 /\ sss_output mmstep Px (fst Px, v1) (i2, v2) /\
    j = iQ + length (cmp_hcode Px iQ).
Proof.
  intros Px iQ v1 j w1 w2 Hs Ho.
  assert (Ho' : sss_output cmp_hstep (iQ, cmp_hcode Px iQ) (cmp_hlink Px iQ (fst Px), w1) (j, w2))
    by (rewrite cmp_hlink_start; exact Ho).
  destruct (cmp_host_complete Px iQ (fst Px) v1 w1 (j, w2) Hs Ho') as (i2 & v2 & w2' & Hs2 & Hf & Hq).
  destruct Hf as [Hf Hfo]. destruct Hq as [Hq Hqo].
  assert (Hl : cmp_hlink Px iQ i2 = iQ + length (cmp_hcode Px iQ)).
  { rewrite cmp_hcode_length. apply cmp_hlink_out. exact Hfo. }
  assert (Hlo : out_code (fst (cmp_hlink Px iQ i2, w2')) (iQ, cmp_hcode Px iQ)).
  { cbn [fst]. rewrite Hl. unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl. }
  pose proof (sss_compute_stop Hlo Hq) as E. inversion E; subst.
  exists i2, v2. split; [exact Hs2 | split; [split; assumption | exact Hl]].
Qed.

Print Assumptions cmp_host_output.
Print Assumptions cmp_host_output_conv.

(* ================================================================= *)
(* The runner of EarnedMulti.v on these programs.                     *)
(* ================================================================= *)

Lemma cmp_mm_hstep_total : forall h i e, exists st2, cmp_hstep h (i, e) st2.
Proof.
  intros [r | r j] i e.
  - eexists. apply HSInc.
  - destruct (e r) eqn:E; eexists; [apply HSDec0 | apply HSDecS]; exact E.
Qed.

Ltac cmp_hclose Hv :=
  first [ reflexivity | congruence | (rewrite Nat.add_0_r; reflexivity) | (rewrite Bool.orb_false_r; reflexivity)
        | (intros r0; unfold Minimal.EarnedMulti.upd, cmp_upd; cbn [snd];
           match goal with |- context[Nat.eqb r0 ?r] => destruct (Nat.eqb r0 r) end;
           first [ reflexivity | (rewrite ?Hv; reflexivity) | apply Hv ])
        | exact Hv ].

Section CmpHostBridge.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

Local Notation hstate := (@Minimal.EarnedMulti.state prop).

(* The state s of the host is at address i with registers e, untrapped. *)
Definition cmp_hrel (s : hstate) (i : nat) (e : nat -> nat) : Prop :=
  Minimal.EarnedMulti.pc (Minimal.EarnedMulti.core_of s) = i /\
  (forall r, Minimal.EarnedMulti.vals (Minimal.EarnedMulti.core_of s) r = e r) /\
  Minimal.EarnedMulti.err (Minimal.EarnedMulti.core_of s) = false.

(* What a program of INC and DEC leaves alone. *)
Definition cmp_hsame (s t : hstate) : Prop :=
  Minimal.EarnedMulti.facts (Minimal.EarnedMulti.core_of s) = Minimal.EarnedMulti.facts (Minimal.EarnedMulti.core_of t) /\
  Minimal.EarnedMulti.chan (Minimal.EarnedMulti.core_of s) = Minimal.EarnedMulti.chan (Minimal.EarnedMulti.core_of t) /\
  Minimal.EarnedMulti.mu s = Minimal.EarnedMulti.mu t /\ Minimal.EarnedMulti.cert s = Minimal.EarnedMulti.cert t.

Lemma cmp_hsame_refl : forall s, cmp_hsame s s.
Proof. intros s. repeat split. Qed.
Lemma cmp_hsame_trans : forall s t u, cmp_hsame s t -> cmp_hsame t u -> cmp_hsame s u.
Proof. intros s t u (A & B & C & D) (A' & B' & C' & D'). repeat split; congruence. Qed.

Definition cmp_hprog (H : list cmp_hi) : list (@Minimal.EarnedMulti.instr prop) := map cmp_hconv H.

(* The instruction at address a of the program (the first at address 1). *)
Lemma cmp_hfetch : forall (H : list cmp_hi) a h, (a, [h]) <sc (1, H) ->
  Minimal.EarnedMulti.fetch (cmp_hprog H) a = Some (cmp_hconv h).
Proof.
  intros H a h (l & r & HH & Ha). simpl in HH, Ha. subst H.
  assert (a = S (length l)) by lia. subst a. unfold cmp_hprog. rewrite map_app. simpl.
  unfold Minimal.EarnedMulti.fetch. rewrite nth_error_app2; [| rewrite map_length; lia].
  rewrite map_length. replace (length l - length l) with 0 by lia. reflexivity.
Qed.

Lemma cmp_hfetch_none : forall (H : list cmp_hi) a, out_code a (1, H) ->
  Minimal.EarnedMulti.fetch (cmp_hprog H) a = None.
Proof.
  intros H a Ho. unfold Minimal.EarnedMulti.fetch. destruct a as [| a]; [reflexivity |].
  unfold cmp_hprog. apply nth_error_None. rewrite map_length.
  unfold out_code, code_end in Ho. simpl in Ho. lia.
Qed.

Lemma cmp_hfetch_some : forall (H : list cmp_hi) a, in_code a (1, H) ->
  exists h, (a, [h]) <sc (1, H).
Proof. intros H a Hi. apply in_code_subcode in Hi. exact Hi. Qed.

Lemma cmp_cexec_inc : forall k r,
  Minimal.EarnedMulti.err k = false ->
  Minimal.EarnedMulti.cexec prop_eqb eval k (Minimal.EarnedMulti.INC r) =
  Minimal.EarnedMulti.write k r (S (Minimal.EarnedMulti.vals k r)) (S (Minimal.EarnedMulti.pc k)).
Proof. intros k r H. unfold Minimal.EarnedMulti.cexec. rewrite H. reflexivity. Qed.

Lemma cmp_cexec_dec : forall k r j,
  Minimal.EarnedMulti.err k = false ->
  Minimal.EarnedMulti.cexec prop_eqb eval k (Minimal.EarnedMulti.DEC r j) =
  match Minimal.EarnedMulti.vals k r with
  | 0 => Minimal.EarnedMulti.goto k (S (Minimal.EarnedMulti.pc k))
  | S n => Minimal.EarnedMulti.write k r n j
  end.
Proof. intros k r j H. unfold Minimal.EarnedMulti.cexec. rewrite H. reflexivity. Qed.

(* An untrapped state at the address of a plain instruction takes the step. *)
Lemma cmp_hstep_run : forall (H : list cmp_hi) h a e st2 s,
  (a, [h]) <sc (1, H) -> cmp_hrel s a e -> cmp_hstep h (a, e) st2 ->
  cmp_hrel (Minimal.EarnedMulti.step prop_eqb eval (cmp_hprog H) s) (fst st2) (snd st2) /\
  cmp_hsame s (Minimal.EarnedMulti.step prop_eqb eval (cmp_hprog H) s).
Proof.
  intros H h a e st2 s Hsc (Hpc & Hv & Her) Hst.
  pose proof (cmp_hfetch H a h Hsc) as Hf.
  destruct s as [k mu cert]. cbn in Hpc, Hv, Her.
  assert (Hn : Minimal.EarnedMulti.next_instr (cmp_hprog H) k = Some (cmp_hconv h)).
  { unfold Minimal.EarnedMulti.next_instr. rewrite Her, Hpc, Hf. destruct h; reflexivity. }
  unfold Minimal.EarnedMulti.step. cbn [Minimal.EarnedMulti.core_of]. rewrite Hn.
  unfold Minimal.EarnedMulti.exec. cbn [Minimal.EarnedMulti.core_of].
  inversion Hst; subst; cbn [cmp_hconv Minimal.EarnedMulti.cost Minimal.EarnedMulti.fires].
  - rewrite cmp_cexec_inc by exact Her. unfold Minimal.EarnedMulti.write.
    repeat split; cbn [cmp_hrel Minimal.EarnedMulti.core_of Minimal.EarnedMulti.pc Minimal.EarnedMulti.vals Minimal.EarnedMulti.err
      Minimal.EarnedMulti.facts Minimal.EarnedMulti.chan Minimal.EarnedMulti.mu Minimal.EarnedMulti.cert];
      try cmp_hclose Hv.
  - rewrite cmp_cexec_dec by exact Her.
    assert (Hz : Minimal.EarnedMulti.vals k r = 0) by (rewrite Hv; assumption). rewrite Hz.
    unfold Minimal.EarnedMulti.goto.
    repeat split; cbn [cmp_hrel Minimal.EarnedMulti.core_of Minimal.EarnedMulti.pc Minimal.EarnedMulti.vals Minimal.EarnedMulti.err
      Minimal.EarnedMulti.facts Minimal.EarnedMulti.chan Minimal.EarnedMulti.mu Minimal.EarnedMulti.cert];
      try cmp_hclose Hv.
  - rewrite cmp_cexec_dec by exact Her.
    assert (Hz : Minimal.EarnedMulti.vals k r = S u) by (rewrite Hv; assumption). rewrite Hz.
    unfold Minimal.EarnedMulti.write.
    repeat split; cbn [cmp_hrel Minimal.EarnedMulti.core_of Minimal.EarnedMulti.pc Minimal.EarnedMulti.vals Minimal.EarnedMulti.err
      Minimal.EarnedMulti.facts Minimal.EarnedMulti.chan Minimal.EarnedMulti.mu Minimal.EarnedMulti.cert];
      try cmp_hclose Hv.
Qed.

(* A state at an address outside the program is halted. *)
Lemma cmp_hhalted : forall (H : list cmp_hi) s a e,
  cmp_hrel s a e -> out_code a (1, H) -> Minimal.EarnedMulti.halted (cmp_hprog H) (Minimal.EarnedMulti.core_of s).
Proof.
  intros H s a e (Hpc & Hv & Her) Ho. unfold Minimal.EarnedMulti.halted, Minimal.EarnedMulti.next_instr.
  rewrite Her, Hpc, (cmp_hfetch_none H a Ho). reflexivity.
Qed.

(* A halted untrapped state is at an address outside the program. *)
Lemma cmp_hhalted_out : forall (H : list cmp_hi) s a e,
  cmp_hrel s a e -> Minimal.EarnedMulti.halted (cmp_hprog H) (Minimal.EarnedMulti.core_of s) -> out_code a (1, H).
Proof.
  intros H s a e (Hpc & Hv & Her) Hh. destruct (in_out_code_dec a (1, H)) as [Hi | Ho]; [| exact Ho].
  exfalso. destruct (cmp_hfetch_some H a Hi) as (h & Hsc). pose proof (cmp_hfetch H a h Hsc) as Hf.
  unfold Minimal.EarnedMulti.halted, Minimal.EarnedMulti.next_instr in Hh.
  rewrite Her, Hpc, Hf in Hh. destruct h; discriminate.
Qed.

(* A run of the register semantics, inside the program, is a run of the host. *)
Theorem cmp_host_run_fwd : forall (H : list cmp_hi) k i e j e' s,
  sss_steps cmp_hstep (1, H) k (i, e) (j, e') -> cmp_hrel s i e ->
  cmp_hrel (Minimal.EarnedMulti.run_prog prop_eqb eval k (cmp_hprog H) s) j e' /\
  cmp_hsame s (Minimal.EarnedMulti.run_prog prop_eqb eval k (cmp_hprog H) s).
Proof.
  intros H k. induction k as [| k IH]; intros i e j e' s Hr Hs.
  - apply sss_steps_0_inv in Hr. inversion Hr; subst. simpl. split; [exact Hs | apply cmp_hsame_refl].
  - destruct (sss_steps_S_inv' Hr) as ((i2 & e2) & H1 & H2).
    destruct H1 as (k0 & l & h & r0 & d & HP & Hst & Hs1). simpl in HP. inversion HP; subst k0.
    inversion Hst; subst.
    assert (Hsc : (S (length l), [h]) <sc (1, l ++ h :: r0)) by (exists l, r0; split; [reflexivity | simpl; lia]).
    assert (Hs1' : cmp_hstep h (S (length l), d) (i2, e2)) by exact Hs1.
    destruct (cmp_hstep_run (l ++ h :: r0) h (S (length l)) d (i2, e2) s Hsc Hs Hs1') as (Hr1 & Hsm1).
    cbn [fst snd] in Hr1.
    destruct (IH i2 e2 j e' _ H2 Hr1) as (Hr2 & Hsm2).
    split; [exact Hr2 |]. eapply cmp_hsame_trans; [exact Hsm1 | exact Hsm2].
Qed.

(* A run of the host that halts, from a state that is at the start of the
   program, is a run of the register semantics that leaves the program. *)
Theorem cmp_host_run_bwd : forall (H : list cmp_hi) n i e s,
  cmp_hrel s i e ->
  Minimal.EarnedMulti.halted (cmp_hprog H) (Minimal.EarnedMulti.core_of (Minimal.EarnedMulti.run_prog prop_eqb eval n (cmp_hprog H) s)) ->
  exists j e', sss_output cmp_hstep (1, H) (i, e) (j, e') /\
    cmp_hrel (Minimal.EarnedMulti.run_prog prop_eqb eval n (cmp_hprog H) s) j e' /\
    cmp_hsame s (Minimal.EarnedMulti.run_prog prop_eqb eval n (cmp_hprog H) s).
Proof.
  intros H n. induction n as [| n IH]; intros i e s Hs Hh.
  - simpl in *. exists i, e. split; [| split; [exact Hs | apply cmp_hsame_refl]].
    split; [exists 0; constructor | eapply cmp_hhalted_out; eassumption].
  - destruct (in_out_code_dec i (1, H)) as [Hi | Ho].
    + destruct (cmp_hfetch_some H i Hi) as (h & Hsc).
      destruct (cmp_mm_hstep_total h i e) as (st2 & Hst).
      destruct (cmp_hstep_run H h i e st2 s Hsc Hs Hst) as (Hr1 & Hsm1).
      simpl in Hh.
      destruct (IH (fst st2) (snd st2) _ Hr1 Hh) as (j & e' & (Hc & Ho') & Hr2 & Hsm2).
      exists j, e'. split; [| split; [exact Hr2 | eapply cmp_hsame_trans; [exact Hsm1 | exact Hsm2]]].
      split; [| exact Ho'].
      destruct Hc as (k1 & Hk1). exists (S k1).
      eapply in_sss_steps_S; [| exact Hk1].
      destruct st2 as [i2 e2]. eapply cmp_hprog_one; [exact Hsc | exact Hst].
    + exists i, e. split; [split; [exists 0; constructor | exact Ho] |].
      assert (Hst : Minimal.EarnedMulti.step prop_eqb eval (cmp_hprog H) s = s).
      { destruct s as [k mu cert]. destruct Hs as (Hpc & Hv & Her). cbn in Hpc, Her.
        unfold Minimal.EarnedMulti.step, Minimal.EarnedMulti.next_instr. cbn [Minimal.EarnedMulti.core_of].
        rewrite Her, Hpc, (cmp_hfetch_none H i Ho). reflexivity. }
      assert (Hrun : Minimal.EarnedMulti.run_prog prop_eqb eval (S n) (cmp_hprog H) s = s).
      { simpl. rewrite Hst. apply Minimal.EarnedMulti.multi_run_prog_halted.
        eapply cmp_hhalted; eassumption. }
      rewrite Hrun. split; [exact Hs | apply cmp_hsame_refl].
Qed.

End CmpHostBridge.


(* ================================================================= *)
(* The host program of a counter machine program.                     *)
(* ================================================================= *)

Definition cmp_host_prog (Q : list cmp_mi) : list cmp_hi := cmp_hcode (1, Q) 1.

Section CmpHostFinal.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.

(* The host state after n steps of the host program from the start with
   registers w. *)
Definition cmp_host_at (Q : list cmp_mi) (w : nat -> nat) (n : nat) : @Minimal.EarnedMulti.state prop :=
  Minimal.EarnedMulti.run_prog prop_eqb eval n (cmp_hprog (cmp_host_prog Q)) (@Minimal.EarnedMulti.start prop w).

(* The state of the host is the end of a run of the plain program: halted,
   at the address after the program, with the registers v and every
   other field of the state as at the start. *)
Definition cmp_host_final (Q : list cmp_mi) (v : nat -> nat) (s : @Minimal.EarnedMulti.state prop) : Prop :=
  Minimal.EarnedMulti.halted (cmp_hprog (cmp_host_prog Q)) (Minimal.EarnedMulti.core_of s) /\
  Minimal.EarnedMulti.pc (Minimal.EarnedMulti.core_of s) = 1 + length (cmp_host_prog Q) /\
  (forall r, Minimal.EarnedMulti.vals (Minimal.EarnedMulti.core_of s) r = v r) /\
  Minimal.EarnedMulti.err (Minimal.EarnedMulti.core_of s) = false /\
  Minimal.EarnedMulti.facts (Minimal.EarnedMulti.core_of s) = [] /\
  Minimal.EarnedMulti.chan (Minimal.EarnedMulti.core_of s) = None /\
  Minimal.EarnedMulti.mu s = 0 /\ Minimal.EarnedMulti.cert s = false.

Lemma cmp_hrel_start : forall w, cmp_hrel (@Minimal.EarnedMulti.start prop w) 1 w.
Proof. intros w. repeat split. Qed.

Lemma cmp_host_final_of : forall Q w s j e',
  cmp_hrel s j e' -> cmp_hsame (@Minimal.EarnedMulti.start prop w) s ->
  Minimal.EarnedMulti.halted (cmp_hprog (cmp_host_prog Q)) (Minimal.EarnedMulti.core_of s) ->
  j = 1 + length (cmp_host_prog Q) ->
  cmp_host_final Q e' s.
Proof.
  intros Q w s j e' (Hpc & Hv & Her) (A & B & C & D) Hh Hj.
  unfold cmp_host_final. repeat split; try assumption.
  - rewrite Hpc. exact Hj.
  - rewrite <- A. reflexivity.
  - rewrite <- B. reflexivity.
  - rewrite <- C. reflexivity.
  - rewrite <- D. reflexivity.
Qed.

Theorem cmp_host_fwd : forall Q v1 j v2 w1,
  cmp_hsim v1 w1 -> sss_output mmstep (1, Q) (1, v1) (j, v2) ->
  exists n, cmp_host_final Q v2 (cmp_host_at Q w1 n).
Proof.
  intros Q v1 j v2 w1 Hs Ho.
  destruct (cmp_host_output (1, Q) 1 v1 j v2 w1 Hs Ho) as (w2 & Hs2 & (Hc & Hout)).
  destruct Hc as (k & Hk).
  destruct (cmp_host_run_fwd prop_eqb eval (cmp_host_prog Q) k 1 w1 _ w2 (@Minimal.EarnedMulti.start prop w1) Hk (cmp_hrel_start w1))
    as (Hr & Hsm).
  exists k.
  assert (Hf : cmp_host_final Q w2 (cmp_host_at Q w1 k)).
  { eapply cmp_host_final_of with (j := 1 + length (cmp_hcode (1, Q) 1)) (e' := w2); [exact Hr | exact Hsm | | reflexivity].
    eapply cmp_hhalted; [exact Hr |]. unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl. }
  destruct Hf as (A & B & C & D1 & D2 & D3 & D4 & D5). repeat split; try assumption.
  intros r. rewrite C. symmetry. apply Hs2.
Qed.

Theorem cmp_host_bwd : forall Q v1 w1 n,
  cmp_hsim v1 w1 ->
  Minimal.EarnedMulti.halted (cmp_hprog (cmp_host_prog Q)) (Minimal.EarnedMulti.core_of (cmp_host_at Q w1 n)) ->
  exists j v2, sss_output mmstep (1, Q) (1, v1) (j, v2) /\ cmp_host_final Q v2 (cmp_host_at Q w1 n).
Proof.
  intros Q v1 w1 n Hs Hh.
  destruct (cmp_host_run_bwd prop_eqb eval (cmp_host_prog Q) n 1 w1 (@Minimal.EarnedMulti.start prop w1)
              (cmp_hrel_start w1) Hh) as (j' & e' & Ho & Hr & Hsm).
  destruct (cmp_host_output_conv (1, Q) 1 v1 j' w1 e' Hs Ho) as (i2 & v2 & Hs2 & Hm & Hj).
  exists i2, v2. split; [exact Hm |].
  assert (Hf : cmp_host_final Q e' (cmp_host_at Q w1 n)).
  { eapply cmp_host_final_of with (j := j') (e' := e'); [exact Hr | exact Hsm | exact Hh | exact Hj]. }
  destruct Hf as (A & B & C & D1 & D2 & D3 & D4 & D5). repeat split; try assumption.
  intros r. rewrite C. symmetry. apply Hs2.
Qed.

End CmpHostFinal.

Print Assumptions cmp_host_fwd.
Print Assumptions cmp_host_bwd.
