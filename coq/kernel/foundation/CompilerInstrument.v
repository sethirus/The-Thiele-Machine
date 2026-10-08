(** CompilerInstrument.v: counting the steps of a counter routine into a
    fresh register.

    A counter program R (vendored mm_sss_env semantics) that never names
    register T is instrumented by putting INC T in front of every
    instruction and sending every jump to the image of its target. The
    image is laid out by the vendored linker and compiler of
    compiler.v, two instructions per source instruction.

      1. Frame: a run of R does not touch T, and changing T (or any
         register R never names) at the start changes nothing else
         [cg_frame].
      2. Counting: every run of R from e in t steps is matched by a run of
         the instrumented program from e with T raised by exactly t
         [cg_steps_count], through the vendored compiler soundness theorem
         (compiler_sound) applied to the instruction compiler
         [cg_cicomp_sound].
      3. Reading T: when R leaves its code after t steps, the instrumented
         program started with T = 0 leaves its code with T = t and every
         other register as R leaves it, and every output of the
         instrumented program has T = t [cg_read_T_spec,
         cg_read_T_unique].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library and CompilerCodes.v. No axioms, no Admitted. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CompilerCodes.

(* ================================================================= *)
(* Instructions that do not name a register.                           *)
(* ================================================================= *)

Definition cg_reg_of (J : mm_instr nat) : nat :=
  match J with mm_inc x => x | mm_dec x _ => x end.

Definition cg_fresh (T : nat) (R : list (mm_instr nat)) : Prop :=
  forall J, In J R -> cg_reg_of J <> T.

Lemma cg_sss_step_in : forall (P : nat * list (mm_instr nat)) st st',
  sss_step (mm_sss_env eq_nat_dec) P st st' ->
  exists J, In J (snd P) /\ mm_sss_env eq_nat_dec J st st'.
Proof.
  intros P st st' (k & l & J & r & d & HP & Hst & Hs). subst P.
  exists J. split; [simpl; apply in_or_app; right; left; reflexivity | exact Hs].
Qed.

(* One step that does not name T, from two register files that agree off T. *)
Lemma cg_frame_step : forall T J i e j e1 e2,
  cg_reg_of J <> T ->
  mm_sss_env eq_nat_dec J (i, e) (j, e1) ->
  (forall y, y <> T -> e2 y = e y) ->
  exists e3, mm_sss_env eq_nat_dec J (i, e2) (j, e3) /\
    (forall y, y <> T -> e3 y = e1 y) /\ e3 T = e2 T /\ e1 T = e T.
Proof.
  intros T J i e j e1 e2 HJ Hs H.
  inversion Hs as [i' x e' | i' x k e' Hz | i' x k e' u Hu]; subst; simpl in HJ.
  - exists (set_env eq_nat_dec e2 x (S (get_env e2 x))). split; [constructor |].
    rewrite !cg_get_env. split; [| rewrite !cg_set_env_neq by auto; split; reflexivity].
    intros y Hy. destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite !cg_set_env_eq. rewrite H by auto. reflexivity.
    + rewrite !cg_set_env_neq by auto. apply H. exact Hy.
  - exists e2. split; [| split; [exact H | split; reflexivity]].
    constructor. rewrite cg_get_env in Hz |- *. rewrite H by auto. exact Hz.
  - exists (set_env eq_nat_dec e2 x u). split.
    + constructor. rewrite cg_get_env in Hu |- *. rewrite H by auto. exact Hu.
    + split; [| rewrite !cg_set_env_neq by auto; split; reflexivity].
      intros y Hy. destruct (Nat.eq_dec x y) as [-> | Hne].
      * rewrite !cg_set_env_eq. reflexivity.
      * rewrite !cg_set_env_neq by auto. apply H. exact Hy.
Qed.

(* Frame: a run of a program that never names T leaves T alone, and runs
   the same way from any register file that agrees off T. *)
Theorem cg_frame : forall T (P : nat * list (mm_instr nat)) n i e j e1 e2,
  cg_fresh T (snd P) ->
  sss_steps (mm_sss_env eq_nat_dec) P n (i, e) (j, e1) ->
  (forall y, y <> T -> e2 y = e y) ->
  exists e3, sss_steps (mm_sss_env eq_nat_dec) P n (i, e2) (j, e3) /\
    (forall y, y <> T -> e3 y = e1 y) /\ e3 T = e2 T /\ e1 T = e T.
Proof.
  intros T P n i e j e1 e2 HF Hs. revert e2.
  remember (i, e) as st eqn:Est. remember (j, e1) as st' eqn:Est'.
  revert i e Est j e1 Est'.
  induction Hs as [st | n st1 st2 st3 H1 H2 IH];
    intros i e Est j e1 Est' e2 He2; subst.
  - injection Est' as -> ->. exists e2. split; [constructor |].
    split; [exact He2 | split; reflexivity].
  - destruct st2 as [i2 f].
    destruct H1 as (k & l & J & r & d & HP & Hst & Hs1).
    assert (HJ : In J (snd P))
      by (rewrite HP; simpl; apply in_or_app; right; left; reflexivity).
    injection Hst as Hi Hd. subst d.
    destruct (cg_frame_step T J i e i2 f e2 (HF J HJ) Hs1 He2) as (f2 & Hs2 & Hf2 & HT2 & HT1).
    destruct (IH i2 f eq_refl j e1 eq_refl f2 Hf2) as (e3 & Hs3 & He3 & HT3 & HT4).
    exists e3. split.
    + econstructor; [| exact Hs3].
      rewrite HP. apply in_sss_step; [exact Hi | exact Hs2].
    + split; [exact He3 | split; congruence].
Qed.

(* ================================================================= *)
(* The counting semantics and the instruction compiler.               *)
(* ================================================================= *)

(* A counted state: the number of steps taken so far and the registers. *)
Definition cg_cstate : Type := (nat * env nat nat)%type.

(* A step of the source program that does not name T, counted. *)
Inductive cg_cstep (T : nat) : mm_instr nat -> nat * cg_cstate -> nat * cg_cstate -> Prop :=
| cg_cstep_in : forall J i c e j e',
    cg_reg_of J <> T ->
    mm_sss_env eq_nat_dec J (i, e) (j, e') ->
    cg_cstep T J (i, (c, e)) (j, (S c, e')).

Definition cg_relink (lnk : nat -> nat) (J : mm_instr nat) : mm_instr nat :=
  match J with mm_inc x => mm_inc x | mm_dec x j => mm_dec x (lnk j) end.

(* Each instruction becomes INC T followed by the instruction, its jump
   sent to the image of the target. *)
Definition cg_cicomp (T : nat) (lnk : nat -> nat) (i : nat) (J : mm_instr nat)
  : list (mm_instr nat) := [mm_inc T; cg_relink lnk J].

Definition cg_cilen (J : mm_instr nat) : nat := 2.

Lemma cg_cicomp_length : forall T lnk n J, length (cg_cicomp T lnk n J) = cg_cilen J.
Proof. reflexivity. Qed.

(* The instrumented registers hold the count in T and the source
   registers everywhere else. *)
Definition cg_csimul (T : nat) (ce : cg_cstate) (w : env nat nat) : Prop :=
  w T = fst ce /\ forall y, y <> T -> w y = snd ce y.

Lemma cg_two_steps : forall i J1 J2 (w : env nat nat) st1 st2,
  mm_sss_env eq_nat_dec J1 (i, w) st1 -> fst st1 = 1 + i ->
  mm_sss_env eq_nat_dec J2 st1 st2 ->
  sss_progress (mm_sss_env eq_nat_dec) (i, [J1; J2]) (i, w) st2.
Proof.
  intros i J1 J2 w st1 st2 H1 Hf H2. exists 2. split; [lia |].
  apply in_sss_steps_S with st1.
  - change (i, [J1; J2]) with (i, [] ++ J1 :: [J2]).
    apply in_sss_step; [simpl; lia | exact H1].
  - apply sss_steps_1. change (i, [J1; J2]) with (i, [J1] ++ J2 :: []).
    apply in_sss_step; [simpl; lia | exact H2].
Qed.

Theorem cg_cicomp_sound : forall T,
  instruction_compiler_sound (cg_cicomp T) (cg_cstep T) (mm_sss_env eq_nat_dec)
    (cg_csimul T).
Proof.
  intros T lnk J i1 v1 i2 v2 w1 Hs Hl [HT Hw].
  inversion Hs as [J' i c e j e' HJ Hm]; subst. simpl in HT, Hw. simpl in Hl.
  set (w' := set_env eq_nat_dec w1 T (S (get_env w1 T))).
  assert (HwT : w' T = S c) by (unfold w'; rewrite cg_set_env_eq, cg_get_env, HT; reflexivity).
  assert (Hw' : forall y, y <> T -> w' y = e y)
    by (intros y Hy; unfold w'; rewrite cg_set_env_neq by auto; apply Hw; exact Hy).
  assert (HT1 : mm_sss_env eq_nat_dec (mm_inc T) (lnk i1, w1) (1 + lnk i1, w'))
    by (unfold w'; constructor).
  inversion Hm as [i' x e0 | i' x k e0 Hz | i' x k e0 u Hu]; subst; simpl in HJ.
  - exists (set_env eq_nat_dec w' x (S (get_env w' x))). split.
    + rewrite Hl. apply (cg_two_steps _ _ _ _ _ _ HT1 eq_refl). simpl. constructor.
    + split; simpl.
      * rewrite cg_set_env_neq by auto. exact HwT.
      * intros y Hy. rewrite !cg_get_env. destruct (Nat.eq_dec x y) as [-> | Hne].
        -- rewrite !cg_set_env_eq. rewrite Hw' by auto. reflexivity.
        -- rewrite !cg_set_env_neq by auto. apply Hw'. exact Hy.
  - exists w'. split.
    + apply (cg_two_steps _ _ _ _ _ _ HT1 eq_refl). simpl. constructor.
      rewrite cg_get_env in Hz |- *. rewrite Hw' by auto. exact Hz.
    + split; [exact HwT | exact Hw'].
  - exists (set_env eq_nat_dec w' x u). split.
    + rewrite Hl. apply (cg_two_steps _ _ _ _ _ _ HT1 eq_refl). simpl.
      replace (2 + lnk i1) with (1 + (1 + lnk i1)) by lia. constructor.
      rewrite cg_get_env in Hu |- *. rewrite Hw' by auto. exact Hu.
    + split; simpl.
      * rewrite cg_set_env_neq by auto. exact HwT.
      * intros y Hy. destruct (Nat.eq_dec x y) as [-> | Hne].
        -- rewrite !cg_set_env_eq. reflexivity.
        -- rewrite !cg_set_env_neq by auto. apply Hw'. exact Hy.
Qed.

(* ================================================================= *)
(* The instrumented program.                                          *)
(* ================================================================= *)

Definition cg_count_err (R : list (mm_instr nat)) (iQ : nat) : nat :=
  iQ + length_compiler cg_cilen R.

Definition cg_count_link (R : list (mm_instr nat)) (i0 iQ : nat) : nat -> nat :=
  linker cg_cilen (i0, R) iQ (cg_count_err R iQ).

Definition cg_count_code (T : nat) (R : list (mm_instr nat)) (i0 iQ : nat)
  : list (mm_instr nat) :=
  compiler (cg_cicomp T) cg_cilen (i0, R) iQ (cg_count_err R iQ).

Lemma cg_count_lsum : forall R, length_compiler cg_cilen R = 2 * length R.
Proof. induction R as [| J R IH]; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma cg_count_code_length : forall T R i0 iQ,
  length (cg_count_code T R i0 iQ) = 2 * length R.
Proof.
  intros. unfold cg_count_code. rewrite compiler_length by apply cg_cicomp_length.
  apply cg_count_lsum.
Qed.

(* A run that never names T, counted. *)
Lemma cg_count_steps : forall T (P : nat * list (mm_instr nat)) n i e j e1 c,
  cg_fresh T (snd P) ->
  sss_steps (mm_sss_env eq_nat_dec) P n (i, e) (j, e1) ->
  sss_steps (cg_cstep T) P n (i, (c, e)) (j, (c + n, e1)).
Proof.
  intros T P n i e j e1 c HF Hs. revert c.
  remember (i, e) as st eqn:Est. remember (j, e1) as st' eqn:Est'.
  revert i e Est j e1 Est'.
  induction Hs as [st | n st1 st2 st3 H1 H2 IH];
    intros i e Est j e1 Est' c; subst.
  - injection Est' as -> ->. rewrite Nat.add_0_r. constructor.
  - destruct st2 as [i2 f].
    destruct H1 as (k & l & J & r & d & HP & Hst & Hs1).
    assert (HJ : In J (snd P))
      by (rewrite HP; simpl; apply in_or_app; right; left; reflexivity).
    injection Hst as Hi Hd. subst d.
    apply in_sss_steps_S with (i2, (S c, f)).
    + rewrite HP. apply in_sss_step; [exact Hi |]. constructor; [apply HF; exact HJ | exact Hs1].
    + replace (c + S n) with (S c + n) by lia. apply (IH i2 f eq_refl j e1 eq_refl).
Qed.

(* Counting: the instrumented program follows the source run and adds the
   number of source steps to T. *)
Theorem cg_steps_count : forall T R i0 iQ n i e j e1 c (w : env nat nat),
  cg_fresh T R ->
  sss_steps (mm_sss_env eq_nat_dec) (i0, R) n (i, e) (j, e1) ->
  cg_csimul T (c, e) w ->
  exists w1,
    sss_compute (mm_sss_env eq_nat_dec) (iQ, cg_count_code T R i0 iQ)
      (cg_count_link R i0 iQ i, w) (cg_count_link R i0 iQ j, w1) /\
    w1 T = c + n /\ (forall y, y <> T -> w1 y = e1 y).
Proof.
  intros T R i0 iQ n i e j e1 c w HF Hs Hw.
  assert (Hc : sss_steps (cg_cstep T) (i0, R) n (i, (c, e)) (j, (c + n, e1)))
    by (apply cg_count_steps; auto).
  destruct (compiler_sound cg_cilen (cg_cicomp_length T) (cg_cicomp_sound T)
              (cg_count_link R i0 iQ) (iQ, cg_count_code T R i0 iQ)
              (fun i' rho H => compiler_subcode (cg_cicomp T) cg_cilen
                                 (cg_cicomp_length T) (i0, R) iQ (cg_count_err R iQ)
                                 i' rho H)
              w (conj Hw (ex_intro _ n Hc)))
    as (w1 & [HT1 Hw1] & Hrun).
  exists w1. split; [exact Hrun | split; [exact HT1 | exact Hw1]].
Qed.

Lemma cg_count_link_start : forall R i0 iQ, cg_count_link R i0 iQ i0 = iQ.
Proof. intros. unfold cg_count_link. apply (linker_code_start cg_cilen (i0, R)). Qed.

Lemma cg_count_link_out : forall R i0 iQ j,
  out_code j (i0, R) -> cg_count_link R i0 iQ j = iQ + 2 * length R.
Proof.
  intros R i0 iQ j H. unfold cg_count_link.
  rewrite (@linker_out_err _ cg_cilen (i0, R) iQ (cg_count_err R iQ) j); [| | exact H].
  - unfold cg_count_err. rewrite cg_count_lsum. reflexivity.
  - unfold cg_count_err. simpl. lia.
Qed.

(* Reading T: started with T = 0 at the start of the instrumented code, the
   instrumented program leaves its code with T holding the exact number of
   source steps, and every other register as the source run leaves it. *)
Theorem cg_read_T_spec : forall T R i0 iQ t e j e1 (w : env nat nat),
  cg_fresh T R ->
  sss_steps (mm_sss_env eq_nat_dec) (i0, R) t (i0, e) (j, e1) ->
  out_code j (i0, R) ->
  w T = 0 -> (forall y, y <> T -> w y = e y) ->
  exists w1,
    sss_output (mm_sss_env eq_nat_dec) (iQ, cg_count_code T R i0 iQ)
      (iQ, w) (iQ + 2 * length R, w1) /\
    w1 T = t /\ (forall y, y <> T -> w1 y = e1 y).
Proof.
  intros T R i0 iQ t e j e1 w HF Hs Hj HwT Hw.
  destruct (cg_steps_count T R i0 iQ t i0 e j e1 0 w HF Hs (conj HwT Hw))
    as (w1 & Hrun & HT1 & Hw1).
  rewrite cg_count_link_start, (cg_count_link_out R i0 iQ j Hj) in Hrun.
  exists w1. split; [split; [exact Hrun |] | split; [exact HT1 | exact Hw1]].
  unfold out_code, code_end. simpl. rewrite cg_count_code_length. lia.
Qed.

(* Every output of the instrumented program, from such a start, reads t in T. *)
Corollary cg_read_T_unique : forall T R i0 iQ t e j e1 (w : env nat nat) st,
  cg_fresh T R ->
  sss_steps (mm_sss_env eq_nat_dec) (i0, R) t (i0, e) (j, e1) ->
  out_code j (i0, R) ->
  w T = 0 -> (forall y, y <> T -> w y = e y) ->
  sss_output (mm_sss_env eq_nat_dec) (iQ, cg_count_code T R i0 iQ) (iQ, w) st ->
  snd st T = t.
Proof.
  intros T R i0 iQ t e j e1 w st HF Hs Hj HwT Hw Ho.
  destruct (cg_read_T_spec T R i0 iQ t e j e1 w HF Hs Hj HwT Hw) as (w1 & Ho1 & HT1 & _).
  assert (st = (iQ + 2 * length R, w1)) as ->.
  { apply (sss_output_fun (fun i s t1 t2 H1 H2 => mm_sss_env_fun H1 H2) Ho Ho1). }
  exact HT1.
Qed.

Print Assumptions cg_sss_step_in.
Print Assumptions cg_frame_step.
Print Assumptions cg_frame.
Print Assumptions cg_cicomp_length.
Print Assumptions cg_two_steps.
Print Assumptions cg_cicomp_sound.
Print Assumptions cg_count_lsum.
Print Assumptions cg_count_code_length.
Print Assumptions cg_count_steps.
Print Assumptions cg_steps_count.
Print Assumptions cg_count_link_start.
Print Assumptions cg_count_link_out.
Print Assumptions cg_read_T_spec.
Print Assumptions cg_read_T_unique.
