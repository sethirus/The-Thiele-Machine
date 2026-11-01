(** TcNorm.v: a vendored alternate-Minsky program, made to leave its code
    through its last line.

    A program of the vendored machine may stop by jumping to any line outside
    its code. The identity instruction compiler, run through the vendored
    generic compiler, copies every instruction and sends every jump that
    leaves the code to the line just after the code. The compiled program
    stops exactly where the first one stops, in the same registers, and it
    always stops at the end of its own code. This is used so that a program
    can be followed by another program (TcPacked.v).

    Dependencies: Coq standard library, the vendored coq-undecidability
    library. No axioms and no unfinished proofs.                                        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Section Norm.
  Variable (n : nat).

  Let simul (v w : vec nat n) : Prop := v = w.

  Local Definition nicomp (lnk : nat -> nat) (i : nat) (x : mm_instr (pos n)) : list (mm_instr (pos n)) :=
    match x with
    | mm_inc r => mm_inc r :: nil
    | mm_dec r j => mm_dec r (lnk j) :: nil
    end.

  Local Definition nilen (x : mm_instr (pos n)) : nat := 1.

  Local Fact nicomp_len : forall lnk i x, length (nicomp lnk i x) = nilen x.
  Proof. intros lnk i [r | r j]; reflexivity. Qed.

  Local Lemma nicomp_sound :
    instruction_compiler_sound nicomp (@mma_sss n) (@mma_sss n) simul.
  Proof.
    intros lnk I i1 v1 i2 v2 w1 Hs Hl Hv. unfold simul in Hv. subst w1.
    destruct I as [x | x j]; simpl in Hl |- *;
      assert (Hl' : lnk (1 + i1) = 1 + lnk i1) by exact Hl.
    - apply mma_sss_INC_inv in Hs as [-> ->].
      exists (vec_change v1 x (S (vec_pos v1 x))). split; [| reflexivity].
      exists 1. split; [lia |]. apply sss_steps_1.
      apply in_sss_step with (l := nil) (r := nil); [simpl; lia |].
      rewrite Hl'. constructor.
    - destruct (vec_pos v1 x) as [| u] eqn:Hx.
      + apply mma_sss_DEC0_inv in Hs; [| exact Hx]. destruct Hs as [-> ->].
        exists v1. split; [| reflexivity].
        exists 1. split; [lia |]. apply sss_steps_1.
        apply in_sss_step with (l := nil) (r := nil); [simpl; lia |].
        rewrite Hl'. replace (lnk i1 + 1) with (1 + lnk i1) by lia.
        apply in_mma_sss_dec_0. exact Hx.
      + apply mma_sss_DEC1_inv with (u := u) in Hs; [| exact Hx]. destruct Hs as [-> ->].
        exists (vec_change v1 x u). split; [| reflexivity].
        exists 1. split; [lia |]. apply sss_steps_1.
        apply in_sss_step with (l := nil) (r := nil); [simpl; lia |].
        apply in_mma_sss_dec_1. exact Hx.
  Qed.

  Definition tc_norm : compiler_t (@mma_sss n) (@mma_sss n) simul.
  Proof.
    apply generic_compiler with nicomp nilen.
    + intros; apply nicomp_len.
    + apply mma_sss_total_ni.
    + apply mma_sss_fun.
    + apply nicomp_sound.
  Defined.

  (* the normalised code of a program, placed at address i *)
  Definition tc_normcode (P : list (mm_instr (pos n))) (i : nat) : list (mm_instr (pos n)) :=
    gc_code tc_norm (1, P) i.

  Theorem tc_normcode_halts : forall P v j w,
    sss_output (@mma_sss n) (1, P) (1, v) (j, w) ->
    forall i, sss_output (@mma_sss n) (i, tc_normcode P i) (i, v) (i + length (tc_normcode P i), w).
  Proof.
    intros P v j w Hout i.
    destruct (@compiler_t_output_sound' _ _ _ _ _ _ _ tc_norm (1, P) i v v j w eq_refl Hout) as [w' [Hw' Hs]].
    unfold simul in Hs. subst w'. exact Hw'.
  Qed.

  Theorem tc_normcode_terminates : forall P v i,
    sss_terminates (@mma_sss n) (i, tc_normcode P i) (i, v) <->
    sss_terminates (@mma_sss n) (1, P) (1, v).
  Proof.
    intros P v i. symmetry.
    apply (@compiler_t_term_equiv _ _ _ _ _ _ _ tc_norm (1, P) i v v eq_refl).
  Qed.
End Norm.

Print Assumptions tc_normcode_halts.
Print Assumptions tc_normcode_terminates.
