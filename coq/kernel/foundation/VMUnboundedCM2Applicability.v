(** A nonterminating CM2 instance and a terminating instance. The same
    increment/zero-branch-decrement pair in the earlier guest terminates;
    this regression makes the control-convention distinction explicit. *)
From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMUnboundedStep VMUnboundedCM2Interpreter
  VMUnboundedCM2Encoding VMUnboundedCM2Correctness.
From Kernel Require Import VMUnboundedMinskyInterpreter VMUnboundedMinskyCorrectness.

Definition cm2_loop_program := [CM2_Inc0; CM2_DecJump0 0].
Definition cm2_loop_config a b : CM2ConfigU :=
  {| cc_pc := 0; cc_c0 := a; cc_c1 := b |}.

Lemma cm2_loop_even_prefix : forall n a b,
  cm2_run_n cm2_loop_program (2*n) (cm2_loop_config a b) (cm2_loop_config a b).
Proof.
  induction n; intros a b.
  - constructor.
  - replace (2*S n) with (S (S (2*n))) by lia.
    eapply cm2_run_n_succ with
      (i := CM2_Inc0) (c1 := {| cc_pc := 1; cc_c0 := S a; cc_c1 := b |}).
    + reflexivity.
    + reflexivity.
    + eapply cm2_run_n_succ with (i := CM2_DecJump0 0) (c1 := cm2_loop_config a b).
      * reflexivity.
      * reflexivity.
      * apply IHn.
Qed.

Theorem cm2_loop_diverges : forall a b,
  cm2_diverges cm2_loop_program (cm2_loop_config a b).
Proof.
  intros a b n. eapply cm2_run_n_prefix.
  - apply (cm2_loop_even_prefix n a b).
  - lia.
Qed.

Theorem cm2_loop_host_never_halts : forall ambient a b fuel,
  ~ cm2_halted (run_vm_u fuel cm2_interpreter_program
    (cm2_total_config_encoding ambient cm2_loop_program (cm2_loop_config a b))).
Proof.
  intros ambient a b fuel [Hpc _].
  pose proof (proj1 (cm2_uniform_interpreter_raw_divergence_total ambient _ _)
    (cm2_loop_diverges a b)) as Hdiv.
  apply (Hdiv fuel). rewrite cm2_interpreter_program_length in Hpc. exact Hpc.
Qed.

Theorem cm2_empty_guest_halts : forall a b,
  cm2_halts [] (cm2_loop_config a b) (cm2_loop_config a b).
Proof. intros. apply cm2_halts_falloff; [constructor|reflexivity]. Qed.

Theorem zero_branch_pair_terminates : forall a b,
  minsky_halts [MU_Inc0; MU_JzDec0 0]
    {| mc_pc := 0; mc_c0 := a; mc_c1 := b |}
    {| mc_pc := 2; mc_c0 := a; mc_c1 := b |}.
Proof.
  intros a b. apply minsky_halts_falloff; [|reflexivity].
  eapply minsky_run_step with
    (i := MU_Inc0) (c1 := {| mc_pc := 1; mc_c0 := S a; mc_c1 := b |}).
  - reflexivity.
  - reflexivity.
  - eapply minsky_run_step with
      (i := MU_JzDec0 0) (c1 := {| mc_pc := 2; mc_c0 := a; mc_c1 := b |}).
    + reflexivity.
    + reflexivity.
    + constructor.
Qed.
