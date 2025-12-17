From Coq Require Import List Bool Arith.PeanoNat Lia QArith ZArith.
Import ListNotations.
Open Scope Q_scope.

Require Import VMStep.
Require Import CHSH.

(** * Bridge: finite box-world predictions -> kernel receipts

    This file makes the slogan “physics embeds into the kernel” *meaningful* in the
    narrow operational sense:

    - A TheoryProgram is a finite list of CHSH trials (x,y,a,b) with bits.
    - The translation \[\[·\]\] compiles the program into kernel instructions
      emitting exactly those trials via [instr_chsh_trial].
    - The simulation theorem proves that decoding the kernel receipts recovers
      the original theory trials (semantics-preserving embedding of observables).

    This is a *crisp, falsifiable* claim: any counterexample trace breaks it.
*)

Module BoxWorldToKernel.

Module KC := KernelCHSH.
Import VMStep.VMStep.

Definition TheoryTrial : Type := KC.Trial.
Definition TheoryProgram : Type := list TheoryTrial.

Definition trial_bits_ok (t : TheoryTrial) : Prop :=
  is_bit t.(KC.t_x) = true /\
  is_bit t.(KC.t_y) = true /\
  is_bit t.(KC.t_a) = true /\
  is_bit t.(KC.t_b) = true.

Definition program_bits_ok (p : TheoryProgram) : Prop :=
  Forall trial_bits_ok p.

Definition compile_trial (t : TheoryTrial) : vm_instruction :=
  instr_chsh_trial t.(KC.t_x) t.(KC.t_y) t.(KC.t_a) t.(KC.t_b) 0%nat.

Definition compile (p : TheoryProgram) : list vm_instruction :=
  map compile_trial p.

Lemma trial_bits_ok_implies_chsh_bits_ok :
  forall t,
    trial_bits_ok t ->
    chsh_bits_ok t.(KC.t_x) t.(KC.t_y) t.(KC.t_a) t.(KC.t_b) = true.
Proof.
  intros t [Hx [Hy [Ha Hb]]].
  unfold chsh_bits_ok.
  rewrite Hx, Hy, Ha, Hb.
  reflexivity.
Qed.

(** ** Simulation theorem

    Decoding trials from the compiled kernel receipts recovers the theory’s
    trial stream exactly.
*)
Theorem simulation_correctness_trials :
  forall p,
    program_bits_ok p ->
    KC.trials_of_receipts (compile p) = p.
Proof.
  induction p as [|t tl IH]; intros Hok; simpl.
  - reflexivity.
  - inversion Hok as [|t' tl' Ht_ok Htl_ok]; subst.
    unfold KC.is_trial_instr.
    simpl.
    rewrite (trial_bits_ok_implies_chsh_bits_ok t Ht_ok).
    simpl.
    destruct t as [x y a b]; simpl.
    rewrite (IH Htl_ok).
    reflexivity.
Qed.

Corollary simulation_correctness_chsh_value :
  forall p,
    program_bits_ok p ->
    KC.chsh (KC.trials_of_receipts (compile p)) = KC.chsh p.
Proof.
  intros p Hok.
  rewrite simulation_correctness_trials with (p := p); auto.
Qed.

(** ** A crisp domain instance: a finite supra-CHSH empirical program

    This is a concrete “prediction engine output” for an experiment: a finite
    multiset of trials. It yields CHSH = 16/5 (> Tsirelson bound).
*)

Definition supra_16_5_program : TheoryProgram :=
  [ (* (1,1): +1 *) {| KC.t_x := 1; KC.t_y := 1; KC.t_a := 0; KC.t_b := 0 |};
    (* (1,0): +1 *) {| KC.t_x := 1; KC.t_y := 0; KC.t_a := 0; KC.t_b := 0 |};
    (* (0,1): +1 *) {| KC.t_x := 0; KC.t_y := 1; KC.t_a := 0; KC.t_b := 0 |};
    (* (0,0): two +1 and three -1 so E(0,0) = -1/5 *)
    {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 0 |};
    {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 0 |};
    {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 1 |};
    {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 1 |};
    {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 1 |}
  ].

Lemma supra_16_5_program_bits_ok : program_bits_ok supra_16_5_program.
Proof.
  repeat constructor; unfold trial_bits_ok, is_bit; simpl; try reflexivity.
Qed.

Theorem supra_16_5_program_chsh :
  KC.chsh supra_16_5_program = (16#5).
Proof.
  vm_compute. reflexivity.
Qed.

End BoxWorldToKernel.
