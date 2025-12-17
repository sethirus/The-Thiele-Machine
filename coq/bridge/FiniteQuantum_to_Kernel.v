From Coq Require Import List Bool Arith.PeanoNat Lia QArith ZArith.
Import ListNotations.
Open Scope Q_scope.

Require Import VMStep.
Require Import CHSH.

(** * Bridge: finite “quantum-admissible” prediction engine -> kernel receipts

    This bridge mirrors [bridge/BoxWorld_to_Kernel.v], but targets a finite
    *Tsirelson-envelope* instance used by the runtime policy.

    - We define an operational “prediction engine output” as a finite list of
      CHSH trials (x,y,a,b) with bits.
    - The translation compiles trials to the non-forgeable receipt channel
      [instr_chsh_trial].
    - The simulation theorem proves the receipt decoder recovers the exact
      trial stream.

    Additionally, we provide a concrete finite dataset whose empirical CHSH is
    exactly the policy threshold 5657/2000.

    Note: this is not a real-analysis derivation of $2\sqrt{2}$; it is a
    receipt-defined finite-domain admissibility theorem matching the VM’s
    conservative bound constant.
*)

Module FiniteQuantumToKernel.

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

(** ------------------------------------------------------------------------- *)
(** ** A concrete finite Tsirelson-envelope dataset

    We build a balanced 2x2 dataset with n_per_setting = 4000.

    - For (1,1), (1,0), (0,1): correlator E=+1 (always a=b).
    - For (0,0): correlator E00 = 343/2000.

    Under the repo convention S = E11 + E10 + E01 - E00, this yields

      S = 3 - 343/2000 = 5657/2000.
*)

Definition n_per_setting : nat := 4000%nat.

Definition t11 : TheoryTrial := {| KC.t_x := 1; KC.t_y := 1; KC.t_a := 0; KC.t_b := 0 |}.
Definition t10 : TheoryTrial := {| KC.t_x := 1; KC.t_y := 0; KC.t_a := 0; KC.t_b := 0 |}.
Definition t01 : TheoryTrial := {| KC.t_x := 0; KC.t_y := 1; KC.t_a := 0; KC.t_b := 0 |}.
Definition t00_same : TheoryTrial := {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 0 |}.
Definition t00_diff : TheoryTrial := {| KC.t_x := 0; KC.t_y := 0; KC.t_a := 0; KC.t_b := 1 |}.

Definition tsirelson_envelope_program : TheoryProgram :=
  repeat t11 n_per_setting ++
  repeat t10 n_per_setting ++
  repeat t01 n_per_setting ++
  repeat t00_same 2343 ++
  repeat t00_diff 1657.

Lemma trial_bits_ok_all_zeros_ones :
  forall x y a b,
    (x = 0%nat \/ x = 1%nat) ->
    (y = 0%nat \/ y = 1%nat) ->
    (a = 0%nat \/ a = 1%nat) ->
    (b = 0%nat \/ b = 1%nat) ->
    trial_bits_ok {| KC.t_x := x; KC.t_y := y; KC.t_a := a; KC.t_b := b |}.
Proof.
  intros x y a b Hx Hy Ha Hb.
  unfold trial_bits_ok, is_bit.
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy];
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb];
  subst; simpl; repeat split; reflexivity.
Qed.

Lemma program_bits_ok_repeat :
  forall t n,
    trial_bits_ok t ->
    program_bits_ok (repeat t n).
Proof.
  intros t n Hok.
  induction n as [|n IH]; simpl.
  - constructor.
  - constructor; auto.
Qed.

Lemma tsirelson_envelope_program_bits_ok : program_bits_ok tsirelson_envelope_program.
Proof.
  unfold tsirelson_envelope_program.
  repeat (apply Forall_app; split).
  - apply program_bits_ok_repeat.
    apply (trial_bits_ok_all_zeros_ones 1 1 0 0); auto.
  - apply program_bits_ok_repeat.
    apply (trial_bits_ok_all_zeros_ones 1 0 0 0); auto.
  - apply program_bits_ok_repeat.
    apply (trial_bits_ok_all_zeros_ones 0 1 0 0); auto.
  - apply program_bits_ok_repeat.
    apply (trial_bits_ok_all_zeros_ones 0 0 0 0); auto.
  - apply program_bits_ok_repeat.
    apply (trial_bits_ok_all_zeros_ones 0 0 0 1); auto.
Qed.

Theorem tsirelson_envelope_program_chsh :
  KC.chsh tsirelson_envelope_program == (5657#2000).
Proof.
  vm_compute.
  reflexivity.
Qed.

Corollary tsirelson_envelope_compiled_chsh :
  KC.chsh (KC.trials_of_receipts (compile tsirelson_envelope_program)) == (5657#2000).
Proof.
  rewrite simulation_correctness_trials.
  - exact tsirelson_envelope_program_chsh.
  - exact tsirelson_envelope_program_bits_ok.
Qed.

End FiniteQuantumToKernel.
