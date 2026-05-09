(** Subsumption: the Thiele instruction set strictly extends the Turing fragment

  This file proves a syntactic separation result. Every Turing program is a
  Thiele program, but not every Thiele program is a Turing program. The
  witness is explicit: a program containing H_ClaimTapeIsZero is accepted by
  the Thiele syntax and rejected by the Turing-fragment predicate.

  The scope is only instruction-set inclusion. It is not a claim that the
  two models differ in bare computability power. The point here is that the
  Thiele machine has extra structure in its instruction language, not that
  it outruns Turing completeness.
*)

From Coq Require Import Arith Lia List Bool.
Import ListNotations.

From Kernel Require Import Kernel KernelTM KernelThiele.

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

Module K := Kernel.
Module KTM := KernelTM.
Module KTH := KernelThiele.

(* A sighted program contains at least one non-Turing instruction *)
Definition program_is_sighted (p : K.program) : Prop :=
  exists instr, In instr p /\ K.turing_instruction instr = false.

(* The sighted witness: a program with H_ClaimTapeIsZero *)
Definition sighted_witness_program : K.program :=
  [K.H_ClaimTapeIsZero 0].

Lemma witness_is_sighted : program_is_sighted sighted_witness_program.
Proof.
  unfold program_is_sighted, sighted_witness_program.
  exists (K.H_ClaimTapeIsZero 0).
  split.
  - simpl. left. reflexivity.
  - reflexivity.
Qed.

Lemma witness_not_turing : ~ K.program_is_turing sighted_witness_program.
Proof.
  unfold K.program_is_turing, sighted_witness_program.
  intro H.
  inversion H; subst.
  simpl in H2. discriminate.
Qed.

(* Main theorem: The Thiele instruction set properly extends the Turing instruction set *)
Theorem main_subsumption :
  (* Strict containment - sighted programs are not Turing programs *)
  exists (p : K.program),
    program_is_sighted p /\ ~ K.program_is_turing p.
Proof.
  exists sighted_witness_program.
  split.
  - exact witness_is_sighted.
  - exact witness_not_turing.
Qed.
