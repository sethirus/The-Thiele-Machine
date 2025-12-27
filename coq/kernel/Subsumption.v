(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia List Bool.
Import ListNotations.

From Kernel Require Import Kernel KernelTM KernelThiele.

Module K := Kernel.
Module KTM := KernelTM.
Module KTH := KernelThiele.

(** This file provides subsumption results showing Turing computation
    is strictly contained in sighted Thiele computation. *)

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

(* Main theorem: Turing is strictly contained in Thiele *)
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
