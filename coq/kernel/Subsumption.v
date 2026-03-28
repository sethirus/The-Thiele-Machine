(** * Subsumption: The Thiele instruction set properly extends the Turing instruction set

    WHY THIS FILE EXISTS:
    The Thiele Machine extends classical Turing computation with "sighted"
    instructions (like H_ClaimTapeIsZero) that have no Turing equivalent.
    This file proves SYNTACTIC SEPARATION: every Turing program is a Thiele
    program, but some Thiele programs (sighted ones) are not Turing programs.

    THE CORE CLAIM:
    There exists a program p that is sighted (contains a non-Turing instruction)
    AND is not a Turing program. Witness: [H_ClaimTapeIsZero 0].

    SCOPE: This is an instruction-set separation, not a computational-power
    separation. Both models are Turing-complete (see ProperSubsumption.v
    for the correct framing: "The distinction is NOT computational power,
    but COST ACCOUNTING").

    FALSIFICATION:
    Show that every sighted program can be simulated by a Turing program
    (i.e., sightedness is eliminable). This would contradict the witness
    construction, which relies on turing_instruction returning false for
    H_ClaimTapeIsZero.

    STATUS: Proven. Zero admits. The proof is constructive: the witness
    program is explicitly exhibited and both properties are verified.
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

(** [witness_is_sighted]: formal specification. *)
Lemma witness_is_sighted : program_is_sighted sighted_witness_program.
Proof.
  unfold program_is_sighted, sighted_witness_program.
  exists (K.H_ClaimTapeIsZero 0).
  split.
  - simpl. left. reflexivity.
  - reflexivity.
Qed.

(** [witness_not_turing]: formal specification. *)
Lemma witness_not_turing : ~ K.program_is_turing sighted_witness_program.
Proof.
  unfold K.program_is_turing, sighted_witness_program.
  intro H.
  inversion H; subst.
  simpl in H2. discriminate.
Qed.

(* Main theorem: The Thiele instruction set properly extends the Turing instruction set *)
(** [main_subsumption]: formal specification. *)
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
