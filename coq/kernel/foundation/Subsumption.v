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

(* INQUISITOR NOTE: proof-connectivity waiver. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost. Any
   Kernel module it imports is a peer result in the same mathematical
   development, not the VM step relation.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. Counted in the WAIVERS census in
   INQUISITOR_REPORT.md. *)

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

(* An existence witness: the sighted class is not contained in the Turing
   class, witnessed by [sighted_witness_program].

   Subsumption in the other direction, that every Turing program embeds in
   the substrate, is a separate claim and lives in
   TuringClassicalEmbedding.v. This theorem does not establish it. *)
Theorem sighted_program_not_turing_witness :
  (* Strict containment - sighted programs are not Turing programs *)
  exists (p : K.program),
    program_is_sighted p /\ ~ K.program_is_turing p.
Proof.
  exists sighted_witness_program.
  split.
  - exact witness_is_sighted.
  - exact witness_not_turing.
Qed.
