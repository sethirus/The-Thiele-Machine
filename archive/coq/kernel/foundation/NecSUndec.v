(** NecSUndec.v: what "undecidable in the library's sense" means for the
    small machine, and why the plain statement "no function decides it"
    cannot be a theorem here.

    The library's notion: undecidable P means that a Boolean decider for P
    would make the complement of single-tape binary Turing machine halting
    enumerable. The repository proves this for the small machine's halting
    problem by reduction from the library's two-counter machine.

    The plain statement "there is no function deciding halting of the small
    machine" is not provable in Coq: under the informative excluded middle
    (forall P, {P} + {~P}), a standard axiom consistent with Coq and
    provided by its standard library as excluded_middle_informative, such a
    function exists. This file proves that implication, with the axiom as
    an explicit premise of the theorem, so the result itself is closed. It is the precise reason the
    book's statement must be "in the library's sense" (a synthetic,
    computability-relative statement) and cannot be a plain one.        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability Definitions.
From Undecidability.TM Require Import SBTM.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec.
From Kernel Require Import EarnedCoreLinks.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* Under the informative excluded middle the small machine's halting
   problem has a Boolean decider in exactly the library's sense. *)
Theorem nec_s_halting_decidable_classically :
  (forall P : Prop, {P} + {~ P}) -> decidable EARNED_HALTING.
Proof.
  intro em.
  exists (fun q => if em (EARNED_HALTING q) then true else false).
  intro q. unfold reflects. destruct (em (EARNED_HALTING q)) as [H | H]; split;
    intro X; try reflexivity; try discriminate; try contradiction; exact H.
Qed.

(* So, under the same axiom, the library's undecidability of the small
   machine's halting problem is equivalent to the enumerability of the
   complement of Turing machine halting: the statement is relative, not an
   absolute "no decider exists". *)
Theorem nec_s_undecidable_is_relative :
  (forall P : Prop, {P} + {~ P}) ->
  (undecidable EARNED_HALTING <-> enumerable (complement SBTM_HALT)).
Proof.
  intro em. split.
  - intro H. apply H. exact (nec_s_halting_decidable_classically em).
  - intros H _. exact H.
Qed.

Print Assumptions nec_s_halting_decidable_classically.
Print Assumptions nec_s_undecidable_is_relative.
Print Assumptions earned_core_halting_undecidable.
Print Assumptions mm2_halting_iff.
