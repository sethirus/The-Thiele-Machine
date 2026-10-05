(** MM2ComplementUndec.v: the complement of pinned MM2 halting is
    undecidable in the upstream synthetic sense.  The proof composes the
    library's own reductions PCPb -> iPCPb -> BSM -> MM -> FRACTRAN_REG ->
    MMA2 -> MM2 under [reduces_complement], starting from
    [PCPb_compl_undec].  Nothing is assumed. *)

From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.
From Undecidability.PCP Require Import PCP PCP_undec.
From Undecidability.PCP.Reductions Require PCPb_iff_iPCPb.
From Undecidability.StackMachines Require Import BSM.
From Undecidability.StackMachines.Reductions Require Import iPCPb_to_BSM_HALTING.
From Undecidability.MinskyMachines Require Import MM MMA MM2.
From Undecidability.MinskyMachines.Reductions Require Import BSM_MM MMA2_to_MM2.
From Undecidability.FRACTRAN Require Import FRACTRAN Reductions.MM_FRACTRAN.
From Undecidability.MinskyMachines.Reductions Require Import FRACTRAN_to_MMA2.

Lemma PCPb_to_MM2 : PCPb ⪯ MM2_HALTING.
Proof.
  eapply reduces_transitive.
  { exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb. }
  eapply reduces_transitive; [apply iPCPb_to_BSM_HALTING|].
  eapply reduces_transitive; [apply BSM_MM_HALTING|].
  eapply reduces_transitive; [apply MM_FRACTRAN_REG_HALTING|].
  eapply reduces_transitive; [apply FRACTRAN_REG_MMA2_HALTING|].
  apply MMA2_MM2_HALTING.
Qed.

Theorem MM2_HALTING_compl_undec : undecidable (complement MM2_HALTING).
Proof.
  apply (undecidability_from_reducibility PCPb_compl_undec).
  apply reduces_complement, PCPb_to_MM2.
Qed.
