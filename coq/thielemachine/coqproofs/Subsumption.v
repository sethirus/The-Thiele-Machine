(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia.

From Kernel Require Import Kernel KernelTM KernelThiele Subsumption.

Module K := Kernel.
Module KTM := KernelTM.
Module KTH := KernelThiele.
Module KS := Kernel.Subsumption.

(** This file provides a proved subsumption result by reusing the
    kernel-level Thiele-vs-Turing simulation and strict containment
    theorems.

    It intentionally avoids placeholder `True` definitions and does not
    introduce new axioms or parameters. *)

Theorem turing_subsumption :
  forall fuel prog st,
    K.program_is_turing prog ->
    KTM.run_tm fuel prog st = KTH.run_thiele fuel prog st.
Proof.
  exact KS.thiele_simulates_turing.
Qed.

Theorem strict_separation :
  exists (p : K.program),
    KTM.run_tm 1 p KS.initial_state <> KS.target_state /\
    KTH.run_thiele 1 p KS.initial_state = KS.target_state.
Proof.
  exact KS.turing_is_strictly_contained.
Qed.

Theorem main_subsumption :
  (forall fuel prog st,
    K.program_is_turing prog ->
    KTM.run_tm fuel prog st = KTH.run_thiele fuel prog st)
  /\
  (exists (p : K.program),
    KTM.run_tm 1 p KS.initial_state <> KS.target_state /\
    KTH.run_thiele 1 p KS.initial_state = KS.target_state).
Proof.
  split.
  - exact turing_subsumption.
  - exact strict_separation.
Qed.
