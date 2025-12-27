(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia List Bool.
Import ListNotations.

From Kernel Require Import Kernel KernelTM KernelThiele Subsumption.

Module K := Kernel.
Module KTM := KernelTM.
Module KTH := KernelThiele.
Module KS := Subsumption.

(** This file re-exports the kernel Subsumption results for the
    ThieleMachine module. *)

(* Re-export main theorem from kernel *)
Theorem turing_strictly_contained_in_thiele :
  exists (p : K.program),
    KS.program_is_sighted p /\ ~ K.program_is_turing p.
Proof.
  exact KS.main_subsumption.
Qed.
