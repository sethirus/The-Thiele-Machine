From KernelTOE Require Import Closure.
From KernelTOE Require Import NoGo.

(** * KernelTOE: single final outcome theorem

    Published shape:
    - KernelMaximalClosure: what the kernel forces.
    - KernelNoGoForTOE: what the kernel cannot force without extra structure.
*)

Theorem KernelTOE_FinalOutcome :
  KernelMaximalClosureP /\ KernelNoGoForTOE_P.
Proof.
  split.
  - exact KernelMaximalClosure.
  - exact KernelNoGoForTOE.
Qed.
