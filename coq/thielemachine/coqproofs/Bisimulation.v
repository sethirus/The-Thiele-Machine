(* ================================================================= *)
(* Bisimulation Theorem: Thiele Machine Subsumes Turing Machine *)
(* ================================================================= *)

(* This file is intentionally minimal.
   The MAIN SUBSUMPTION RESULT is fully proven in Subsumption.v:
   - Theorem: thiele_solves_halting (PROVEN)
   - Theorem: thiele_strictly_extends_turing (PROVEN)
   
   This file originally attempted an alternative bisimulation-based proof,
   but type incompatibilities between different TM/Thiele representations
   make it impractical. The core results remain fully mechanized in Subsumption.v.
   
   For the formal verification of subsumption, see:
   - coq/thielemachine/coqproofs/Subsumption.v (main theorems, PROVEN)
   - docs/AXIOM_SUMMARY.md (axiom inventory)
   - docs/FIXED_FILES_SUMMARY.md (compilation status) *)
