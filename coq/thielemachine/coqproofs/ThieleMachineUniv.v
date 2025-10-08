(* ================================================================= *)
(* Universal Thiele Machine - Module Instantiation *)
(* ================================================================= *)

(* This file attempts to instantiate universal theorems via modules.
   The MAIN WORKING PROOFS now live in Separation.v (sighted vs blind gap).

   This file has module signature matching issues:
   - StepObs must be an inductive/record definition in the module
   - Type compatibility between abstract and concrete signatures

   For the flagship separation theorem, see:
   - coq/thielemachine/coqproofs/Separation.v (current main result)
   - coq/thielemachine/coqproofs/ThieleMachineConcrete.v (concrete implementation)
   - docs/FIXED_FILES_SUMMARY.md (compilation status) *)
