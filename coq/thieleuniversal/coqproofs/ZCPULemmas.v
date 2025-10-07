(* ================================================================= *)
(* ZCPU Helper Lemmas *)
(* ================================================================= *)

(* This file has decode_instr signature incompatibilities between
   CPU.v and ThieleUniversal.v:
   - ThieleUniversal.decode_instr : State -> Instr
   - Original usage: decode_instr : nat -> Instr
   
   The main UTM proofs are complete in ThieleUniversal.v without this file.
   
   For the verified Universal TM proofs, see:
   - coq/thieleuniversal/coqproofs/ThieleUniversal.v (3,053 lines, FULLY PROVEN)
   - coq/thieleuniversal/coqproofs/UTM_CoreLemmas.v (helper lemmas)
   - docs/AXIOM_SUMMARY.md (axiom inventory)
   - docs/UTM_DEBUG_WORKING.md (debug notes) *)
