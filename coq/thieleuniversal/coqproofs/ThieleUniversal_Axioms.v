(* ================================================================ *)
(* HISTORICAL NOTES FOR THIELEUNIVERSAL AXIOMS                      *)
(* ================================================================ *)
(*
   The universal interpreter no longer relies on standalone axioms.
   All three lemmas—loop preservation, register recovery, and rule-table
   lookup—are now fully mechanised inside [ThieleUniversal.v].  This
   file remains as a historical record for auditors who wish to review
   the original informal proof sketches.

   For the current formal statements, see:
     - [ThieleUniversal.v] Lemma find_rule_loop_preserves_inv
     - [ThieleUniversal.v] Lemma pc_29_implies_registers_from_rule_table
     - [ThieleUniversal.v] Lemma find_rule_from_memory_components
*)
