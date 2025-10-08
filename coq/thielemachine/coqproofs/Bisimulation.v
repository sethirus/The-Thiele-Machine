(* ================================================================= *)
(* Bisimulation Theorem: legacy placeholder *)
(* ================================================================= *)

(* This file is intentionally minimal.
   The legacy subsumption story is archived in `archive/coq/Subsumption_Legacy.v`
   and relied on a `HALTING_ORACLE` instruction plus the axiom `halting_undecidable`.

   Earlier drafts tried to relate the abstract and concrete machines via a
   bisimulation argument, yet the modelling gaps (oracle vs. no oracle,
   bounded halting predicate, axiomatized receipts) make a faithful
   bisimulation infeasible at present. We keep this placeholder to direct
   readers to the accurate status report instead of giving the impression
   that a second independent proof exists.

   For details, consult:
   - coq/thielemachine/coqproofs/Separation.v (current flagship theorem)
   - coq/README_PROOFS.md (module status and limitations)
   - coq/AXIOM_INVENTORY.md (complete axiom list) *)
