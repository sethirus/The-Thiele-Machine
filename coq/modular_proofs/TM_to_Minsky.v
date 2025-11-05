(* Skeleton of a TM -> Minsky compiler and roadmap for correctness
   proofs.  This file intentionally contains only a compact, documented
   scaffold: a complete, general compiler is left for incremental
   development because the full correctness proof requires a modest
   amount of encoding infrastructure (register allocation for the tape,
   program layout, etc.).  The recommended development path is:

   1.  Formalize the register-encoding of a TM configuration (head,
       state, tape) into a small list of Minsky registers.
   2.  Implement a code-generator that produces a Minsky program that
       emulates the TM's rule table using the encoded registers.
   3.  Prove a one-step simulation lemma relating [tm_step] to a
       bounded number of [run_n] steps of the generated program.

   For now this module provides a placeholder [compile_tm_to_minsky]
   and a brief example showing how a trivial TM could be handled. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Open Scope nat_scope.

From ThieleUniversal Require Import TM.
From ThieleMachine.Modular_Proofs Require Import Minsky.

Module TM_to_Minsky.

(* Placeholder compiler: returns the empty program.  Replace this with a
   real code generator once an encoding from TM configurations to
   register files has been fixed. *)
Definition compile_tm_to_minsky (tm : TM) : Minsky.program := []%list.

(* ------------------------------------------------------------------ *)
(* Example / roadmap notes                                              *)
(* ------------------------------------------------------------------ *)
(* Example idea (informal): encode the TM tape in two large-register
   integers (left, right) using a positional encoding and keep the
   current head position implicitly by which digits are in which
   register.  Each TM rule becomes a short Minsky sequence that:
     - tests the encoded head-symbol,
     - writes the new symbol (arithmetic on the encoded registers),
     - increments/decrements the encoded head position, and
     - updates the state register.

   The correctness lemma will have the shape:

     forall tm conf,
       let p := compile_tm_to_minsky tm in
       encode_conf conf = mconf ->
       decode_conf (run_n p mconf K) = tm_step tm conf

   for some fixed K depending on the code-generation scheme.
*)

End TM_to_Minsky.
