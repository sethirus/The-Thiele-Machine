(* ================================================================= *)
(* ThieleUniversalBridge Module: BridgeHeader *)
(* Extracted from lines 1-50 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

(* Dependencies noted for reference: Invariants *)
(* These are NOT imported to keep modules standalone for analysis *)

(* ================================================================= *)
(* Bridge module providing concrete implementations from archive    *)
(* This module extracts working definitions from the archive to     *)
(* avoid circular dependencies and compilation errors.              *)
(*                                                                   *)
(* STATUS: Partially complete                                        *)
(*   - Core definitions (run1, run_n, setup_state): CONCRETE ✓     *)
(*   - Basic lemmas (setup_state_regs_length, inv_min): PROVED ✓   *)
(*   - Helper lemmas (nth_add_skipn, nth_firstn_lt): PROVED ✓      *)
(*   - Transition lemmas: ADMITTED (require symbolic execution)     *)
(*                                                                   *)
(* NOTE: Relocated under thielemachine/verification to quarantine   *)
(* the instruction-level replay from the default `make core` flow.  *)
(* Use `make -C coq bridge` (or `verification`) to exercise this    *)
(* artifact without blocking the audited tier.                      *)
(*                                                                   *)
(* To complete: The transition lemmas require detailed symbolic     *)
(* execution proofs through the CPU interpreter. These are complex  *)
(* but mechanizable - they involve stepping through the instruction *)
(* sequence and maintaining invariants.                             *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.

Local Open Scope nat_scope.
Local Notation length := List.length.

(* Instrumentation helpers to locate long-running proofs during timed bridge
   builds.  The [Time] vernac modifier is applied to the key loop lemmas, and
   [bridge_checkpoint] marks entry into their proofs so a timed build can
   report the last completed milestone before hitting a timeout. *)
Ltac bridge_checkpoint msg :=
  let s := eval compute in msg in idtac "[bridge]" s.

(* ----------------------------------------------------------------- *)
(* Program encoding                                                  *)
(* ----------------------------------------------------------------- *)

(* The encoded universal program *)
Definition program : list nat :=
  flat_map UTM_Encode.encode_instr_words UTM_Program.program_instrs.

(* Compute the concrete program length once so decoding bounds can reuse it
   without re-running a large reduction. *)
Definition program_len : nat := Eval vm_compute in List.length program.

Lemma program_length_eq : List.length program = program_len.
Proof. reflexivity. Qed.
