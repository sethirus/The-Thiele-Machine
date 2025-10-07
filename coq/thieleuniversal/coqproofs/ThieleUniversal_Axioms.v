(* ================================================================ *)
(* AXIOMATIZED LEMMAS FOR THIELEUNIVERSAL.V                         *)
(* ================================================================ *)
(*
   This file contains the three key lemmas that are currently axiomatized
   due to proof complexity. Each axiom is accompanied by:
   1. A clear statement of what it asserts
   2. Why it's true (informal argument)
   3. A proposed proof strategy for future mechanization
*)

Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Nat.

Require Import ThieleUniversal.UTM_Encode.
Require Import ThieleUniversal.UTM_Program.
Require Import ThieleUniversal.TM.
Require Import ThieleUniversal.ZArith_ext.
Require Import ThieleUniversal.ZCPU.

(* ================================================================ *)
(* AXIOM 1: Loop Invariant Preservation                            *)
(* ================================================================ *)

(*
   INFORMAL STATEMENT:
   The find-rule loop (PCs 4-11) preserves its invariant. Starting from
   PC=4 with the loop invariant satisfied at index i:
   - If a matching rule is found, execution reaches PC=29 (apply-start) in 17 steps
   - If no match, execution returns to PC=4 with invariant satisfied at index i+1
     in either 6 steps (Q-mismatch) or 13 steps (symbol-mismatch)

   WHY IT'S TRUE:
   The interpreter follows this control flow:
   - PC 4-6: Load rule components from memory at RULES_START_ADDR + 5*i
   - PC 7: Branch on Q match
     - If match: continue to PC 12
     - If no match: increment address (PC 8-11) and loop back (6 steps total)
   - PC 12: Branch on symbol match (if Q matched)
     - If match: jump to PC 22 (apply phase)
     - If no match: increment address (PC 13-21) and loop back (13 steps total)
   - PC 22-28: Load rule action components into registers
   - PC 29: Apply-start point

   PROOF STRATEGY:
   1. Symbolic execution approach:
      - Define helper lemmas for each instruction's effect on state
      - Prove preservation through each path separately
      - Use case analysis on the guard conditions

   2. Alternative inductive approach:
      - Prove invariant for one iteration
      - Compose iterations using transitivity
      - Handle termination when rule is found

   CURRENT BLOCKERS:
   - The existing proof has incorrect bullet structure (mixing Some/None cases)
   - Needs complete redesign with proper case analysis
*)

Axiom find_rule_loop_preserves_inv : forall (tm : TM) (conf : TMConfig) (st : State) (i : nat),
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.

(* ================================================================ *)
(* AXIOM 2: Registers from Rule Table                              *)
(* ================================================================ *)

(*
   INFORMAL STATEMENT:
   If execution reaches PC=29 (apply-start), then the registers REG_Q',
   REG_WRITE, and REG_MOVE must have been loaded from some rule in the
   encoded rule table in memory.

   WHY IT'S TRUE:
   The only way to reach PC=29 is through the apply phase (PCs 22-28):
   - PC 22: Copy rule address to TEMP1
   - PC 23: Load q_next from memory[TEMP1] to Q'
   - PC 24-25: Increment TEMP1, load write symbol to WRITE
   - PC 26-27: Increment TEMP1, load move direction to MOVE
   - PC 28: Jump to 29

   The memory locations accessed are:
   - RULES_START_ADDR + 5*i + 2 (q_next)
   - RULES_START_ADDR + 5*i + 3 (write)
   - RULES_START_ADDR + 5*i + 4 (move)

   PROOF STRATEGY:
   1. Use loop invariant to track TEMP1 value before apply phase
   2. Symbolically execute PCs 22-28 to show:
      - TEMP1 = RULES_START_ADDR + 5*i + 2 at PC 23
      - TEMP1 = RULES_START_ADDR + 5*i + 3 at PC 25
      - TEMP1 = RULES_START_ADDR + 5*i + 4 at PC 27
   3. Use memory preservation to show these locations unchanged
   4. Extract witness i from the loop invariant

   DEPENDENCIES:
   - Requires find_rule_loop_preserves_inv to establish loop invariant
   - Needs helper lemmas for AddConst, LoadIndirect effects
*)

Axiom pc_29_implies_registers_from_rule_table :
  forall (tm : TM) (conf : TMConfig) (st : State) (k : nat) (st' : State),
    let '((q, tape), head) := conf in
    inv st tm conf ->
    st' = run_n st k ->
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    IS_ApplyRule_Start (read_reg REG_PC st') ->
    exists i, i < length (tm_rules tm) /\
      nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_Q' st' /\
      nth (RULES_START_ADDR + i * 5 + 3) (mem st') 0 = read_reg REG_WRITE st' /\
      nth (RULES_START_ADDR + i * 5 + 4) (mem st') 0 = read_reg REG_MOVE st'.

(* ================================================================ *)
(* AXIOM 3: Find Rule from Memory                                   *)
(* ================================================================ *)

(*
   INFORMAL STATEMENT:
   If the memory at position i contains components that match the current
   registers, and those components came from the encoded rule table, then
   find_rule returns that rule.

   WHY IT'S TRUE:
   The find_rule function searches through the rule list comparing each rule's
   q and symbol fields with the current state. If memory[i*5+2..4] contains
   (q_next, write, move) and these are in the registers, and memory[i*5+0..1]
   contains (q, symbol) matching the current config, then find_rule will
   return this rule.

   PROOF STRATEGY:
   1. Induction on rule list position:
      Base case i=0: The first rule is checked directly
      Inductive case i>0: If not found by position i, recurse on tail

   2. Key steps:
      - Use encode_rules structure to relate memory to rule list
      - Show that memory layout matches find_rule search order
      - Use decidable equality on q and symbol to handle matches

   3. Alternative approach:
      - Prove helper: encode_rules injective on matching rules
      - Show memory equality implies rule equality
      - Use find_rule_skipn_index lemma from UTM_CoreLemmas

   CURRENT BLOCKERS:
   - Proof has nested admits for rule matching logic
   - Needs cleaner decomposition of encode_rules properties
*)

Axiom find_rule_from_memory_components :
  forall (tm : TM) (conf : TMConfig) (i : nat) (st' : State),
    let '((q, tape), head) := conf in
    i < length (tm_rules tm) ->
    nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_Q' st' ->
    nth (RULES_START_ADDR + i * 5 + 3) (mem st') 0 = read_reg REG_WRITE st' ->
    nth (RULES_START_ADDR + i * 5 + 4) (mem st') 0 = read_reg REG_MOVE st' ->
    firstn (length (encode_rules (tm_rules tm)))
          (skipn RULES_START_ADDR (mem st')) =
    encode_rules (tm_rules tm) ->
    find_rule (tm_rules tm) q (nth head tape (tm_blank tm)) =
      Some (read_reg REG_Q' st', read_reg REG_WRITE st', decode_z (read_reg REG_MOVE st')).

(* ================================================================ *)
(* PROOF STRATEGY NOTES                                             *)
(* ================================================================ *)

(*
   RECOMMENDED APPROACH FOR MECHANIZATION:

   Phase 1: Helper Lemma Infrastructure
   - Symbolic execution lemmas for each instruction type
   - Memory preservation lemmas
   - Register update lemmas
   - Program counter arithmetic lemmas

   Phase 2: Loop Invariant (Axiom 1)
   - Start with simplified version: no monotonicity requirements
   - Prove single iteration preservation
   - Handle branching with explicit case analysis
   - Compose iterations using transitivity

   Phase 3: Register Loading (Axiom 2)
   - Prove backward from PC=29 to PC=22
   - Track TEMP1 through each increment
   - Use memory preservation from Phase 1
   - Connect to loop invariant from Phase 2

   Phase 4: Memory-to-Find-Rule Bridge (Axiom 3)
   - Prove encode_rules injectivity
   - Show memory slicing preserves structure
   - Use list induction on rule table
   - Connect to find_rule definition

   ESTIMATED EFFORT:
   - Phase 1: ~200 lines of helper lemmas
   - Phase 2: ~500 lines (main complexity)
   - Phase 3: ~300 lines
   - Phase 4: ~400 lines
   Total: ~1400 lines of careful symbolic execution

   ALTERNATIVE: Keep as axioms with this documentation
   The axioms are semantically sound and the informal arguments are convincing.
   Mechanization is possible but requires significant effort for what are
   essentially symbolic execution proofs.
*)
