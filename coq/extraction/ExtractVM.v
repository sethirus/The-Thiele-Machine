(**
   ExtractVM.v
   
   Extraction of VM kernel semantics to OCaml.
   This provides the canonical extracted implementation that serves
   as the source of truth for Verilog and Python generation.
   
   Author: Generated from Thiele Machine kernel
   Date: 2025-12-11
*)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.

(* Import the kernel modules *)
Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import VMEncoding.
Require Import MuLedgerConservation.

(** Configure extraction *)
Extraction Language OCaml.

(** Extract standard library types *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(** Extract strings as OCaml strings *)
Extract Inductive string => "string" [ """""" "String.make 1" ].

(** 
   Main extraction
   
   This extracts:
   - All 16 VM instructions (vm_instruction type)
   - Operational semantics (vm_step)
   - μ-cost functions (instruction_cost, apply_cost)
   - State management (advance_state)
   - Simulation functions (vm_apply)
   - Encoding functions (compile_vm_operation)
*)

Extraction "vm_extracted.ml"
  (* Core types *)
  vm_instruction
  VMState
  PartitionGraph
  CSRState
  ModuleID
  VMAxiom
  lassert_certificate
  
  (* Cost functions *)
  instruction_cost
  apply_cost
  
  (* State management *)
  advance_state
  latch_err
  
  (* Step semantics - all 16 instructions *)
  vm_step
  
  (* Simulation *)
  vm_apply
  
  (* Encoding *)
  compile_vm_operation
  
  (* Conservation *)
  extract_ledger.

(**
   Post-extraction verification:
   
   The generated vm_extracted.ml file should contain:
   1. Type vm_instruction with 16 constructors
   2. Function instruction_cost matching all 16 cases
   3. Function vm_step with 20+ step rules
   4. All support functions
   
   This serves as the canonical implementation that:
   - Verilog opcode definitions are generated from
   - Python instruction types are generated from
   - Ensures perfect three-layer consistency
*)
