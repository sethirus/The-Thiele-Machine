(**
  Extraction.v

  Foundry entrypoint: extract the executable kernel VM semantics from Coq to OCaml.

  This file is intentionally small and purely declarative.
  It is invoked by `./scripts/forge_artifact.sh`.
*)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import Strings.String.

(* Kernel VM semantics *)
Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.

Extraction Language OCaml.

(* Keep the extracted surface stable and readable. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

(* Map Coq nat to OCaml int for a compact executable IR. *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(*
  Performance-critical word32 helpers:
  The kernel VM uses nat-as-int for scratch registers and memory.
  The Coq definitions go through N (binary naturals) which, under the current
  nat extraction, can trigger deep recursion for large ints.

  We extract these helpers directly to OCaml bit operations to keep execution
  real and safe for full 32-bit values.
*)
Extract Constant VMState.word32 =>
  "(fun x -> x land 0xFFFFFFFF)".

Extract Constant VMState.word32_xor =>
  "(fun a b -> (a lxor b) land 0xFFFFFFFF)".

Extract Constant VMState.word32_popcount =>
  "(fun x -> let v = x land 0xFFFFFFFF in let rec pc v acc = if v = 0 then acc else pc (v land (v - 1)) (acc + 1) in pc v 0)".

(**
  Main extraction target.

  NOTE:
  - `vm_apply` is the executable single-step kernel semantics.
  - `run_vm` is a fuel-bounded trace interpreter.

  The Foundry pipeline treats the generated OCaml as the canonical IR.
*)
Extraction "../build/thiele_core.ml"
  (* Core types *)
  VMStep.vm_instruction
  VMStep.lassert_certificate
  VMState.VMState
  VMState.PartitionGraph
  VMState.CSRState
  VMState.ModuleID
  VMState.VMAxiom

  (* Helpers used by the step semantics *)
  VMStep.instruction_cost
  VMStep.apply_cost
  VMStep.advance_state
  VMStep.latch_err
  VMState.ascii_checksum
  VMState.graph_pnew
  VMState.graph_psplit
  VMState.graph_pmerge
  VMState.graph_add_axiom
  VMState.graph_record_discovery
  VMState.csr_set_err
  VMState.csr_set_status
  VMState.csr_set_cert_addr

  (* Executable semantics *)
  SimulationProof.vm_apply
  SimulationProof.run_vm.
