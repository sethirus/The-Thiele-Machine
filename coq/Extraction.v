(**
  Extraction.v

  MINIMAL extraction for the VM runner to avoid stack overflow.
  
  The full extraction with all modules (Receipt, CHSH, MuCost, etc.) causes
  OCaml stack overflow during garbage collection due to deeply nested proof
  structures. This minimal extraction includes only the core VM semantics
  needed by tools/extracted_vm_runner.ml

  Note: Other experimental features (receipt validation, CHSH extraction, etc.)  
  are verified in Coq but not extracted to OCaml to avoid the stack overflow issue.
*)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import VMEncoding KernelTM.
From Kernel Require Import MuCostModel MuLedgerConservation MuInitiality NoFreeInsight.
From Kernel Require Import SimulationProof.
From Kernel Require Import Certification QuantumBound.
From Kernel Require Import RevelationRequirement.
From KamiHW Require Import Abstraction ThieleCPUBusTop.

Import VMStep.VMStep.

(* Proof anchor: extraction builds must type-check the NoFreeInsight certification
   boundary theorem used by downstream verification layers. *)
Theorem extraction_nofi_supra_boundary_anchor :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    RevelationProof.trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    QuantumBound.quantum_admissible trace ->
    ~ CertificationTheory.Certified s_final CertificationTheory.supra_quantum_certified trace.
Proof.
  exact CertificationTheory.quantum_admissible_cannot_certify_supra_chsh.
Qed.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.sub => "fun n m -> max 0 (n-m)".
Extract Constant Nat.eqb => "(=)".

Extract Constant VMState.word32 =>
  "(fun x -> x land 0xFFFFFFFF)".

Extract Constant VMState.word32_xor =>
  "(fun a b -> (a lxor b) land 0xFFFFFFFF)".

Extract Constant VMState.word32_popcount =>
  "(fun x -> let v = x land 0xFFFFFFFF in let rec pc v acc = if v = 0 then acc else pc (v land (v - 1)) (acc + 1) in pc v 0)".

(* Ensure OCaml callers of [vm_apply] get NoFI enforcement by default.
   [vm_apply_nofi] uses [vm_apply_unsafe], so this alias does not recurse. *)
Extract Constant SimulationProof.vm_apply => "vm_apply_runtime".

Extraction "../build/thiele_core.ml"
  VMStep.vm_instruction
  VMStep.nofi_step_cost_okb
  VMStep.nofi_trace_cost_okb
  VMState.VMState
  SimulationProof.vm_apply_runtime
  SimulationProof.vm_apply_nofi
  SimulationProof.vm_apply
  Abstraction.KamiSnapshot
  ThieleCPUBusTop.BusReg
  ThieleCPUBusTop.BusCoreView
  ThieleCPUBusTop.BusShadowRegs
  ThieleCPUBusTop.BusWrapperState
  ThieleCPUBusTop.BusOp
  ThieleCPUBusTop.decodeBusReg
  ThieleCPUBusTop.busRegReadable
  ThieleCPUBusTop.busRegWritable
  ThieleCPUBusTop.busRead
  ThieleCPUBusTop.busWrite
  ThieleCPUBusTop.bus_step
  ThieleCPUBusTop.coreViewOfSnapshot.
