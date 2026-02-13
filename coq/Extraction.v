(**
  Extraction.v

  Foundry entrypoint: extract the full verified kernel from Coq to OCaml.

  This file extracts all executable (computable) definitions from the kernel,
  organized by subsystem:
    1. Core VM semantics (VMState, VMStep, SimulationProof)
    2. Receipt integrity validation (ReceiptIntegrity)
    3. CHSH measurement extraction and statistics (CHSHExtraction, CHSH)
    4. Semantic μ-cost computation (SemanticMuCost)
    5. Operational μ-cost model (MuCostModel)
    6. μ-Ledger conservation accounting (MuLedgerConservation)
    7. Falsifiable prediction checking (FalsifiablePrediction)
    8. Three-layer isomorphism wire specs (ThreeLayerIsomorphism)
    9. Hardware/Python bisimulation step functions (HardwareBisimulation)
   10. Tsirelson bound computation (TsirelsonComputation)

  The Foundry pipeline treats the generated OCaml as the canonical IR.
  Invoked by `./scripts/forge_artifact.sh`.
*)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.
From Coq Require Import Strings.String.

(* ---------- Core VM semantics ---------- *)
From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.

(* ---------- Receipt integrity ---------- *)
From Kernel Require Import ReceiptIntegrity.

(* ---------- CHSH measurement pipeline ---------- *)
From Kernel Require Import CHSHExtraction.
From Kernel Require Import CHSH.

(* ---------- Semantic μ-cost ---------- *)
From Kernel Require Import SemanticMuCost.

(* ---------- Operational μ-cost model ---------- *)
From Kernel Require Import MuCostModel.

(* ---------- μ-Ledger conservation ---------- *)
From Kernel Require Import MuLedgerConservation.

(* ---------- Falsifiable predictions ---------- *)
From Kernel Require Import FalsifiablePrediction.

(* ---------- Three-layer isomorphism ---------- *)
From Kernel Require Import ThreeLayerIsomorphism.

(* ---------- Bisimulation step functions ---------- *)
From Kernel Require Import HardwareBisimulation.

(* ---------- Tsirelson computation ---------- *)
From Kernel Require Import TsirelsonComputation.

Extraction Language OCaml.

(* ================================================================ *)
(*  Type mappings: keep the extracted surface stable and readable.   *)
(* ================================================================ *)

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

(* Map Coq nat to OCaml int for a compact executable IR. *)
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(* Efficient native-int implementations for nat arithmetic.
   Without these, Nat.pow 2 31 (used in ReceiptIntegrity.mu_max)
   triggers Peano-recursive mul/add chains that stack overflow. *)
Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant Nat.sub => "fun n m -> Stdlib.max 0 (n-m)".
Extract Constant Nat.pred => "fun n -> Stdlib.max 0 (n-1)".
Extract Constant Nat.pow =>
  "fun b e -> let rec go acc e = if e <= 0 then acc else go (acc * b) (e-1) in go 1 e".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.divmod =>
  "fun x y q u -> let d = y + 1 in (q + x / d, d - 1 - x mod d)".
Extract Constant Nat.modulo =>
  "fun x y -> if y = 0 then x else x mod y".
Extract Constant Nat.div =>
  "fun x y -> if y = 0 then 0 else x / y".

(* ================================================================ *)
(*  Performance-critical word32 helpers.                             *)
(*  The kernel VM uses nat-as-int for scratch registers and memory.  *)
(*  The Coq definitions go through N (binary naturals) which, under  *)
(*  the current nat extraction, can trigger deep recursion for large  *)
(*  ints.  We extract these directly to OCaml bit operations.        *)
(* ================================================================ *)

Extract Constant VMState.word32 =>
  "(fun x -> x land 0xFFFFFFFF)".

Extract Constant VMState.word32_xor =>
  "(fun a b -> (a lxor b) land 0xFFFFFFFF)".

Extract Constant VMState.word32_popcount =>
  "(fun x -> let v = x land 0xFFFFFFFF in let rec pc v acc = if v = 0 then acc else pc (v land (v - 1)) (acc + 1) in pc v 0)".

(* ================================================================ *)
(*  Main extraction target.                                          *)
(*                                                                   *)
(*  Every symbol listed below is extracted to ../build/thiele_core.ml *)
(*  and its .mli interface.  The list is organized by subsystem so   *)
(*  that additions are easy to audit.                                *)
(* ================================================================ *)

Extraction "../build/thiele_core.ml"

  (* ---- 1. Core types ---- *)
  VMStep.vm_instruction
  VMStep.lassert_certificate
  VMState.VMState
  VMState.PartitionGraph
  VMState.CSRState
  VMState.ModuleID
  VMState.VMAxiom

  (* ---- 2. Core helpers (step semantics) ---- *)
  VMStep.instruction_cost
  VMStep.apply_cost
  VMStep.advance_state
  VMStep.advance_state_rm
  VMStep.latch_err
  VMStep.is_bit
  VMStep.chsh_bits_ok
  VMState.ascii_checksum
  VMState.graph_pnew
  VMState.graph_psplit
  VMState.graph_pmerge
  VMState.graph_lookup
  VMState.graph_remove
  VMState.graph_update
  VMState.graph_add_axiom
  VMState.graph_add_axioms
  VMState.graph_record_discovery
  VMState.graph_find_region
  VMState.graph_add_module
  VMState.csr_set_err
  VMState.csr_set_status
  VMState.csr_set_cert_addr
  VMState.normalize_region
  VMState.nat_list_eq
  VMState.nat_list_subset
  VMState.nat_list_disjoint
  VMState.nat_list_union
  VMState.partition_valid
  VMState.read_reg
  VMState.write_reg
  VMState.read_mem
  VMState.swap_regs
  VMState.word32
  VMState.word32_xor
  VMState.word32_popcount
  VMState.reg_index
  VMState.mem_index
  VMState.REG_COUNT
  VMState.MEM_SIZE

  (* ---- 3. Executable semantics (single-step + trace runner) ---- *)
  SimulationProof.vm_apply
  SimulationProof.run_vm

  (* ---- 4. Receipt integrity validation ---- *)
  ReceiptIntegrity.Receipt
  ReceiptIntegrity.mu_max
  ReceiptIntegrity.mu_in_range_b
  ReceiptIntegrity.instruction_mu_delta
  ReceiptIntegrity.receipt_mu_consistent_b
  ReceiptIntegrity.receipt_mu_in_range_b
  ReceiptIntegrity.receipt_fully_valid_b
  ReceiptIntegrity.chain_links_b
  ReceiptIntegrity.chain_all_consistent_b
  ReceiptIntegrity.chain_all_in_range_b
  ReceiptIntegrity.chain_all_valid_b
  ReceiptIntegrity.receipt_chain_valid_b
  ReceiptIntegrity.chain_total_cost
  ReceiptIntegrity.chain_final_mu

  (* ---- 5. CHSH extraction pipeline ---- *)
  CHSHExtraction.CHSHTrial
  CHSHExtraction.extract_chsh_trials_from_trace
  CHSHExtraction.filter_trials
  CHSHExtraction.compute_correlation
  CHSHExtraction.chsh_from_trials
  CHSHExtraction.chsh_from_vm_trace

  (* ---- 6. CHSH from receipts (original trial-based) ---- *)
  KernelCHSH.Trial
  KernelCHSH.LocalStrategy
  KernelCHSH.is_trial_instr
  KernelCHSH.trials_of_receipts
  KernelCHSH.sign_z
  KernelCHSH.trial_value_z
  KernelCHSH.count_setting
  KernelCHSH.sum_setting_z
  KernelCHSH.expectation
  KernelCHSH.chsh
  KernelCHSH.trial_of_local
  KernelCHSH.trials_of_local
  KernelCHSH.chsh_local_z

  (* ---- 7. Semantic μ-cost computation ---- *)
  SemanticMuCost.ConstraintVar
  SemanticMuCost.ArithExpr
  SemanticMuCost.CompOp
  SemanticMuCost.AtomicConstraint
  SemanticMuCost.Constraint
  SemanticMuCost.normalize_comp_op
  SemanticMuCost.should_flip_comparison
  SemanticMuCost.normalize_atomic
  SemanticMuCost.flatten_and
  SemanticMuCost.flatten_or
  SemanticMuCost.rebuild_and
  SemanticMuCost.rebuild_or
  SemanticMuCost.count_vars_arith
  SemanticMuCost.count_vars
  SemanticMuCost.count_atoms
  SemanticMuCost.count_operators
  SemanticMuCost.log2_nat
  SemanticMuCost.semantic_complexity_bits
  SemanticMuCost.axiom_semantic_cost
  SemanticMuCost.axiom_cost_with_fallback

  (* ---- 8. Operational μ-cost model ---- *)
  MuCostModel.module_count
  MuCostModel.partition_complexity
  MuCostModel.mu_cost_of_instr
  MuCostModel.mu_cost_of_trace

  (* ---- 9. μ-Ledger conservation accounting ---- *)
  MuLedgerConservation.ledger_entries
  MuLedgerConservation.bounded_run
  MuLedgerConservation.ledger_sum
  MuLedgerConservation.irreversible_bits
  MuLedgerConservation.irreversible_count
  MuLedgerConservation.ledger_component_sum

  (* ---- 10. Falsifiable prediction checking ---- *)
  FalsifiablePrediction.ExperimentalTrial
  FalsifiablePrediction.trace_mu_cost
  FalsifiablePrediction.region_size
  FalsifiablePrediction.evidence_size
  FalsifiablePrediction.pnew_cost_bound
  FalsifiablePrediction.psplit_cost_bound
  FalsifiablePrediction.pmerge_cost_bound
  FalsifiablePrediction.discover_cost_bound
  FalsifiablePrediction.check_prediction

  (* ---- 11. Three-layer isomorphism wire specs ---- *)
  ThreeLayerIsomorphism.project_vmstate
  ThreeLayerIsomorphism.trace_cost
  ThreeLayerIsomorphism.run_wire
  ThreeLayerIsomorphism.run_fws

  (* ---- 12. Hardware / Python bisimulation ---- *)
  HardwareBisimulation.HardwareState
  HardwareBisimulation.PythonState
  HardwareBisimulation.hardware_step
  HardwareBisimulation.python_step
  HardwareBisimulation.hardware_multi_step
  HardwareBisimulation.python_multi_step
  HardwareBisimulation.q16_16_one

  (* ---- 13. Tsirelson bound constants ---- *)
  TsirelsonComputation.sqrt2_approx
  TsirelsonComputation.inv_sqrt2
  TsirelsonComputation.tsirelson.
