(**
  MinimalExtraction.v
  
  MINIMAL extraction for debugging stack overflow issue.
  Extract ONLY what build/extracted_vm_runner.ml actually uses.
*)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

(* SAFE: Standard Coq library nat arithmetic — OCaml (+) is equivalent for non-negative int *)
Extract Constant Nat.add => "(+)".
(* SAFE: Standard Coq library nat multiplication — OCaml ( * ) is equivalent for non-negative int *)
Extract Constant Nat.mul => "( * )".
(* SAFE: Standard Coq library nat subtraction — clamped to 0 matches Nat.sub semantics *)
Extract Constant Nat.sub => "fun n m -> max 0 (n-m)".
(* SAFE: Standard Coq library nat equality — OCaml structural (=) matches Nat.eqb on int *)
Extract Constant Nat.eqb => "(=)".

(* SAFE: 32-bit mask — truncation to 32 bits is the defining operation of word32 *)
Extract Constant VMState.word32 =>
  "(fun x -> x land 0xFFFFFFFF)".

(* SAFE: bitwise XOR + 32-bit mask — standard bit operation, trivially correct *)
Extract Constant VMState.word32_xor =>
  "(fun a b -> (a lxor b) land 0xFFFFFFFF)".

(* SAFE: popcount via Kernighan bit-clear loop — well-known correct algorithm *)
Extract Constant VMState.word32_popcount =>
  "(fun x -> let v = x land 0xFFFFFFFF in let rec pc v acc = if v = 0 then acc else pc (v land (v - 1)) (acc + 1) in pc v 0)".

Extraction "../build/thiele_core_minimal.ml"
  VMStep.vm_instruction
  VMState.VMState
  SimulationProof.vm_apply.
