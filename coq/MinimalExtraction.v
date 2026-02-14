(**
  MinimalExtraction.v
  
  MINIMAL extraction for debugging stack overflow issue.
  Extract ONLY what tools/extracted_vm_runner.ml actually uses.
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

Extraction "../build/thiele_core_minimal.ml"
  VMStep.vm_instruction
  VMState.VMState
  SimulationProof.vm_apply.
