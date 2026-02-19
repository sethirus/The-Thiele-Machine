(** Golden test vectors for canonical hash validation.

    This file defines reference states and computes their canonical encodings
    and hashes. Python tests verify exact alignment by comparing against
    these Coq-computed values.
    
    To extract golden vectors:
      make -C coq thielemachine/coqproofs/GoldenVectors.vo
      coqc -Q coq/thielemachine thielemachine coq/thielemachine/coqproofs/GoldenVectors.v 2>&1 | grep "Golden"
*)

From Coq Require Import List ZArith.
Require Import ThieleMachine.CoreSemantics.
Require Import ThieleMachine.Hash256.
Import ListNotations.
Open Scope Z_scope.

(** =========================================================================
    GOLDEN VECTOR 1: Empty State
    ========================================================================= *)

Definition golden1_state : State := {|
  partition := {| modules := []; next_module_id := 0%nat |};
  mu_ledger := {| mu_operational := 0; mu_information := 0; mu_total := 0; mu_tensor := repeat 0 16 |};
  pc := 0%nat;
  halted := false;
  result := None;
  program := []
|}.

Definition golden1_encoding : list Z := encode_state golden1_state.

Definition golden1_hash : list bool := hash_state golden1_state.

(* Helper: convert list bool to hex-like nat for display *)
Fixpoint bool_list_to_nat (bs : list bool) : nat :=
  match bs with
  | [] => 0%nat
  | b :: bs' => (if b then 1%nat else 0%nat) + 2 * bool_list_to_nat bs'
  end.

(** Compute encoding and hash *)
(* Uncomment to see output: *)
(* Compute golden1_encoding. *)
(* Compute Hash256.fold_mix golden1_encoding 0. *)

(** =========================================================================
    GOLDEN VECTOR 2: State with One Module
    ========================================================================= *)

Definition golden2_state : State := {|
  partition := {|
    modules := [(0%nat, [1%nat; 2%nat; 3%nat])];
    next_module_id := 1%nat
  |};
  mu_ledger := {| mu_operational := 8; mu_information := 0; mu_total := 8; mu_tensor := repeat 0 16 |};
  pc := 1%nat;
  halted := false;
  result := None;
  program := [PNEW [1%nat; 2%nat; 3%nat]]
|}.

Definition golden2_encoding : list Z := encode_state golden2_state.

Definition golden2_hash : list bool := hash_state golden2_state.

(* Uncomment to see output: *)
(* Compute golden2_encoding. *)
(* Compute Hash256.fold_mix golden2_encoding 0. *)

(** =========================================================================
    GOLDEN VECTOR 3: State with Result
    ========================================================================= *)

Definition golden3_state : State := {|
  partition := {| modules := []; next_module_id := 0%nat |};
  mu_ledger := {| mu_operational := 1; mu_information := 0; mu_total := 1; mu_tensor := repeat 0 16 |};
  pc := 1%nat;
  halted := true;
  result := Some 42%nat;
  program := [EMIT 42%nat]
|}.

Definition golden3_encoding : list Z := encode_state golden3_state.

Definition golden3_hash : list bool := hash_state golden3_state.

(* Uncomment to see output: *)
(* Compute golden3_encoding. *)
(* Compute Hash256.fold_mix golden3_encoding 0. *)

(** =========================================================================
    GOLDEN VECTOR 4: Complex Partition
    ========================================================================= *)

Definition golden4_state : State := {|
  partition := {|
    modules := [
      (0%nat, [1%nat; 2%nat]);
      (1%nat, [3%nat; 4%nat; 5%nat]);
      (2%nat, [6%nat])
    ];
    next_module_id := 3%nat
  |};
  mu_ledger := {| mu_operational := 24; mu_information := 0; mu_total := 24; mu_tensor := repeat 0 16 |};
  pc := 3%nat;
  halted := false;
  result := None;
  program := [
    PNEW [1%nat; 2%nat];
    PNEW [3%nat; 4%nat; 5%nat];
    PNEW [6%nat]
  ]
|}.

Definition golden4_encoding : list Z := encode_state golden4_state.

Definition golden4_hash : list bool := hash_state golden4_state.

(* Uncomment to see output: *)
(* Compute golden4_encoding. *)
(* Compute Hash256.fold_mix golden4_encoding 0. *)

(** =========================================================================
    EXTRACTION INSTRUCTIONS
    ========================================================================= *)

(**
   To extract golden vectors for Python tests:
   
   1. Compile this file:
      make -C coq thielemachine/coqproofs/GoldenVectors.vo
   
   2. Extract encoded values:
      coqc -Q coq/thielemachine thielemachine coq/thielemachine/coqproofs/GoldenVectors.v
      
   3. Look for "Compute golden*_encoding" output and copy to Python
   
   4. Compute hash as integer:
      Hash256.fold_mix encoding 0
   
   5. Convert to hex in Python:
      hex(coq_hash_int)[2:].zfill(64)
   
   Example:
     Coq: Compute Hash256.fold_mix golden1_encoding 0.
     Output: 1234567890
     Python: hex(1234567890)[2:].zfill(64)
*)
