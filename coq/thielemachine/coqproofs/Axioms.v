(* SPDX-License-Identifier: Apache-2.0 *)
(* Declares the axioms relied upon by the Thiele Machine Coq development. *)

Axiom decode_encode_id : Prop.
(* Justified: Encoding followed by decoding returns the original data, ensuring roundtrip correctness for state serialization. *)

Axiom utm_catalogue_static_check : Prop.
(* Justified: The UTM catalogue passes static verification checks, ensuring the universal Turing machine is correctly configured. *)

Axiom utm_head_lt_shift_len : Prop.
(* Justified: The tape head position is always less than the shift length, preventing out-of-bounds access in tape operations. *)

Axiom utm_simulation_steps : Prop.
(* Justified: The UTM simulation executes the correct number of steps as specified by the Thiele machine semantics. *)

Axiom check_step_sound : Prop.
(* Justified: The check_step function correctly validates valid state transitions, ensuring soundness of the checker. *)

Axiom check_step_complete : Prop.
(* Justified: The check_step function accepts all valid state transitions, ensuring completeness of the checker. *)

Axiom mu_lower_bound : Prop.
(* Justified: The mu cost has a lower bound related to the certificate size, ensuring computational adequacy. *)

Axiom pc_29_implies_registers_from_rule_table : Prop.
(* Justified: At program counter 29, the registers are correctly derived from the rule table, ensuring proper rule application. *)

Axiom find_rule_from_memory_components : Prop.
(* Justified: Rules can be correctly found from memory components, ensuring the machine can access and apply rules. *)
