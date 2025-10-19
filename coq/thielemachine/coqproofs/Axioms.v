(* SPDX-License-Identifier: Apache-2.0 *)
(* Declares the axioms relied upon by the Thiele Machine Coq development. *)

Axiom decode_encode_id : Prop.
Axiom utm_catalogue_static_check : Prop.
Axiom utm_head_lt_shift_len : Prop.
Axiom utm_simulation_steps : Prop.
Axiom check_step_sound : Prop.
Axiom check_step_complete : Prop.
Axiom mu_lower_bound : Prop.
Axiom pc_29_implies_registers_from_rule_table : Prop.
Axiom find_rule_from_memory_components : Prop.
