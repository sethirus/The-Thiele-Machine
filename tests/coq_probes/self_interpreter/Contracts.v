(* B3 self-interpreter contract probe: full statements, definitions of the
   observations and relations, and global assumptions of every result. *)
From Kernel Require Import VMSelfGuest VMSelfProgram VMSelfCorrect VMSelfRun.
From Kernel Require Import VMSelfUniversal VMSelfLimitative.

Print GInstr. Print g_denote. Print g_program. Print g_word_N. Print g_wf.
Print g_state. Print g_st. Print g_next.
Print g_code_N. Print g_width. Print g_fetch.
Print U_END. Print hst. Print hb. Print h_rep. Print h_done. Print h_steps. Print h_tail. Print h_prefix.
Print g_step. Print g_run. Print g_terminal. Print gc_state. Print hbc.
Print cm2_block. Print cm2_compile. Print crel. Print ccnt.
Print self_input. Print self_host_halts. Print self_mm2_input.

Check g_step_is_vm_apply_u. Print Assumptions g_step_is_vm_apply_u.
Check g_code_fetch. Print Assumptions g_code_fetch.
Check g_code_fetch_outside. Print Assumptions g_code_fetch_outside.
Check g_width_fits. Print Assumptions g_width_fits.
Check U_length. Print Assumptions U_length.
Check h_step. Print Assumptions h_step.
Check h_steps_pos. Print Assumptions h_steps_pos.
Check g_run_is_run_vm_u. Print Assumptions g_run_is_run_vm_u.
Check h_block. Print Assumptions h_block.
Check h_simulation. Print Assumptions h_simulation.
Check self_interpreter_complete. Print Assumptions self_interpreter_complete.
Check self_interpreter_sound. Print Assumptions self_interpreter_sound.
Check self_interpreter_correct. Print Assumptions self_interpreter_correct.
Check self_interpreter_divergence. Print Assumptions self_interpreter_divergence.
Check U_pc_bound. Print Assumptions U_pc_bound.
Check self_interpreter_divergence_live. Print Assumptions self_interpreter_divergence_live.
Check self_interpreter_malformed. Print Assumptions self_interpreter_malformed.
Check cm2_compile_wf. Print Assumptions cm2_compile_wf.
Check cm2_step_sim. Print Assumptions cm2_step_sim.
Check cm2_compile_complete. Print Assumptions cm2_compile_complete.
Check cm2_compile_sound. Print Assumptions cm2_compile_sound.
Check self_mm2_halting_iff. Print Assumptions self_mm2_halting_iff.
Check self_host_synthetic_undecidability. Print Assumptions self_host_synthetic_undecidability.
