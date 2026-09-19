(* B4 contract probe: model, observation, transformer, and every limitative
   result with its global assumptions. *)
From Kernel Require Import VMSelfGuest VMSelfRun MM2ComplementUndec VMSelfRice VMSelfRiceUndec.

Print g_input. Print g_beh. Print g_equiv. Print g_extensional.
Print rpc. Print reloc_i. Print reloc. Print embeds.
Print qprog. Print rice_pre. Print rice_restore. Print rice_prog. Print g_bottom.
Print g_decides. Print g_halts_on_zero. Print g_returns_zero.

Check MM2_HALTING_compl_undec. Print Assumptions MM2_HALTING_compl_undec.
Check g_beh_host_iff. Print Assumptions g_beh_host_iff.
Check reloc_run. Print Assumptions reloc_run.
Check tail_beh. Print Assumptions tail_beh.
Check rice_prog_wf. Print Assumptions rice_prog_wf.
Check rice_prog_halting. Print Assumptions rice_prog_halting.
Check rice_prog_nonhalting. Print Assumptions rice_prog_nonhalting.
Check g_bottom_beh. Print Assumptions g_bottom_beh.
Check self_rice. Print Assumptions self_rice.
Check self_rice_dual. Print Assumptions self_rice_dual.
Check g_decides_decidable. Print Assumptions g_decides_decidable.
Check self_rice_representable. Print Assumptions self_rice_representable.
Check g_halts_on_zero_undecidable. Print Assumptions g_halts_on_zero_undecidable.
Check g_returns_zero_undecidable. Print Assumptions g_returns_zero_undecidable.
Check total_run_obstruction. Print Assumptions total_run_obstruction.
