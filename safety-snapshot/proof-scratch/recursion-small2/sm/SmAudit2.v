(* Assumption audit for the recursion-small2 files. Every line must print
   "Closed under the global context". *)
Require Import Sm.SmTally Sm.SmTallyL Sm.SmLoops Sm.SmLoops2 Sm.SmLoops3 Sm.SmMMAOff Sm.SmBlock
  Sm.SmChain Sm.SmFixed Sm.SmFixedPoint Sm.SmNoExact Sm.SmSmnAll.
Print Assumptions sm2_kleene_obs.
Print Assumptions sm2_no_exact.
Print Assumptions sm2_smn_all.
Print Assumptions sm2_reg_bound.
Print Assumptions sm2_final_numbers.
Print Assumptions sm2_ev_spec.
Print Assumptions sm2_ev_MMA.
Print Assumptions sm2_bint_of_MMA.
Print Assumptions sm2_while.
Print Assumptions sm2_fan_spec.
Print Assumptions sm2_check_loop.
Print Assumptions sm2_commit_loop.
Print Assumptions sm2_certify_loop.
Print Assumptions sm2_trap_zero.
Print Assumptions sm2_trap_pos.
Print Assumptions sm2_mma_ctx.
Print Assumptions sm2_mma_ctx_halt.
Print Assumptions sm2_setup.
Print Assumptions sm2_setup_halt.
Print Assumptions sm2_replay.
Print Assumptions sm2_VG_forward.
Print Assumptions sm2_VG_halt.
Print Assumptions sm2_fwd_core.
Print Assumptions sm2_bwd_core.
Print Assumptions sm2_kleene_fun.
