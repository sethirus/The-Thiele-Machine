(** Reduction of the actual dispatch observer to its fetched decoded action. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary HWBoundaryReads
  ActionEvaluator ActionObservation ReadFreeObservation DecodedReadFree
  DispatchObservation DispatchFetch.
From Coq Require Import String.
Open Scope string_scope.

Definition hwb_tensor_total (b : HWB) : word WordSz := (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (wplus (hw_mu_tensor b (natToWord 4 0)) (hw_mu_tensor b (natToWord 4 1))) (hw_mu_tensor b (natToWord 4 2))) (hw_mu_tensor b (natToWord 4 3))) (hw_mu_tensor b (natToWord 4 4))) (hw_mu_tensor b (natToWord 4 5))) (hw_mu_tensor b (natToWord 4 6))) (hw_mu_tensor b (natToWord 4 7))) (hw_mu_tensor b (natToWord 4 8))) (hw_mu_tensor b (natToWord 4 9))) (hw_mu_tensor b (natToWord 4 10))) (hw_mu_tensor b (natToWord 4 11))) (hw_mu_tensor b (natToWord 4 12))) (hw_mu_tensor b (natToWord 4 13))) (hw_mu_tensor b (natToWord 4 14))) (hw_mu_tensor b (natToWord 4 15))).
Definition hwb_bianchi (b : HWB) : bool :=
  if wlt_dec (hw_mu b) (hwb_tensor_total b) then true else false.
Definition hwb_decoded (b : HWB) (instruction : word InstrSz) : ActionT type Void :=
  dispatch_decoded
    (hw_chsh_check_result b)
    (hw_pc b)
    (hw_mu b)
    (hw_regs b)
    (hw_mem b)
    (hw_partition_ops b)
    (hw_mdl_ops b)
    (hw_info_gain b)
    (hw_error_code b)
    (hw_logic_acc b)
    (hw_cert_addr b)
    (hw_active_module b)
    (hw_mcycle_lo b)
    (hw_mcycle_hi b)
    (hw_minstret_lo b)
    (hw_minstret_hi b)
    (hw_trap_vector b)
    (hw_mu_tensor b)
    (hw_module_tensors b)
    (hw_csr_heap_base b)
    (hw_ptTable b)
    (hw_pt_next_id b)
    (hw_certified b)
    (hw_morph_src_table b)
    (hw_morph_dst_table b)
    (hw_morph_valid_table b)
    (hw_morph_coupling_desc_table b)
    (hw_morph_identity_table b)
    (hw_morph_next_id b)
    (hw_coupling_desc_valid_table b)
    (hw_coupling_desc_count_table b)
    (hw_coupling_desc_base_table b)
    (hw_coupling_desc_label_table b)
    (hw_coupling_desc_label_len_table b)
    (hw_coupling_desc_next_id b)
    (hw_coupling_pair_next_id b)
    (hw_formula_desc_valid_table b)
    (hw_formula_desc_next_id b)
    (hw_cert_desc_valid_table b)
    (hw_cert_desc_next_id b)
    (hw_desc_meta_valid_table b)
    (hw_desc_meta_next_id b)
    (hw_wc_same_00 b)
    (hw_wc_diff_00 b)
    (hw_wc_same_01 b)
    (hw_wc_diff_01 b)
    (hw_wc_same_10 b)
    (hw_wc_diff_10 b)
    (hw_wc_same_11 b)
    (hw_wc_diff_11 b)
    (hwb_tensor_total b)
    instruction
    (hwb_bianchi b).

Local Opaque dispatch_decoded.
Theorem dispatch_boundary_decoded_observer : forall b imem key,
  observe_dispatch_write (dispatch_with_imem b imem) key =
  observe_action_write (M.empty _) key
    (hwb_decoded b (imem (dispatch_fetch_address b))).
Proof.
  intros. unfold observe_dispatch_write.
  change (observe_action_write (dispatch_with_imem b imem) key
    (dispatch_fetch_action type) =
    observe_action_write (M.empty _) key
      (hwb_decoded b (imem (dispatch_fetch_address b)))).
  unfold dispatch_fetch_action, dispatch_with_imem, hwb_decoded.
  repeat first [progress cbn [observe_action_write]
  | rewrite action_read_add_imem_other by discriminate
  | rewrite action_read_add_imem
  | rewrite hwb_read_halted
  | rewrite hwb_read_err
  | rewrite hwb_read_lassert_phase
  | rewrite hwb_read_mc_phase
  | rewrite hwb_read_chsh_phase
  | rewrite hwb_read_chsh_check_result
  | rewrite hwb_read_pc
  | rewrite hwb_read_mu
  | rewrite hwb_read_regs
  | rewrite hwb_read_mem
  | rewrite hwb_read_imem
  | rewrite hwb_read_partition_ops
  | rewrite hwb_read_mdl_ops
  | rewrite hwb_read_info_gain
  | rewrite hwb_read_error_code
  | rewrite hwb_read_logic_acc
  | rewrite hwb_read_cert_addr
  | rewrite hwb_read_active_module
  | rewrite hwb_read_mstatus
  | rewrite hwb_read_mcycle_lo
  | rewrite hwb_read_mcycle_hi
  | rewrite hwb_read_minstret_lo
  | rewrite hwb_read_minstret_hi
  | rewrite hwb_read_trap_vector
  | rewrite hwb_read_mu_tensor
  | rewrite hwb_read_module_tensors
  | rewrite hwb_read_csr_heap_base
  | rewrite hwb_read_ptTable
  | rewrite hwb_read_pt_next_id
  | rewrite hwb_read_certified
  | rewrite hwb_read_morph_src_table
  | rewrite hwb_read_morph_dst_table
  | rewrite hwb_read_morph_valid_table
  | rewrite hwb_read_morph_coupling_desc_table
  | rewrite hwb_read_morph_identity_table
  | rewrite hwb_read_morph_next_id
  | rewrite hwb_read_coupling_desc_valid_table
  | rewrite hwb_read_coupling_desc_count_table
  | rewrite hwb_read_coupling_desc_base_table
  | rewrite hwb_read_coupling_desc_label_table
  | rewrite hwb_read_coupling_desc_label_len_table
  | rewrite hwb_read_coupling_desc_next_id
  | rewrite hwb_read_coupling_pair_next_id
  | rewrite hwb_read_formula_desc_valid_table
  | rewrite hwb_read_formula_desc_next_id
  | rewrite hwb_read_cert_desc_valid_table
  | rewrite hwb_read_cert_desc_next_id
  | rewrite hwb_read_desc_meta_valid_table
  | rewrite hwb_read_desc_meta_next_id
  | rewrite hwb_read_wc_same_00
  | rewrite hwb_read_wc_diff_00
  | rewrite hwb_read_wc_same_01
  | rewrite hwb_read_wc_diff_01
  | rewrite hwb_read_wc_same_10
  | rewrite hwb_read_wc_diff_10
  | rewrite hwb_read_wc_same_11
  | rewrite hwb_read_wc_diff_11
  ].
  cbn [evalExpr evalUniBit evalBinBit evalBinBitBool evalConstT].
  unfold dispatch_fetch_address, hwb_bianchi, hwb_tensor_total.
  apply observe_read_free_action.
  apply dispatch_decoded_read_free.
Qed.
