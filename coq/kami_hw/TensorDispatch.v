(** Arbitrary decoded state: per-module tensor storage is separate from mu_tensor. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary BoundaryDecoded ActionObservation
  DispatchObservation DispatchExecution DispatchFetch.
From Coq Require Import String NArith.
Open Scope string_scope.
Lemma tensor_set_decoded : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool)
    (chsh_check_result_v : type (Bool))
    (pc_v : type (Bit WordSz))
    (mu_v : type (Bit WordSz))
    (regs_v : type (Vector (Bit WordSz) RegIdxSz))
    (mem_v : type (Vector (Bit WordSz) MemAddrSz))
    (partition_ops_v : type (Bit WordSz))
    (mdl_ops_v : type (Bit WordSz))
    (info_gain_v : type (Bit WordSz))
    (error_code_v : type (Bit WordSz))
    (logic_acc_v : type (Bit WordSz))
    (cert_addr_v : type (Bit WordSz))
    (active_module_v : type (Bit PTableIdxSz))
    (mcycle_lo_v : type (Bit WordSz))
    (mcycle_hi_v : type (Bit WordSz))
    (minstret_lo_v : type (Bit WordSz))
    (minstret_hi_v : type (Bit WordSz))
    (trap_vector_v : type (Bit WordSz))
    (mu_tensor_v : type (Vector (Bit WordSz) MuTensorIdxSz))
    (module_tensors_v : type (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
    (csr_heap_base_v : type (Bit WordSz))
    (pt_sizes_v : type (Vector (Bit WordSz) PTableIdxSz))
    (pt_next_id_v : type (Bit PTableNextIdSz))
    (certified_v : type (Bool))
    (morph_src_table_v : type (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_dst_table_v : type (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_valid_table_v : type (Vector Bool MorphTableIdxSz))
    (morph_coupling_desc_table_v : type (Vector (Bit DescIdxSz) MorphTableIdxSz))
    (morph_identity_table_v : type (Vector Bool MorphTableIdxSz))
    (morph_next_id_v : type (Bit MorphTableNextIdSz))
    (coupling_desc_valid_table_v : type (Vector Bool CouplingDescIdxSz))
    (coupling_desc_count_table_v : type (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz))
    (coupling_desc_base_table_v : type (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz))
    (coupling_desc_label_table_v : type (Vector (Bit WordSz) CouplingDescIdxSz))
    (coupling_desc_label_len_table_v : type (Vector (Bit 6) CouplingDescIdxSz))
    (coupling_desc_next_id_v : type (Bit DescTableNextIdSz))
    (coupling_pair_next_id_v : type (Bit DescTableNextIdSz))
    (formula_desc_valid_table_v : type (Vector Bool FormulaDescIdxSz))
    (formula_desc_next_id_v : type (Bit DescTableNextIdSz))
    (cert_desc_valid_table_v : type (Vector Bool CertDescIdxSz))
    (cert_desc_next_id_v : type (Bit DescTableNextIdSz))
    (desc_meta_valid_table_v : type (Vector Bool DescMetaIdxSz))
    (desc_meta_next_id_v : type (Bit DescTableNextIdSz))
    (wc_same_00_v : type (Bit WordSz))
    (wc_diff_00_v : type (Bit WordSz))
    (wc_same_01_v : type (Bit WordSz))
    (wc_diff_01_v : type (Bit WordSz))
    (wc_same_10_v : type (Bit WordSz))
    (wc_diff_10_v : type (Bit WordSz))
    (wc_same_11_v : type (Bit WordSz))
    (wc_diff_11_v : type (Bit WordSz))
    (tensor_total : type (Bit WordSz))
    (bianchi_violation : type (Bool))
,
 observe_action_write (M.empty _) "module_tensors"
   (dispatch_decoded chsh_check_result_v pc_v mu_v regs_v mem_v partition_ops_v mdl_ops_v info_gain_v error_code_v logic_acc_v cert_addr_v active_module_v mcycle_lo_v mcycle_hi_v minstret_lo_v minstret_hi_v trap_vector_v mu_tensor_v module_tensors_v csr_heap_base_v pt_sizes_v pt_next_id_v certified_v morph_src_table_v morph_dst_table_v morph_valid_table_v morph_coupling_desc_table_v morph_identity_table_v morph_next_id_v coupling_desc_valid_table_v coupling_desc_count_table_v coupling_desc_base_table_v coupling_desc_label_table_v coupling_desc_label_len_table_v coupling_desc_next_id_v coupling_pair_next_id_v formula_desc_valid_table_v formula_desc_next_id_v cert_desc_valid_table_v cert_desc_next_id_v desc_meta_valid_table_v desc_meta_next_id_v wc_same_00_v wc_diff_00_v wc_same_01_v wc_diff_01_v wc_same_10_v wc_diff_10_v wc_same_11_v wc_diff_11_v tensor_total (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 37) (NToWord 96 (N.shiftl 2 88)))))) bianchi_violation) =
 Some (existT (fullType type)
   (SyntaxKind (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
   (if bianchi_violation then module_tensors_v else
     fun m => if weq m ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) then
       (fun i => if weq i ((WS a0 (WS a1 (WS a2 (WS a3 WO))))) then combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (natToWord 24 0)
         else module_tensors_v ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) i)
       else module_tensors_v m)).
Proof.
 intros. destruct bianchi_violation;
 lazy;
 clear_concrete_word_casts;
 reflexivity.
Qed.

Lemma tensor_get_decoded : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool)
    (chsh_check_result_v : type (Bool))
    (pc_v : type (Bit WordSz))
    (mu_v : type (Bit WordSz))
    (regs_v : type (Vector (Bit WordSz) RegIdxSz))
    (mem_v : type (Vector (Bit WordSz) MemAddrSz))
    (partition_ops_v : type (Bit WordSz))
    (mdl_ops_v : type (Bit WordSz))
    (info_gain_v : type (Bit WordSz))
    (error_code_v : type (Bit WordSz))
    (logic_acc_v : type (Bit WordSz))
    (cert_addr_v : type (Bit WordSz))
    (active_module_v : type (Bit PTableIdxSz))
    (mcycle_lo_v : type (Bit WordSz))
    (mcycle_hi_v : type (Bit WordSz))
    (minstret_lo_v : type (Bit WordSz))
    (minstret_hi_v : type (Bit WordSz))
    (trap_vector_v : type (Bit WordSz))
    (mu_tensor_v : type (Vector (Bit WordSz) MuTensorIdxSz))
    (module_tensors_v : type (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
    (csr_heap_base_v : type (Bit WordSz))
    (pt_sizes_v : type (Vector (Bit WordSz) PTableIdxSz))
    (pt_next_id_v : type (Bit PTableNextIdSz))
    (certified_v : type (Bool))
    (morph_src_table_v : type (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_dst_table_v : type (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_valid_table_v : type (Vector Bool MorphTableIdxSz))
    (morph_coupling_desc_table_v : type (Vector (Bit DescIdxSz) MorphTableIdxSz))
    (morph_identity_table_v : type (Vector Bool MorphTableIdxSz))
    (morph_next_id_v : type (Bit MorphTableNextIdSz))
    (coupling_desc_valid_table_v : type (Vector Bool CouplingDescIdxSz))
    (coupling_desc_count_table_v : type (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz))
    (coupling_desc_base_table_v : type (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz))
    (coupling_desc_label_table_v : type (Vector (Bit WordSz) CouplingDescIdxSz))
    (coupling_desc_label_len_table_v : type (Vector (Bit 6) CouplingDescIdxSz))
    (coupling_desc_next_id_v : type (Bit DescTableNextIdSz))
    (coupling_pair_next_id_v : type (Bit DescTableNextIdSz))
    (formula_desc_valid_table_v : type (Vector Bool FormulaDescIdxSz))
    (formula_desc_next_id_v : type (Bit DescTableNextIdSz))
    (cert_desc_valid_table_v : type (Vector Bool CertDescIdxSz))
    (cert_desc_next_id_v : type (Bit DescTableNextIdSz))
    (desc_meta_valid_table_v : type (Vector Bool DescMetaIdxSz))
    (desc_meta_next_id_v : type (Bit DescTableNextIdSz))
    (wc_same_00_v : type (Bit WordSz))
    (wc_diff_00_v : type (Bit WordSz))
    (wc_same_01_v : type (Bit WordSz))
    (wc_diff_01_v : type (Bit WordSz))
    (wc_same_10_v : type (Bit WordSz))
    (wc_diff_10_v : type (Bit WordSz))
    (wc_same_11_v : type (Bit WordSz))
    (wc_diff_11_v : type (Bit WordSz))
    (tensor_total : type (Bit WordSz))
    (bianchi_violation : type (Bool))
,
 observe_action_write (M.empty _) "regs"
   (dispatch_decoded chsh_check_result_v pc_v mu_v regs_v mem_v partition_ops_v mdl_ops_v info_gain_v error_code_v logic_acc_v cert_addr_v active_module_v mcycle_lo_v mcycle_hi_v minstret_lo_v minstret_hi_v trap_vector_v mu_tensor_v module_tensors_v csr_heap_base_v pt_sizes_v pt_next_id_v certified_v morph_src_table_v morph_dst_table_v morph_valid_table_v morph_coupling_desc_table_v morph_identity_table_v morph_next_id_v coupling_desc_valid_table_v coupling_desc_count_table_v coupling_desc_base_table_v coupling_desc_label_table_v coupling_desc_label_len_table_v coupling_desc_next_id_v coupling_pair_next_id_v formula_desc_valid_table_v formula_desc_next_id_v cert_desc_valid_table_v cert_desc_next_id_v desc_meta_valid_table_v desc_meta_next_id_v wc_same_00_v wc_diff_00_v wc_same_01_v wc_diff_01_v wc_same_10_v wc_diff_10_v wc_same_11_v wc_diff_11_v tensor_total (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 38) (NToWord 96 (N.shiftl 2 88)))))) bianchi_violation) =
 Some (existT (fullType type) (SyntaxKind (Vector (Bit WordSz) RegIdxSz))
   (if bianchi_violation then regs_v else
     fun r => if weq r (WS a0 (WS a1 (WS a2 (WS a3 WO)))) then
       module_tensors_v (WS b4 (WS b5 (WS b6 (WS b7 WO)))) (WS b0 (WS b1 (WS b2 (WS b3 WO))))
     else regs_v r)).
Proof.
 intros. destruct bianchi_violation;
 lazy;
 clear_concrete_word_casts;
 reflexivity.
Qed.

Theorem tensor_set_dispatch_observation : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool) b imem,
  imem (dispatch_fetch_address b) = (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 37) (NToWord 96 (N.shiftl 2 88)))))) ->
  observe_dispatch_write (dispatch_with_imem b imem) "module_tensors" =
 Some (existT (fullType type)
   (SyntaxKind (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
   (if hwb_bianchi b then (hw_module_tensors b) else
     fun m => if weq m ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) then
       (fun i => if weq i ((WS a0 (WS a1 (WS a2 (WS a3 WO))))) then combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (natToWord 24 0)
         else (hw_module_tensors b) ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) i)
       else (hw_module_tensors b) m)).
Proof.
  intros. rewrite dispatch_boundary_decoded_observer. rewrite H.
  unfold hwb_decoded. apply tensor_set_decoded.
Qed.

Corollary tensor_set_actual_write : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool) b imem u,
  imem (dispatch_fetch_address b) = (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 37) (NToWord 96 (N.shiftl 2 88)))))) ->
  eval_dispatch (dispatch_with_imem b imem) = Some u ->
  M.find "module_tensors" (M.union u (dispatch_with_imem b imem)) =
 Some (existT (fullType type)
   (SyntaxKind (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
   (if hwb_bianchi b then (hw_module_tensors b) else
     fun m => if weq m ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) then
       (fun i => if weq i ((WS a0 (WS a1 (WS a2 (WS a3 WO))))) then combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (natToWord 24 0)
         else (hw_module_tensors b) ((WS a4 (WS a5 (WS a6 (WS a7 WO))))) i)
       else (hw_module_tensors b) m)).
Proof.
  intros. rewrite M.find_union.
  rewrite <- (observe_dispatch_write_correct _ _ _ H0).
  rewrite (tensor_set_dispatch_observation a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b imem H).
  reflexivity.
Qed.

Theorem tensor_get_dispatch_observation : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool) b imem,
  imem (dispatch_fetch_address b) = (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 38) (NToWord 96 (N.shiftl 2 88)))))) ->
  observe_dispatch_write (dispatch_with_imem b imem) "regs" =
 Some (existT (fullType type) (SyntaxKind (Vector (Bit WordSz) RegIdxSz))
   (if hwb_bianchi b then (hw_regs b) else
     fun r => if weq r (WS a0 (WS a1 (WS a2 (WS a3 WO)))) then
       (hw_module_tensors b) (WS b4 (WS b5 (WS b6 (WS b7 WO)))) (WS b0 (WS b1 (WS b2 (WS b3 WO))))
     else (hw_regs b) r)).
Proof.
  intros. rewrite dispatch_boundary_decoded_observer. rewrite H.
  unfold hwb_decoded. apply tensor_get_decoded.
Qed.

Corollary tensor_get_actual_write : forall (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 : bool) b imem u,
  imem (dispatch_fetch_address b) = (combine ((WS c0 (WS c1 (WS c2 (WS c3 (WS c4 (WS c5 (WS c6 (WS c7 WO))))))))) (combine ((WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))) (combine ((WS a0 (WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 WO))))))))) (combine (natToWord 8 38) (NToWord 96 (N.shiftl 2 88)))))) ->
  eval_dispatch (dispatch_with_imem b imem) = Some u ->
  M.find "regs" (M.union u (dispatch_with_imem b imem)) =
 Some (existT (fullType type) (SyntaxKind (Vector (Bit WordSz) RegIdxSz))
   (if hwb_bianchi b then (hw_regs b) else
     fun r => if weq r (WS a0 (WS a1 (WS a2 (WS a3 WO)))) then
       (hw_module_tensors b) (WS b4 (WS b5 (WS b6 (WS b7 WO)))) (WS b0 (WS b1 (WS b2 (WS b3 WO))))
     else (hw_regs b) r)).
Proof.
  intros. rewrite M.find_union.
  rewrite <- (observe_dispatch_write_correct _ _ _ H0).
  rewrite (tensor_get_dispatch_observation a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b imem H).
  reflexivity.
Qed.

Lemma dispatch_csr_status_not_written : forall b imem,
  observe_dispatch_write (dispatch_with_imem b imem) "csr_status" = None.
Proof.
  intros. rewrite dispatch_boundary_decoded_observer.
  unfold hwb_decoded. lazy. reflexivity.
Qed.

Corollary dispatch_csr_status_preserved : forall b imem u,
  eval_dispatch (dispatch_with_imem b imem) = Some u ->
  M.find "csr_status" (M.union u (dispatch_with_imem b imem)) =
  M.find "csr_status" (dispatch_with_imem b imem).
Proof.
  intros. rewrite M.find_union.
  rewrite <- (observe_dispatch_write_correct _ _ _ H).
  rewrite dispatch_csr_status_not_written. reflexivity.
Qed.

Lemma dispatch_csr_heap_base_not_written : forall b imem,
  observe_dispatch_write (dispatch_with_imem b imem) "csr_heap_base" = None.
Proof.
  intros. rewrite dispatch_boundary_decoded_observer.
  unfold hwb_decoded. lazy. reflexivity.
Qed.

Corollary dispatch_csr_heap_base_preserved : forall b imem u,
  eval_dispatch (dispatch_with_imem b imem) = Some u ->
  M.find "csr_heap_base" (M.union u (dispatch_with_imem b imem)) =
  M.find "csr_heap_base" (dispatch_with_imem b imem).
Proof.
  intros. rewrite M.find_union.
  rewrite <- (observe_dispatch_write_correct _ _ _ H).
  rewrite dispatch_csr_heap_base_not_written. reflexivity.
Qed.
