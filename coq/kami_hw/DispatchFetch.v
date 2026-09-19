(** Instruction-fetch frame for the actual dispatch observer. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary DispatchExecution DispatchObservation
  ActionEvaluator ActionObservation ReadFreeObservation DecodedReadFree.
From Coq Require Import String.
Open Scope string_scope.

Definition dispatch_with_imem (b : HWB)
  (imem : type (Vector (Bit InstrSz) MemAddrSz)) : RegsT :=
  M.add "imem" (hwb_reg (Vector (Bit InstrSz) MemAddrSz) imem) (hwb_regs b).

Definition dispatch_fetch_address (b : HWB) : word MemAddrSz :=
  split1 MemAddrSz (WordSz - MemAddrSz) (hw_pc b).

Definition dispatch_fetch_action : Action Void :=
  fun ty => (Read halted_v : Bool <- "halted";
        Assert !#halted_v;

        Read err_v : Bool <- "err";
        Assert !#err_v;

        (* LASSERT FSM: step rule fires only when FSM is idle (phase = 0). *)
        Read lassert_phase_v : Bit 3 <- "lassert_phase";
        Assert (#lassert_phase_v == $0);

        (* Morphism-coupling FSM (M5): step rule also inhibited while a
           MORPH/COMPOSE coupling computation is in flight,
           same pattern as the LASSERT and CHSH_LASSERT FSMs. *)
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $0);

        (* CHSH_LASSERT FSM: step rule also inhibited when CHSH FSM is running.
           The chsh check is multi-cycle (23 phases sharing one 384-bit mult),
           and on phase 23 the FSM overrides PC/err/error_code if the check
           failed. Until then the step rule sees a stale chsh_check_result;
           the Assert below guarantees the step rule fires only between
           CHSH_LASSERT invocations, never during a CHSH FSM run. *)
        Read chsh_phase_v : Bit 5 <- "chsh_phase";
        Assert (#chsh_phase_v == $0);
        Read chsh_check_result_v : Bool <- "chsh_check_result";

        (* Fetch instruction from internal instruction memory *)
        Read pc_v : Bit WordSz <- "pc";
        Read mu_v : Bit WordSz <- "mu";
        Read regs_v : Vector (Bit WordSz) RegIdxSz <- "regs";
        Read mem_v : Vector (Bit WordSz) MemAddrSz <- "mem";
        Read imem_v : Vector (Bit InstrSz) MemAddrSz <- "imem";
        Read partition_ops_v : Bit WordSz <- "partition_ops";
        Read mdl_ops_v : Bit WordSz <- "mdl_ops";
        Read info_gain_v : Bit WordSz <- "info_gain";
        Read error_code_v : Bit WordSz <- "error_code";
        Read logic_acc_v : Bit WordSz <- "logic_acc";
        Read cert_addr_v : Bit WordSz <- "cert_addr";
        Read active_module_v : Bit PTableIdxSz <- "active_module";
        Read mstatus_v : Bit WordSz <- "mstatus";
        Read mcycle_lo_v : Bit WordSz <- "mcycle_lo";
        Read mcycle_hi_v : Bit WordSz <- "mcycle_hi";
        Read minstret_lo_v : Bit WordSz <- "minstret_lo";
        Read minstret_hi_v : Bit WordSz <- "minstret_hi";
        Read trap_vector_v : Bit WordSz <- "trap_vector";
        Read mu_tensor_v : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        Read module_tensors_v : Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz <- "module_tensors";
        Read csr_heap_base_v : Bit WordSz <- "csr_heap_base";
        Read pt_sizes_v : Vector (Bit WordSz) PTableIdxSz <- "ptTable";
        Read pt_next_id_v : Bit PTableNextIdSz <- "pt_next_id";
        Read certified_v : Bool <- "certified";
        Read morph_src_table_v : Vector (Bit PTableIdxSz) MorphTableIdxSz <- "morph_src_table";
        Read morph_dst_table_v : Vector (Bit PTableIdxSz) MorphTableIdxSz <- "morph_dst_table";
        Read morph_valid_table_v : Vector Bool MorphTableIdxSz <- "morph_valid_table";
        Read morph_coupling_desc_table_v : Vector (Bit DescIdxSz) MorphTableIdxSz <- "morph_coupling_desc_table";
        Read morph_identity_table_v : Vector Bool MorphTableIdxSz <- "morph_identity_table";
        Read morph_next_id_v : Bit MorphTableNextIdSz <- "morph_next_id";
        Read coupling_desc_valid_table_v : Vector Bool CouplingDescIdxSz <- "coupling_desc_valid_table";
        Read coupling_desc_count_table_v : Vector (Bit CouplingPairCountSz) CouplingDescIdxSz <- "coupling_desc_count_table";
        Read coupling_desc_base_table_v : Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz <- "coupling_desc_base_table";
        Read coupling_desc_label_table_v : Vector (Bit WordSz) CouplingDescIdxSz <- "coupling_desc_label_table";
        Read coupling_desc_label_len_table_v : Vector (Bit 6) CouplingDescIdxSz <- "coupling_desc_label_len_table";
        Read coupling_desc_next_id_v : Bit DescTableNextIdSz <- "coupling_desc_next_id";
        Read coupling_pair_next_id_v : Bit DescTableNextIdSz <- "coupling_pair_next_id";
        Read formula_desc_valid_table_v : Vector Bool FormulaDescIdxSz <- "formula_desc_valid_table";
        Read formula_desc_next_id_v : Bit DescTableNextIdSz <- "formula_desc_next_id";
        Read cert_desc_valid_table_v : Vector Bool CertDescIdxSz <- "cert_desc_valid_table";
        Read cert_desc_next_id_v : Bit DescTableNextIdSz <- "cert_desc_next_id";
        Read desc_meta_valid_table_v : Vector Bool DescMetaIdxSz <- "desc_meta_valid_table";
        Read desc_meta_next_id_v : Bit DescTableNextIdSz <- "desc_meta_next_id";

        (* Witness counter registers — 8-bucket CHSH trial state *)
        Read wc_same_00_v : Bit WordSz <- "wc_same_00";
        Read wc_diff_00_v : Bit WordSz <- "wc_diff_00";
        Read wc_same_01_v : Bit WordSz <- "wc_same_01";
        Read wc_diff_01_v : Bit WordSz <- "wc_diff_01";
        Read wc_same_10_v : Bit WordSz <- "wc_same_10";
        Read wc_diff_10_v : Bit WordSz <- "wc_diff_10";
        Read wc_same_11_v : Bit WordSz <- "wc_same_11";
        Read wc_diff_11_v : Bit WordSz <- "wc_diff_11";

        (* Bianchi conservation check: tensor_total must not exceed mu.
           Check BEFORE executing the instruction (matches handwritten RTL). *)
        LET t0 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~0~0~0)];
        LET t1 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~0~0~1)];
        LET t2 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~0~1~0)];
        LET t3 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~0~1~1)];
        LET t4 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~1~0~0)];
        LET t5 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~1~0~1)];
        LET t6 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~1~1~0)];
        LET t7 : Bit WordSz <- #mu_tensor_v@[$$(WO~0~1~1~1)];
        LET t8 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~0~0~0)];
        LET t9 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~0~0~1)];
        LET t10 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~0~1~0)];
        LET t11 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~0~1~1)];
        LET t12 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~1~0~0)];
        LET t13 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~1~0~1)];
        LET t14 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~1~1~0)];
        LET t15 : Bit WordSz <- #mu_tensor_v@[$$(WO~1~1~1~1)];
        LET tensor_total : Bit WordSz <-
          #t0 + #t1 + #t2 + #t3 + #t4 + #t5 + #t6 + #t7 +
          #t8 + #t9 + #t10 + #t11 + #t12 + #t13 + #t14 + #t15;
        LET bianchi_violation <- #tensor_total > #mu_v;

        LET pc_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #pc_v;
        LET instr_v : Bit InstrSz <- #imem_v@[#pc_addr];
        dispatch_decoded chsh_check_result_v pc_v mu_v regs_v mem_v partition_ops_v mdl_ops_v info_gain_v error_code_v logic_acc_v cert_addr_v active_module_v mcycle_lo_v mcycle_hi_v minstret_lo_v minstret_hi_v trap_vector_v mu_tensor_v module_tensors_v csr_heap_base_v pt_sizes_v pt_next_id_v certified_v morph_src_table_v morph_dst_table_v morph_valid_table_v morph_coupling_desc_table_v morph_identity_table_v morph_next_id_v coupling_desc_valid_table_v coupling_desc_count_table_v coupling_desc_base_table_v coupling_desc_label_table_v coupling_desc_label_len_table_v coupling_desc_next_id_v coupling_pair_next_id_v formula_desc_valid_table_v formula_desc_next_id_v cert_desc_valid_table_v cert_desc_next_id_v desc_meta_valid_table_v desc_meta_next_id_v wc_same_00_v wc_diff_00_v wc_same_01_v wc_diff_01_v wc_same_10_v wc_diff_10_v wc_same_11_v wc_diff_11_v tensor_total instr_v bianchi_violation)%kami_action.

Local Opaque dispatch_decoded.
Local Opaque wplus wminus wmult wmultZ wmultZsu wdivN wdivZ wremN wremZ
  wneg wnot wand wor wxor wlshift wrshift wrshifta wordToNat wordToN
  wlt_dec wslt_dec weq weqb split1 split2 evalZeroExtendTrunc evalSignExtendTrunc.

Lemma dispatch_reads_fetch_frame : forall old old' imem imem' pc key,
  (forall r k, r <> "imem" -> action_read old r k = action_read old' r k) ->
  action_read old "pc" (SyntaxKind (Bit WordSz)) = Some pc ->
  action_read old "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some imem ->
  action_read old' "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some imem' ->
  imem (split1 MemAddrSz (WordSz - MemAddrSz) pc) =
    imem' (split1 MemAddrSz (WordSz - MemAddrSz) pc) ->
  observe_dispatch_write old key = observe_dispatch_write old' key.
Proof.
  intros old old' imem imem' pc key Hagree Hpc Hi Hi' Hfetch.
  unfold observe_dispatch_write.
  change (observe_action_write old key (dispatch_fetch_action type) =
    observe_action_write old' key (dispatch_fetch_action type)).
  unfold dispatch_fetch_action.
  repeat first [
    rewrite <- (Hagree "pc" (SyntaxKind (Bit WordSz))) by discriminate
  | rewrite Hpc
  | rewrite Hi
  | rewrite Hi'
  | progress cbn [observe_action_write]
  | match goal with
    | |- context [action_read old ?r ?k] =>
      rewrite <- (Hagree r k) by discriminate;
      destruct (action_read old r k); [|reflexivity]
    end ].
  cbn [evalExpr evalUniBit].
  change (imem (split1 MemAddrSz 25 pc) = imem' (split1 MemAddrSz 25 pc)) in Hfetch.
  rewrite Hfetch.
  apply observe_read_free_action.
  apply dispatch_decoded_read_free.
Qed.

Lemma action_read_add_imem_other : forall old imem r k,
  r <> "imem" ->
  action_read (M.add "imem"
    (hwb_reg (Vector (Bit InstrSz) MemAddrSz) imem) old) r k =
  action_read old r k.
Proof.
  intros old imem r [k|native] Hne; [|reflexivity].
  unfold action_read, action_read_syntax.
  rewrite M.find_add_2 by exact Hne. reflexivity.
Qed.

Lemma action_read_add_imem : forall old imem,
  action_read (M.add "imem"
    (hwb_reg (Vector (Bit InstrSz) MemAddrSz) imem) old)
    "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some imem.
Proof.
  intros. apply action_read_complete. apply M.find_add_1.
Qed.

Lemma action_read_hwb_pc : forall b,
  action_read (hwb_regs b) "pc" (SyntaxKind (Bit WordSz)) = Some (hw_pc b).
Proof.
  intros. apply action_read_complete. unfold hwb_regs. apply M.find_add_1.
Qed.

(** Every written register, every opcode and arbitrary typed boundary values.
    Assertions are still justified by the successful-execution premise of
    [observe_dispatch_write_correct], not by this observation frame alone. *)
Theorem dispatch_fetch_frame : forall b imem imem' key,
  imem (dispatch_fetch_address b) = imem' (dispatch_fetch_address b) ->
  observe_dispatch_write (dispatch_with_imem b imem) key =
  observe_dispatch_write (dispatch_with_imem b imem') key.
Proof.
  intros b imem imem' key Hfetch. unfold dispatch_with_imem.
  eapply dispatch_reads_fetch_frame with (pc := hw_pc b).
  - intros. repeat rewrite action_read_add_imem_other by assumption. reflexivity.
  - rewrite action_read_add_imem_other by discriminate. apply action_read_hwb_pc.
  - apply action_read_add_imem.
  - apply action_read_add_imem.
  - exact Hfetch.
Qed.

Corollary dispatch_constant_imem_observation : forall b imem key,
  observe_dispatch_write (dispatch_with_imem b imem) key =
  observe_dispatch_write
    (dispatch_with_imem b (fun _ => imem (dispatch_fetch_address b))) key.
Proof. intros. apply dispatch_fetch_frame. reflexivity. Qed.

Lemma dispatch_reads_fetch_eval_frame : forall old old' imem imem' pc,
  (forall r k, r <> "imem" -> action_read old r k = action_read old' r k) ->
  action_read old "pc" (SyntaxKind (Bit WordSz)) = Some pc ->
  action_read old "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some imem ->
  action_read old' "imem" (SyntaxKind (Vector (Bit InstrSz) MemAddrSz)) = Some imem' ->
  imem (split1 MemAddrSz (WordSz - MemAddrSz) pc) =
    imem' (split1 MemAddrSz (WordSz - MemAddrSz) pc) ->
  eval_linear_action old (attrType dispatch_rule type) =
  eval_linear_action old' (attrType dispatch_rule type).
Proof.
  intros old old' imem imem' pc Hagree Hpc Hi Hi' Hfetch.
  change (eval_linear_action old (dispatch_fetch_action type) =
    eval_linear_action old' (dispatch_fetch_action type)).
  unfold dispatch_fetch_action.
  repeat first [
    rewrite <- (Hagree "pc" (SyntaxKind (Bit WordSz))) by discriminate
  | rewrite Hpc
  | rewrite Hi
  | rewrite Hi'
  | progress cbn [eval_linear_action]
  | match goal with
    | |- context [if ?p then _ else _] => destruct p; [|reflexivity]
    end
  | match goal with
    | |- context [action_read old ?r ?k] =>
      rewrite <- (Hagree r k) by discriminate;
      destruct (action_read old r k); [|reflexivity]
    end ].
  cbn [evalExpr evalUniBit].
  change (imem (split1 MemAddrSz 25 pc) = imem' (split1 MemAddrSz 25 pc)) in Hfetch.
  rewrite Hfetch.
  apply eval_read_free_action.
  apply dispatch_decoded_read_free.
Qed.

Theorem dispatch_fetch_eval_frame : forall b imem imem',
  imem (dispatch_fetch_address b) = imem' (dispatch_fetch_address b) ->
  eval_dispatch (dispatch_with_imem b imem) =
  eval_dispatch (dispatch_with_imem b imem').
Proof.
  intros b imem imem' Hfetch. unfold eval_dispatch, dispatch_with_imem.
  erewrite dispatch_reads_fetch_eval_frame with (old' :=
    M.add "imem" (hwb_reg (Vector (Bit InstrSz) MemAddrSz) imem') (hwb_regs b))
    (pc := hw_pc b).
  - reflexivity.
  - intros. repeat rewrite action_read_add_imem_other by assumption. reflexivity.
  - rewrite action_read_add_imem_other by discriminate. apply action_read_hwb_pc.
  - apply action_read_add_imem.
  - apply action_read_add_imem.
  - exact Hfetch.
Qed.

Corollary dispatch_fetch_actual_action_frame : forall b imem imem' u,
  imem (dispatch_fetch_address b) = imem' (dispatch_fetch_address b) ->
  (SemAction (dispatch_with_imem b imem) (attrType dispatch_rule type)
      u (M.empty _) WO <->
   SemAction (dispatch_with_imem b imem') (attrType dispatch_rule type)
      u (M.empty _) WO).
Proof.
  intros. rewrite <- !dispatch_actual_action_iff.
  rewrite (dispatch_fetch_eval_frame b imem imem') by assumption. reflexivity.
Qed.
