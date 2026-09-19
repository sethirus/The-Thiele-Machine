(** Exact AST preservation of the fetch factoring, before later CPU changes. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore.
From Coq Require Import List String.
Open Scope string_scope.
Definition dispatch_before_fetch_factoring : Action Void := fun ty =>
  (Read halted_v : Bool <- "halted";
        Assert !#halted_v;

        Read err_v : Bool <- "err";
        Assert !#err_v;

        (* LASSERT FSM: step rule fires only when FSM is idle (phase = 0). *)
        Read lassert_phase_v : Bit 3 <- "lassert_phase";
        Assert (#lassert_phase_v == $0);

        (* Morphism-coupling FSM (M5): step rule also inhibited while a
           MORPH/COMPOSE/MORPH_TENSOR coupling computation is in flight,
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
        LET legacy_instr : Bit WordSz <- UniBit (Trunc WordSz InstrUpperSz) #instr_v;

        (* ISA-v2 transport: legacy low lane plus selected upper-lane fields. *)
        LET isa_version : Bit 8 <- UniBit (ConstExtract 120 8 0) #instr_v;
        LET format_id : Bit FormatIdSz <- UniBit (ConstExtract 112 FormatIdSz 8) #instr_v;
        LET flags : Bit 16 <- UniBit (ConstExtract 96 16 16) #instr_v;
        LET ext0 : Bit WordSz <- UniBit (ConstExtract 32 WordSz 64) #instr_v;
        LET opcode : Bit OpcodeSz <- UniBit (ConstExtract 24 8 0) #legacy_instr;
        LET op_a   : Bit 8        <- UniBit (ConstExtract 16 8 8) #legacy_instr;
        LET op_b   : Bit 8        <- UniBit (ConstExtract 8 8 16) #legacy_instr;
        LET cost_v : Bit CostSz   <- UniBit (Trunc 8 24) #legacy_instr;
        LET subtype : Bit FormatSubtypeSz <- UniBit (ConstExtract 12 FormatSubtypeSz 0) #flags;
        LET desc_kind : Bit DescKindFieldSz <- UniBit (ConstExtract 8 DescKindFieldSz 4) #flags;
        LET inline_len : Bit InlineLenSz <- UniBit (Trunc InlineLenSz 8) #flags;
        LET primary_desc_id : Bit DescIdxSz <- UniBit (Trunc DescIdxSz 28) #ext0;
        LET secondary_desc_id : Bit DescIdxSz <- UniBit (ConstExtract 6 DescIdxSz 22) #ext0;
        LET primary_desc_id_7 : Bit DescTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #primary_desc_id;
        LET secondary_desc_id_7 : Bit DescTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #secondary_desc_id;
        LET secondary_desc_present <- #secondary_desc_id != $0;

        LET is_morph_opcode <-
          (#opcode == $$(OP_MORPH)) || (#opcode == $$(OP_COMPOSE)) ||
          (#opcode == $$(OP_MORPH_ID)) || (#opcode == $$(OP_MORPH_DELETE)) ||
          (#opcode == $$(OP_MORPH_ASSERT)) || (#opcode == $$(OP_MORPH_TENSOR)) ||
          (#opcode == $$(OP_MORPH_GET));
        LET is_cert_opcode <-
          (#opcode == $$(OP_LASSERT)) || (#opcode == $$(OP_LJOIN)) ||
          (#opcode == $$(OP_EMIT)) || (#opcode == $$(OP_REVEAL)) ||
          (#opcode == $$(OP_CERTIFY)) || (#opcode == $$(OP_MORPH_ASSERT)) ||
          (#opcode == $$(OP_CHSH_LASSERT));
        LET is_branch_ext_capable <-
          (#opcode == $$(OP_JUMP)) || (#opcode == $$(OP_JNEZ)) || (#opcode == $$(OP_CALL));
        LET is_tensor_ext_capable <-
          (#opcode == $$(OP_REVEAL)) || (#opcode == $$(OP_TENSOR_SET)) || (#opcode == $$(OP_TENSOR_GET));
        LET format_known <-
          (#format_id == $$(FMT_LEGACY)) || (#format_id == $$(FMT_BRANCH_EXT)) ||
          (#format_id == $$(FMT_TENSOR_EXT)) || (#format_id == $$(FMT_MORPH_INLINE)) ||
          (#format_id == $$(FMT_DESC)) || (#format_id == $$(FMT_CERT_INLINE));
        LET format_allowed_for_opcode <-
          IF (#format_id == $$(FMT_LEGACY))
          then $$true
          else (IF (#format_id == $$(FMT_BRANCH_EXT))
                then #is_branch_ext_capable
                else (IF (#format_id == $$(FMT_TENSOR_EXT))
                      then #is_tensor_ext_capable
                      else (IF (#format_id == $$(FMT_MORPH_INLINE))
                            then #is_morph_opcode
                            else (IF (#format_id == $$(FMT_DESC))
                                  then (#is_morph_opcode || #is_cert_opcode)
                                  else (IF (#format_id == $$(FMT_CERT_INLINE))
                                        then #is_cert_opcode
                                        else $$false)))));
        LET desc_kind_is_zero <- #desc_kind == $$(WO~0~0~0~0);
        LET desc_kind_is_morph <- #desc_kind == $$(WO~0~0~0~0);
        LET desc_kind_is_coupling <- #desc_kind == $$(WO~0~0~0~1);
        LET desc_kind_is_formula <- #desc_kind == $$(WO~0~0~1~0);
        LET desc_kind_is_cert <- #desc_kind == $$(WO~0~0~1~1);
        LET desc_kind_is_meta <- #desc_kind == $$(WO~0~1~0~0);
        LET desc_kind_valid <-
          #desc_kind_is_morph || #desc_kind_is_coupling || #desc_kind_is_formula ||
          #desc_kind_is_cert || #desc_kind_is_meta;
        LET flags_are_zero <- #flags == $0;
        LET inline_len_zero <- #inline_len == $0;
        LET inline_len_too_large <- #inline_len > $8;
        LET reserved_flag_fault <-
          ((#format_id == $$(FMT_LEGACY)) || (#format_id == $$(FMT_BRANCH_EXT)) ||
           (#format_id == $$(FMT_TENSOR_EXT))) && !#flags_are_zero;
        LET inline_payload_fault <-
          ((#format_id == $$(FMT_MORPH_INLINE)) || (#format_id == $$(FMT_CERT_INLINE))) &&
          (!#desc_kind_is_zero || #inline_len_zero || #inline_len_too_large);
        LET desc_flag_fault <-
          (#format_id == $$(FMT_DESC)) && (!#inline_len_zero || !#desc_kind_valid);

        LET primary_morph_desc_invalid <-
          (#primary_desc_id_7 >= #morph_next_id_v) || !(#morph_valid_table_v@[#primary_desc_id]);
        LET secondary_morph_desc_invalid <-
          #secondary_desc_present &&
          ((#secondary_desc_id_7 >= #morph_next_id_v) || !(#morph_valid_table_v@[#secondary_desc_id]));
        LET primary_coupling_desc_invalid <-
          (#primary_desc_id_7 >= #coupling_desc_next_id_v) || !(#coupling_desc_valid_table_v@[#primary_desc_id]);
        LET secondary_coupling_desc_invalid <-
          #secondary_desc_present &&
          ((#secondary_desc_id_7 >= #coupling_desc_next_id_v) ||
           !(#coupling_desc_valid_table_v@[#secondary_desc_id]));
        LET primary_formula_desc_invalid <-
          (#primary_desc_id_7 >= #formula_desc_next_id_v) || !(#formula_desc_valid_table_v@[#primary_desc_id]);
        LET secondary_formula_desc_invalid <-
          #secondary_desc_present &&
          ((#secondary_desc_id_7 >= #formula_desc_next_id_v) ||
           !(#formula_desc_valid_table_v@[#secondary_desc_id]));
        LET primary_cert_desc_invalid <-
          (#primary_desc_id_7 >= #cert_desc_next_id_v) || !(#cert_desc_valid_table_v@[#primary_desc_id]);
        LET secondary_cert_desc_invalid <-
          #secondary_desc_present &&
          ((#secondary_desc_id_7 >= #cert_desc_next_id_v) ||
           !(#cert_desc_valid_table_v@[#secondary_desc_id]));
        LET primary_meta_desc_invalid <-
          (#primary_desc_id_7 >= #desc_meta_next_id_v) || !(#desc_meta_valid_table_v@[#primary_desc_id]);
        LET secondary_meta_desc_invalid <-
          #secondary_desc_present &&
          ((#secondary_desc_id_7 >= #desc_meta_next_id_v) ||
           !(#desc_meta_valid_table_v@[#secondary_desc_id]));
        LET generic_desc_range_fault <-
          (#format_id == $$(FMT_DESC)) &&
          (((#desc_kind_is_morph || #desc_kind_is_coupling || #desc_kind_is_meta) &&
            ((#desc_kind_is_morph && (#primary_morph_desc_invalid || #secondary_morph_desc_invalid)) ||
             (#desc_kind_is_coupling && (#primary_coupling_desc_invalid || #secondary_coupling_desc_invalid)) ||
             (#desc_kind_is_meta && (#primary_meta_desc_invalid || #secondary_meta_desc_invalid)))));
        LET cert_desc_kind_mismatch <-
          (#format_id == $$(FMT_DESC)) && #is_cert_opcode &&
          !(#desc_kind_is_formula || #desc_kind_is_cert);
        LET morph_desc_kind_mismatch <-
          (#format_id == $$(FMT_DESC)) && #is_morph_opcode &&
          !(#desc_kind_is_morph || #desc_kind_is_coupling || #desc_kind_is_meta);
        LET cert_desc_invalid <-
          (#format_id == $$(FMT_DESC)) &&
          (#cert_desc_kind_mismatch ||
           (#desc_kind_is_formula && (#primary_formula_desc_invalid || #secondary_formula_desc_invalid)) ||
           (#desc_kind_is_cert && (#primary_cert_desc_invalid || #secondary_cert_desc_invalid)));
        LET morph_alloc_opcode <-
          (#opcode == $$(OP_MORPH)) || (#opcode == $$(OP_COMPOSE)) ||
          (#opcode == $$(OP_MORPH_ID)) || (#opcode == $$(OP_MORPH_TENSOR));
        LET rich_table_overflow <-
          (#morph_alloc_opcode && (#morph_next_id_v >= $16)) ||
          (((#format_id == $$(FMT_MORPH_INLINE)) || (#format_id == $$(FMT_DESC))) &&
           (#opcode == $$(OP_MORPH)) &&
           (#coupling_desc_next_id_v >= $16));
        LET isa_version_invalid <- #isa_version != $$(WO~0~0~0~0~0~0~1~0);
        LET format_invalid <- !#format_known || !#format_allowed_for_opcode || #morph_desc_kind_mismatch;
        LET inline_malformed <- #reserved_flag_fault || #inline_payload_fault || #desc_flag_fault;
        LET rich_fault <-
          #isa_version_invalid || #format_invalid || #inline_malformed ||
          #generic_desc_range_fault || #rich_table_overflow || #cert_desc_invalid;
        LET rich_fault_error_code : Bit WordSz <-
          IF #isa_version_invalid
          then $$(ERR_ISA_VERSION)
          else (IF #format_invalid
                then $$(ERR_FORMAT_INVALID)
                else (IF #inline_malformed
                      then $$(ERR_INLINE_MALFORMED)
                      else (IF #generic_desc_range_fault
                            then $$(ERR_DESC_RANGE)
                            else (IF #rich_table_overflow
                                  then $$(ERR_TABLE_OVERFLOW)
                                  else (IF #cert_desc_invalid
                                        then $$(ERR_CERT_DESC_INVALID)
                                        else #error_code_v)))));

        (* Zero-extend the declared delta and the packed bit-count.  In the
           compact ISA, OP_EMIT/OP_REVEAL/OP_READ_PORT use op_b as the number
           of information bits carried by the instruction. *)
        LET cost32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #cost_v;
        LET op_b_32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;
        LET bit_payload_charge : Bit WordSz <-
          IF ((#opcode == $$(OP_EMIT)) ||
              (#opcode == $$(OP_REVEAL)) ||
              (#opcode == $$(OP_READ_PORT)))
          then #op_b_32
          else $0;
        LET bit_priced_mu : Bit WordSz <- #mu_v + #bit_payload_charge + #cost32 + $1;

        (* LASSERT: kind bit packed into op_a[5]; freg = dst_idx; creg = src_idx.
           SAT (kind=1): enter multi-cycle FSM.  UNSAT (kind=0): immediate trap. *)
        LET lassert_kind_bit : Bit 1 <- UniBit (ConstExtract 5 1 2) #op_a;
        LET lassert_is_sat <- #lassert_kind_bit == $$(WO~1);
        LET is_lassert <- #opcode == $$(OP_LASSERT);
        LET lassert_unsat_trap <- #is_lassert && !#lassert_is_sat;

        (* Compute the declared-delta-only μ path.  Bit-bearing cert setters
           use bit_priced_mu instead. *)
        LET new_mu : Bit WordSz <- #mu_v + #cost32;

        (* Default: PC+1 *)
        LET pc_plus_1 : Bit WordSz <- #pc_v + $1;

        (* Register index: truncate op_a/op_b to 5 bits *)
        LET dst_idx : Bit RegIdxSz <- UniBit (Trunc RegIdxSz _) #op_a;
        LET src_idx : Bit RegIdxSz <- UniBit (Trunc RegIdxSz _) #op_b;

        (* For ADD/SUB: rs1 = op_b[7:4], rs2 = op_b[3:0] *)
        LET op_b_hi : Bit 4 <- UniBit (ConstExtract 4 4 0) #op_b;
        LET op_b_lo : Bit 4 <- UniBit (Trunc 4 4) #op_b;
        LET rs1_idx : Bit RegIdxSz <- UniBit (ZeroExtendTrunc _ _) #op_b_hi;
        LET rs2_idx : Bit RegIdxSz <- UniBit (ZeroExtendTrunc _ _) #op_b_lo;

        (* Read source register values *)
        LET rs1_val : Bit WordSz <- #regs_v@[#rs1_idx];
        LET rs2_val : Bit WordSz <- #regs_v@[#rs2_idx];
        LET dst_val : Bit WordSz <- #regs_v@[#dst_idx];
        LET src_val : Bit WordSz <- #regs_v@[#src_idx];

        (* Zero-extend op_b to 32 bits for LOAD_IMM immediate *)
        LET imm32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;

        (* Memory address from register value — register-indirect addressing *)
        LET mem_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #src_val;
        LET mem_addr_a : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #dst_val;
        (* Legacy 8-bit address for XOR_LOAD (still uses immediate addressing) *)
        LET mem_addr_imm : Bit MemAddrSz <- UniBit (ZeroExtendTrunc _ _) #op_b;
        LET mem_val : Bit WordSz <- read_mem #mem_addr #mem_v;
        (* HEAP_LOAD/HEAP_STORE: address relative to csr_heap_base. *)
        LET heap_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#csr_heap_base_v + #src_val);
        LET heap_addr_a : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#csr_heap_base_v + #dst_val);
        LET heap_val : Bit WordSz <- read_mem #heap_addr #mem_v;
        LET mem_val_imm : Bit WordSz <- read_mem #mem_addr_imm #mem_v;

        (* Stack pointer (r31) for CALL/RET *)
        LET sp_val : Bit WordSz <- #regs_v@[$$(SP_IDX)];
        LET sp_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_val;
        LET sp_inc : Bit WordSz <- #sp_val + $1;
        LET sp_dec : Bit WordSz <- #sp_val - $1;
        LET sp_dec_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_dec;

        (* Partition wall enforcement: LOAD/STORE/CALL/RET may only access active module region. *)
        LET active_region_size : Bit WordSz <- #pt_sizes_v@[#active_module_v];
        LET load_in_bounds <-
          check_bounds (IF (#opcode == $$(OP_HEAP_LOAD)) then #heap_addr else #mem_addr) #active_region_size;
        LET store_in_bounds <-
          check_bounds (IF (#opcode == $$(OP_HEAP_STORE)) then #heap_addr_a else #mem_addr_a) #active_region_size;
        LET call_in_bounds <- check_bounds #sp_addr #active_region_size;
        LET ret_in_bounds <- check_bounds #sp_dec_addr #active_region_size;
        (* XOR_LOAD uses immediate addressing — no locality check, matches Coq step_xor_load *)
        LET is_load_op <- (#opcode == $$(OP_LOAD)) ||
                          (#opcode == $$(OP_HEAP_LOAD));
        LET is_store_op <- (#opcode == $$(OP_STORE)) || (#opcode == $$(OP_HEAP_STORE));
        LET is_call_op <- #opcode == $$(OP_CALL);
        LET is_ret_op <- #opcode == $$(OP_RET);
        LET load_locality_bad <- #is_load_op && !#load_in_bounds;
        LET store_locality_bad <- #is_store_op && !#store_in_bounds;
        LET call_locality_bad <- #is_call_op && !#call_in_bounds;
        LET ret_locality_bad <- #is_ret_op && !#ret_in_bounds;
        LET locality_violation <-
          #load_locality_bad || #store_locality_bad || #call_locality_bad || #ret_locality_bad;

        (* Logic-gated physics lock for high-value instructions. *)
        LET logic_key_ok <- #logic_acc_v == $$(LOGIC_GATE_KEY);
        LET is_high_value_op <-
          (#opcode == $$(OP_REVEAL)) || (#opcode == $$(OP_PDISCOVER)) || (#opcode == $$(OP_CHSH_TRIAL));
        LET high_value_locked <- #is_high_value_op && !#logic_key_ok;


        (* Capacity guards: never wrap partition table indices. *)
        LET ptable_full <- #pt_next_id_v >= $64;
        LET ptable_room_one <- !#ptable_full;
        LET ptable_room_two <- (#pt_next_id_v + $2) <= $64;
        LET pnew_overflow <- (#opcode == $$(OP_PNEW)) && !#ptable_room_one;
        LET psplit_overflow <- (#opcode == $$(OP_PSPLIT)) && !#ptable_room_two;
        LET pmerge_overflow <- (#opcode == $$(OP_PMERGE)) && !#ptable_room_one;
        LET ptable_overflow_violation <- #pnew_overflow || #psplit_overflow || #pmerge_overflow;

        (* Partition-table indexed value probes for in-core PDISCOVER datapath *)
        LET pt_probe_idx : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #op_b;
        LET pt_probe_size : Bit WordSz <- #pt_sizes_v@[#pt_probe_idx];

        (* JNEZ: target address from op_b zero-extended *)
        LET jnez_target : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;

        (* JUMP/CALL: target from {op_a, op_b} = 16-bit zero-extended *)
        LET jump_target_16 : Bit 16 <- {#op_a, #op_b};
        LET jump_target : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #jump_target_16;

        LET ret_pc : Bit WordSz <-
          IF #ret_in_bounds
          then read_mem #sp_dec_addr #mem_v
          else $0;

        (* Morph dispatch (M4 complete): FMT_MORPH_INLINE carries the
           operands that do not fit in the legacy low lane. All morph opcodes
           now use hardware morph-table state. Encoding limits for legacy paths
           are documented per opcode below. MORPH_TENSOR supports both
           FMT_MORPH_INLINE (g from ext0[5:0]) and legacy (g = slot 0). *)
        LET is_morph_inline <- #format_id == $$(FMT_MORPH_INLINE);
        LET is_morph_ext <- (#opcode == $$(OP_MORPH)) && #is_morph_inline;
        LET is_compose_ext <- (#opcode == $$(OP_COMPOSE)) && #is_morph_inline;
        LET is_morph_id_ext <- (#opcode == $$(OP_MORPH_ID)) && #is_morph_inline;
        LET is_morph_delete_ext <- (#opcode == $$(OP_MORPH_DELETE)) && #is_morph_inline;
        LET is_morph_get_ext <- (#opcode == $$(OP_MORPH_GET)) && #is_morph_inline;
        LET is_morph_assert_ext <- (#opcode == $$(OP_MORPH_ASSERT)) && (#format_id == $$(FMT_CERT_INLINE));
        (* Legacy morph paths: use hardware morph-table state with available
           low-lane operands. MORPH: self-morphism (src=dst=op_b module) since
           dst_mod not in 32-bit word. COMPOSE: m2=slot 0. MORPH_GET: selector 0.
           MORPH_ASSERT: cert_addr set to 0 (no inline checksum in 32-bit word). *)
        LET is_morph_legacy <- (#opcode == $$(OP_MORPH)) && !#is_morph_inline;
        LET is_compose_legacy <- (#opcode == $$(OP_COMPOSE)) && !#is_morph_inline;
        LET is_morph_id_legacy <- (#opcode == $$(OP_MORPH_ID)) && !#is_morph_inline;
        LET is_morph_delete_legacy <- (#opcode == $$(OP_MORPH_DELETE)) && !#is_morph_inline;
        LET is_morph_get_legacy <- (#opcode == $$(OP_MORPH_GET)) && !#is_morph_inline;
        LET is_morph_assert_legacy <- (#opcode == $$(OP_MORPH_ASSERT)) && !(#format_id == $$(FMT_CERT_INLINE));
        LET is_morph_tensor_inline <- (#opcode == $$(OP_MORPH_TENSOR)) && #is_morph_inline;
        LET is_morph_tensor_legacy <- (#opcode == $$(OP_MORPH_TENSOR)) && !#is_morph_inline;
        LET is_morph_tensor <- (#opcode == $$(OP_MORPH_TENSOR));

        LET ext_morph_dst_mod : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz 26) #ext0;
        (* MORPH's coupling operand in the extended format: a memory base
           address for the serialized coupling block (M5), not a descriptor
           reference. 7 bits (MemAddrSz) covers the full 128-word memory;
           bits 13-31 of ext0 remain unused for this opcode. *)
        LET ext_coupling_base : Bit MemAddrSz <- UniBit (ConstExtract 6 MemAddrSz 19) #ext0;
        LET ext_compose_m2 : Bit MorphTableIdxSz <- UniBit (Trunc MorphTableIdxSz 28) #ext0;
        LET ext_get_selector : Bit 2 <- UniBit (Trunc 2 30) #ext0;
        LET ext_assert_property_checksum : Bit WordSz <- #ext0;

        LET morph_src_mod_idx : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz 2) #op_b;
        LET morph_identity_mod_idx : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz 2) #op_b;
        LET morph_lookup_idx : Bit MorphTableIdxSz <- UniBit (Trunc MorphTableIdxSz 4) #op_b;
        LET morph_delete_idx : Bit MorphTableIdxSz <- UniBit (Trunc MorphTableIdxSz 4) #op_a;
        LET morph_assert_idx : Bit MorphTableIdxSz <- UniBit (Trunc MorphTableIdxSz 4) #op_a;
        LET morph_slot : Bit MorphTableIdxSz <- UniBit (Trunc MorphTableIdxSz 1) #morph_next_id_v;
        LET morph_slot_word : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #morph_slot;

        LET ext_compose_m2_7 : Bit MorphTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #ext_compose_m2;
        LET morph_lookup_idx_7 : Bit MorphTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #morph_lookup_idx;
        LET morph_delete_idx_7 : Bit MorphTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #morph_delete_idx;
        LET morph_assert_idx_7 : Bit MorphTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #morph_assert_idx;
        LET morph_alloc_room <- #morph_next_id_v < $16;

        LET morph_src_mod_exists <- #pt_sizes_v@[#morph_src_mod_idx] != $0;
        LET morph_dst_mod_exists <- #pt_sizes_v@[#ext_morph_dst_mod] != $0;
        LET morph_identity_mod_exists <- #pt_sizes_v@[#morph_identity_mod_idx] != $0;

        (* Descriptor capacity is checked here. The FSM checks pair capacity
           before writes; empty couplings need no pair-table space. *)
        LET coupling_alloc_room <-
          (#coupling_desc_next_id_v < $16);

        LET compose_m1_valid <-
          (#morph_lookup_idx_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_lookup_idx]);
        LET compose_m2_valid <-
          (#ext_compose_m2_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#ext_compose_m2]);
        LET compose_m1_src : Bit PTableIdxSz <- #morph_src_table_v@[#morph_lookup_idx];
        LET compose_m1_dst : Bit PTableIdxSz <- #morph_dst_table_v@[#morph_lookup_idx];
        LET compose_m2_src : Bit PTableIdxSz <- #morph_src_table_v@[#ext_compose_m2];
        LET compose_m2_dst : Bit PTableIdxSz <- #morph_dst_table_v@[#ext_compose_m2];
        LET compose_endpoints_match <- #compose_m1_dst == #compose_m2_src;

        (* Legacy COMPOSE uses morph slot 0 as m2 (m2 absent from 32-bit encoding). *)
        LET morph_zero_idx : Bit MorphTableIdxSz <- $0;
        LET morph_zero_idx_7 : Bit MorphTableNextIdSz <- $0;
        LET legacy_compose_m2_valid <-
          (#morph_zero_idx_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_zero_idx]);
        LET legacy_compose_m2_src : Bit PTableIdxSz <- #morph_src_table_v@[#morph_zero_idx];
        LET legacy_compose_m2_dst : Bit PTableIdxSz <- #morph_dst_table_v@[#morph_zero_idx];
        LET legacy_compose_endpoints_match <- #compose_m1_dst == #legacy_compose_m2_src;

        (* MORPH_TENSOR: f = morph at morph_lookup_idx (op_b), g = ext0[5:0] (EXT)
           or slot 0 (legacy, since g absent from 32-bit word). Reuses ext_compose_m2
           layout since both fields live in ext0[5:0]. *)
        LET morph_tensor_g_id : Bit MorphTableIdxSz <-
          IF #is_morph_tensor_inline then #ext_compose_m2 else $0;
        LET morph_tensor_g_id_7 : Bit MorphTableNextIdSz <-
          IF #is_morph_tensor_inline then #ext_compose_m2_7 else $0;
        LET morph_tensor_g_valid <-
          (#morph_tensor_g_id_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_tensor_g_id]);
        LET morph_tensor_g_dst : Bit PTableIdxSz <- #morph_dst_table_v@[#morph_tensor_g_id];

        LET morph_lookup_valid <-
          (#morph_lookup_idx_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_lookup_idx]);
        LET morph_delete_valid <-
          (#morph_delete_idx_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_delete_idx]);
        LET morph_assert_valid <-
          (#morph_assert_idx_7 < #morph_next_id_v) &&
          (#morph_valid_table_v@[#morph_assert_idx]);

        LET morph_get_src : Bit PTableIdxSz <- #morph_src_table_v@[#morph_lookup_idx];
        LET morph_get_dst : Bit PTableIdxSz <- #morph_dst_table_v@[#morph_lookup_idx];
        LET morph_get_is_identity <- #morph_identity_table_v@[#morph_lookup_idx];
        LET morph_get_coupling_desc : Bit DescIdxSz <- #morph_coupling_desc_table_v@[#morph_lookup_idx];
        LET morph_get_coupling_desc_7 : Bit DescTableNextIdSz <- UniBit (ZeroExtendTrunc _ _) #morph_get_coupling_desc;
        LET morph_get_coupling_zero <- #morph_get_coupling_desc == $0;
        LET morph_get_coupling_valid <-
          (#morph_get_coupling_desc_7 < #coupling_desc_next_id_v) &&
          (#coupling_desc_valid_table_v@[#morph_get_coupling_desc]);
        LET morph_get_coupling_fault <-
          #is_morph_get_ext && #morph_lookup_valid &&
          !#morph_get_coupling_zero && !#morph_get_coupling_valid;
        LET morph_get_coupling_count_raw : Bit CouplingPairCountSz <-
          IF #morph_get_coupling_zero
          then $0
          else #coupling_desc_count_table_v@[#morph_get_coupling_desc];
        LET morph_get_src_word : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #morph_get_src;
        LET morph_get_dst_word : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #morph_get_dst;
        LET morph_get_coupling_count : Bit WordSz <-
          UniBit (ZeroExtendTrunc _ _) #morph_get_coupling_count_raw;
        LET morph_get_identity_word : Bit WordSz <-
          IF #morph_get_is_identity then $1 else $0;
        (* Legacy MORPH_GET always uses selector 0 (returns src module ID). *)
        LET effective_get_selector : Bit 2 <-
          IF #is_morph_get_ext then #ext_get_selector else $0;
        LET morph_get_value : Bit WordSz <-
          IF (#effective_get_selector == $$(WO~0~0))
          then #morph_get_src_word
          else (IF (#effective_get_selector == $$(WO~0~1))
                then #morph_get_dst_word
                else (IF (#effective_get_selector == $$(WO~1~0))
                      then #morph_get_coupling_count
                      else #morph_get_identity_word));

        (* Fault predicates: cover both EXT and legacy paths, plus MORPH_TENSOR. *)
        LET morph_ext_endpoint_fault <-
          (#is_morph_ext && (!#morph_src_mod_exists || !#morph_dst_mod_exists || !#coupling_alloc_room)) ||
          (#is_morph_id_ext && !#morph_identity_mod_exists);
        LET morph_legacy_endpoint_fault <-
          (#is_morph_legacy && !#morph_src_mod_exists) ||
          (#is_morph_id_legacy && !#morph_identity_mod_exists);
        LET compose_lookup_fault <-
          (#is_compose_ext && (!#compose_m1_valid || !#compose_m2_valid)) ||
          (#is_compose_legacy && (!#compose_m1_valid || !#legacy_compose_m2_valid));
        LET compose_type_fault <-
          (#is_compose_ext && #compose_m1_valid && #compose_m2_valid && !#compose_endpoints_match) ||
          (#is_compose_legacy && #compose_m1_valid && #legacy_compose_m2_valid && !#legacy_compose_endpoints_match);
        LET morph_delete_fault <-
          ((#is_morph_delete_ext || #is_morph_delete_legacy) && !#morph_delete_valid);
        LET morph_get_fault <-
          ((#is_morph_get_ext || #is_morph_get_legacy) && !#morph_lookup_valid);
        LET morph_assert_fault <-
          ((#is_morph_assert_ext || #is_morph_assert_legacy) && !#morph_assert_valid);
        LET morph_tensor_lookup_fault <-
          #is_morph_tensor && !#compose_m1_valid;
        LET morph_tensor_g_fault <-
          #is_morph_tensor && #compose_m1_valid && !#morph_tensor_g_valid;
        LET morph_runtime_fault <-
          #morph_ext_endpoint_fault || #morph_legacy_endpoint_fault ||
          #compose_lookup_fault || #compose_type_fault ||
          #morph_delete_fault || #morph_get_fault || #morph_get_coupling_fault ||
          #morph_assert_fault || #morph_tensor_lookup_fault || #morph_tensor_g_fault;
        LET morph_runtime_error_code : Bit WordSz <-
          IF (#compose_type_fault)
          then $$(ERR_COMPOSE_TYPE)
          else (IF (#compose_lookup_fault || #morph_delete_fault || #morph_get_fault ||
                    #morph_assert_fault || #morph_tensor_lookup_fault || #morph_tensor_g_fault)
                then $$(ERR_MORPH_NOT_FOUND)
                else $$(ERR_COUPLING_INVALID));

        LET morph_alloc_success <- #is_morph_ext && #morph_alloc_room &&
          #morph_src_mod_exists && #morph_dst_mod_exists && #coupling_alloc_room;
        LET legacy_morph_alloc_success <- #is_morph_legacy && #morph_alloc_room &&
          #morph_src_mod_exists;  (* self-morphism: same module for src and dst *)
        LET morph_id_success <- #is_morph_id_ext && #morph_alloc_room && #morph_identity_mod_exists;
        LET morph_id_legacy_success <- #is_morph_id_legacy && #morph_alloc_room && #morph_identity_mod_exists;
        LET compose_success <- #is_compose_ext && #morph_alloc_room && #coupling_alloc_room &&
          #compose_m1_valid && #compose_m2_valid && #compose_endpoints_match;
        LET legacy_compose_success <- #is_compose_legacy && #morph_alloc_room && #coupling_alloc_room &&
          #compose_m1_valid && #legacy_compose_m2_valid && #legacy_compose_endpoints_match;
        LET morph_tensor_success <- #is_morph_tensor && #morph_alloc_room && #coupling_alloc_room &&
          #compose_m1_valid && #morph_tensor_g_valid;
        LET morph_get_success <-
          (#is_morph_get_ext || #is_morph_get_legacy) &&
          #morph_lookup_valid && !#morph_get_coupling_fault;
        LET morph_delete_success <-
          (#is_morph_delete_ext || #is_morph_delete_legacy) && #morph_delete_valid;
        LET morph_assert_success <-
          (#is_morph_assert_ext || #is_morph_assert_legacy) && #morph_assert_valid;
        LET morph_allocates <-
          #morph_alloc_success || #legacy_morph_alloc_success ||
          #morph_id_success || #morph_id_legacy_success ||
          #compose_success || #legacy_compose_success ||
          #morph_tensor_success;

        (* Allocation fields: select src/dst/coupling/identity for the new morph slot. *)
        LET morph_alloc_src : Bit PTableIdxSz <-
          IF #morph_alloc_success then #morph_src_mod_idx
          else (IF #legacy_morph_alloc_success then #morph_src_mod_idx  (* self: src=op_b module *)
          else (IF (#morph_id_success || #morph_id_legacy_success) then #morph_identity_mod_idx
          else (IF #compose_success then #compose_m1_src
          else (IF #legacy_compose_success then #compose_m1_src
          else (IF #morph_tensor_success then #compose_m1_src  (* tensor: src from f *)
          else #morph_identity_mod_idx)))));
        LET morph_alloc_dst : Bit PTableIdxSz <-
          IF #morph_alloc_success then #ext_morph_dst_mod
          else (IF #legacy_morph_alloc_success then #morph_src_mod_idx  (* self: dst=op_b module *)
          else (IF (#morph_id_success || #morph_id_legacy_success) then #morph_identity_mod_idx
          else (IF #compose_success then #compose_m2_dst
          else (IF #legacy_compose_success then #legacy_compose_m2_dst
          else (IF #morph_tensor_success then #morph_tensor_g_dst  (* tensor: dst from g *)
          else #morph_identity_mod_idx)))));
        (* Morphism-coupling FSM (M5) dispatch: MORPH, COMPOSE, and
           MORPH_TENSOR each allocate a fresh descriptor for their coupling
           data rather than writing $0 (empty) unconditionally. The
           descriptor id is known immediately, coupling_desc_next_id_v,
           before the FSM runs; the FSM's own job is to populate that
           descriptor's base/count/pairs and advance the two next-id
           counters, in the background, while pc/mu/registers/morph tables
           already commit this same cycle exactly as before. *)
        LET mc_enters_fsm <-
          #morph_alloc_success || #compose_success || #legacy_compose_success ||
          #morph_tensor_success;
        LET morph_alloc_coupling : Bit DescIdxSz <-
          IF #mc_enters_fsm
          then UniBit (Trunc DescIdxSz _) #coupling_desc_next_id_v
          else $0;
        LET morph_alloc_identity <- #morph_id_success || #morph_id_legacy_success;

        (* Morphism-coupling FSM (M5): which existing descriptors COMPOSE and
           MORPH_TENSOR need to read from. m1/f always come from
           morph_lookup_idx; m2 comes from ext_compose_m2 (extended COMPOSE)
           or morph_zero_idx (legacy COMPOSE, m2 is always slot 0); g comes
           from morph_tensor_g_id. Identity morphisms always carry empty
           coupling by construction (MORPH_ID always allocates coupling_desc
           0), so COMPOSE's identity shortcut is realized by zeroing that
           side's pair count rather than by a separate code path: the shared
           copy loop then naturally copies only the non-identity side. *)
        LET mc_compose_active <- #compose_success || #legacy_compose_success;
        LET mc_m1_id : Bit MorphTableIdxSz <- #morph_lookup_idx;
        LET mc_m2_id : Bit MorphTableIdxSz <-
          IF #is_compose_ext then #ext_compose_m2 else #morph_zero_idx;
        LET mc_f_id : Bit MorphTableIdxSz <- #morph_lookup_idx;
        LET mc_g_id : Bit MorphTableIdxSz <- #morph_tensor_g_id;

        LET mc_compose_is_id1 <- #morph_identity_table_v@[#mc_m1_id];
        LET mc_compose_is_id2 <- #morph_identity_table_v@[#mc_m2_id];
        LET mc_needs_join <-
          #mc_compose_active && !#mc_compose_is_id1 && !#mc_compose_is_id2;
        LET mc_needs_copy <-
          (#mc_compose_active && (#mc_compose_is_id1 || #mc_compose_is_id2)) ||
          #morph_tensor_success;

        LET mc_src1_desc : Bit DescIdxSz <-
          IF #mc_compose_active
          then #morph_coupling_desc_table_v@[#mc_m1_id]
          else #morph_coupling_desc_table_v@[#mc_f_id];
        LET mc_src2_desc : Bit DescIdxSz <-
          IF #mc_compose_active
          then #morph_coupling_desc_table_v@[#mc_m2_id]
          else #morph_coupling_desc_table_v@[#mc_g_id];

        LET mc_src1_base_d : Bit CouplingPairIdxSz <-
          #coupling_desc_base_table_v@[#mc_src1_desc];
        LET mc_src1_count_d : Bit CouplingPairCountSz <-
          IF (#mc_compose_active && #mc_compose_is_id1) then $0
          else #coupling_desc_count_table_v@[#mc_src1_desc];
        LET mc_src2_base_d : Bit CouplingPairIdxSz <-
          #coupling_desc_base_table_v@[#mc_src2_desc];
        LET mc_src2_count_d : Bit CouplingPairCountSz <-
          IF (#mc_compose_active && #mc_compose_is_id2) then $0
          else #coupling_desc_count_table_v@[#mc_src2_desc];

        LET mc_new_phase : Bit 4 <-
          IF #morph_alloc_success then $$(WO~0~0~0~1)
          else (IF #mc_needs_copy then $$(WO~0~1~0~0)
          else (IF #mc_needs_join then $$(WO~0~1~1~1)
          else $$(WO~0~0~0~0)));
        LET mc_write_base_d : Bit DescTableNextIdSz <- #coupling_pair_next_id_v;

        (* Execute: compute all possible results *)
        LET add_result : Bit WordSz <- #rs1_val + #rs2_val;
        LET sub_result : Bit WordSz <- #rs1_val - #rs2_val;
        LET and_result : Bit WordSz <- BinBit (Band _) #rs1_val #rs2_val;
        LET or_result  : Bit WordSz <- BinBit (Bor _) #rs1_val #rs2_val;
        LET shl_result : Bit WordSz <- BinBit (Sll _ _) #rs1_val #rs2_val;
        LET shr_result : Bit WordSz <- BinBit (Srl _ _) #rs1_val #rs2_val;
        LET mul_result : Bit WordSz <- BinBit (Mul _ SignUU) #rs1_val #rs2_val;
        LET lui_shift  : Bit WordSz <- $$(natToWord WordSz 8);
        LET lui_result : Bit WordSz <- BinBit (Sll _ _) #imm32 #lui_shift;
        LET xor_result : Bit WordSz <- #dst_val ~+ #src_val;
        LET jnez_taken <- #dst_val != $0;

        (* Popcount for XOR_RANK: tree-based bit count (32-bit optimized).
           Using binary literals to avoid Peano extraction overhead. *)
        LET pop_val : Bit WordSz <- #src_val;
        (* Step 1: pairs - 0x55555555 *)
        LET pop_mask1 : Bit WordSz <- $$(WO~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1);
        LET pop_s1a : Bit WordSz <- #pop_val ~& #pop_mask1;
        LET pop_s1b : Bit WordSz <- (BinBit (Srl _ _) #pop_val ($$(WO~0~0~0~0~0~1))) ~& #pop_mask1;
        LET pop_2 : Bit WordSz <- #pop_s1a + #pop_s1b;
        (* Step 2: nibbles - 0x33333333 *)
        LET pop_mask2 : Bit WordSz <- $$(WO~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1);
        LET pop_n1 : Bit WordSz <- #pop_2 ~& #pop_mask2;
        LET pop_n2 : Bit WordSz <- (BinBit (Srl _ _) #pop_2 ($$(WO~0~0~0~0~1~0))) ~& #pop_mask2;
        LET pop_4 : Bit WordSz <- #pop_n1 + #pop_n2;
        (* Step 3: bytes - 0x0F0F0F0F *)
        LET pop_mask3 : Bit WordSz <- $$(WO~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1);
        LET pop_b1 : Bit WordSz <- #pop_4 ~& #pop_mask3;
        LET pop_b2 : Bit WordSz <- (BinBit (Srl _ _) #pop_4 ($$(WO~0~0~0~1~0~0))) ~& #pop_mask3;
        LET pop_8 : Bit WordSz <- #pop_b1 + #pop_b2;
        (* Step 4: 2-byte groups - 0x00FF00FF *)
        LET pop_mask4 : Bit WordSz <- $$(WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1);
        LET pop_h1 : Bit WordSz <- #pop_8 ~& #pop_mask4;
        LET pop_h2 : Bit WordSz <- (BinBit (Srl _ _) #pop_8 ($$(WO~0~0~1~0~0~0))) ~& #pop_mask4;
        LET pop_16 : Bit WordSz <- #pop_h1 + #pop_h2;
        (* Step 5: final sum for 32-bit - 0x0000FFFF *)
        LET pop_mask5 : Bit WordSz <- $$(WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1);
        LET pop_q1 : Bit WordSz <- #pop_16 ~& #pop_mask5;
        LET pop_q2 : Bit WordSz <- (BinBit (Srl _ _) #pop_16 ($$(WO~0~1~0~0~0~0))) ~& #pop_mask5;
        LET popcount : Bit WordSz <- #pop_q1 + #pop_q2;

        (* CHSH_TRIAL certificate gate:
           - packed outcomes op_b are 2-bit values (0..3)
           - x=1 settings (op_a[1]) require non-zero mu_tensor evidence from REVEAL *)
        LET chsh_outcomes_bad <- #op_b > $$(WO~0~0~0~0~0~0~1~1);
        LET is_x1_trial <- #op_a > $$(WO~0~0~0~0~0~0~0~1);
        LET chsh_cert_missing <- (#is_x1_trial) && (#tensor_total == $0);
        LET chsh_bits_bad <- #chsh_cert_missing;

          (* CHSH_TRIAL witness counter update:
            op_a[1:0] = setting (x,y) → selects bucket (00/01/10/11)
            op_b[1:0] = outcome (a,b) → same when a==b, diff otherwise
           We use 2-bit truncations and compare to 2-bit constants. *)
        LET chsh_settings : Bit 2 <- UniBit (Trunc 2 _) #op_a;
        LET chsh_outcomes : Bit 2 <- UniBit (Trunc 2 _) #op_b;
        (* Outcomes same when both bits equal: 00 or 11 → same; 01 or 10 → diff *)
        LET chsh_outcomes_same <- (#chsh_outcomes == $$(WO~0~0)) || (#chsh_outcomes == $$(WO~1~1));
        LET is_bucket_00 <- #chsh_settings == $$(WO~0~0);
        LET is_bucket_01 <- #chsh_settings == $$(WO~0~1);
        LET is_bucket_10 <- #chsh_settings == $$(WO~1~0);
        LET is_bucket_11 <- #chsh_settings == $$(WO~1~1);

        (* No-Free-Insight guard for info-bearing instructions.
           EMIT pays op_b bits directly in μ, so the legacy cost>=op_b guard
           remains only for PDISCOVER's non-bit-priced discovery counter. *)
        LET is_info_gain_op <-
          (#opcode == $$(OP_PDISCOVER)) || (#opcode == $$(OP_EMIT));
        LET is_declared_bound_op <- #opcode == $$(OP_PDISCOVER);
        LET nfi_violation <- #is_declared_bound_op && (#cost32 < #op_b_32);

        (* CHSH_TRIAL is valid only when opcode matches and no violations *)
        LET is_chsh_valid <- (#opcode == $$(OP_CHSH_TRIAL)) && !#chsh_bits_bad &&
          !#bianchi_violation && !#locality_violation && !#ptable_overflow_violation &&
          !#high_value_locked && !#nfi_violation && !#rich_fault;

        (* ============================================================
           CHSH_LASSERT column-contractivity check (combinational).

           Hardware mirror of [column_contractive_check_witness] in VMStep.v.
           For each (x,y) ∈ {00,01,10,11} pair we have:
             n_xy = wc_same_xy + wc_diff_xy  (unsigned)
             d_xy = wc_same_xy - wc_diff_xy  (signed; we track |d| and sign)
           The Z-arithmetic check
             A := n00²·n10² - d00²·n10² - d10²·n00² >= 0
             B := n01²·n11² - d01²·n11² - d11²·n01² >= 0
             C := d00·d01·n10·n11 + d10·d11·n00·n01
             0 < n_xy  for all xy
             C² ≤ A·B
           is implemented below using fixed-width wide-bit unsigned arithmetic
           with explicit sign tracking. Bit widths chosen so that with 32-bit
           counters the check is exact: max |C|² and |A·B| are ≤ 2^264, hence
           384-bit final values.

           Widths:
             64  bits: n_xy and |d_xy| (zero-extended from 32 bits)
             128 bits: n_xy², |d_xy|² (each input ≤ 2^33, product ≤ 2^66)
             256 bits: n²·n², |d|²·n² (each ≤ 2^132)
             384 bits: A·B and C² (each ≤ 2^264)

           Result: [chsh_lassert_check_ok] is true iff every condition holds. *)
        LET is_chsh_lassert <- (#opcode == $$(OP_CHSH_LASSERT));

        (* Zero-extend the 8 counter registers to 64 bits. *)
        LET ll_s00_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_same_00_v;
        LET ll_d00_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_diff_00_v;
        LET ll_s01_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_same_01_v;
        LET ll_d01_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_diff_01_v;
        LET ll_s10_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_same_10_v;
        LET ll_d10_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_diff_10_v;
        LET ll_s11_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_same_11_v;
        LET ll_d11_64 : Bit 64 <- UniBit (ZeroExtendTrunc WordSz 64) #wc_diff_11_v;

        (* Compute n_xy = same + diff (unsigned, 64-bit fits 33-bit sum). *)
        LET ll_n00 : Bit 64 <- #ll_s00_64 + #ll_d00_64;
        LET ll_n01 : Bit 64 <- #ll_s01_64 + #ll_d01_64;
        LET ll_n10 : Bit 64 <- #ll_s10_64 + #ll_d10_64;
        LET ll_n11 : Bit 64 <- #ll_s11_64 + #ll_d11_64;

        (* Compute |d_xy| and sign_xy (sign=true means same < diff, i.e. d<0). *)
        LET ll_sign00 <- #ll_s00_64 < #ll_d00_64;
        LET ll_sign01 <- #ll_s01_64 < #ll_d01_64;
        LET ll_sign10 <- #ll_s10_64 < #ll_d10_64;
        LET ll_sign11 <- #ll_s11_64 < #ll_d11_64;
        LET ll_abs_d00 : Bit 64 <-
          IF #ll_sign00 then (#ll_d00_64 - #ll_s00_64) else (#ll_s00_64 - #ll_d00_64);
        LET ll_abs_d01 : Bit 64 <-
          IF #ll_sign01 then (#ll_d01_64 - #ll_s01_64) else (#ll_s01_64 - #ll_d01_64);
        LET ll_abs_d10 : Bit 64 <-
          IF #ll_sign10 then (#ll_d10_64 - #ll_s10_64) else (#ll_s10_64 - #ll_d10_64);
        LET ll_abs_d11 : Bit 64 <-
          IF #ll_sign11 then (#ll_d11_64 - #ll_s11_64) else (#ll_s11_64 - #ll_d11_64);

        (* All n_xy must be strictly positive. *)
        LET ll_all_n_pos <-
          (#ll_n00 != $0) && (#ll_n01 != $0) && (#ll_n10 != $0) && (#ll_n11 != $0);

        (* CHSH_LASSERT check: the column-contractive check (8 squarings + 14
           wide products + final compare) used to live combinationally here,
           costing ~1131 DSP48E1 slices in synth (more than K325T's 840) and
           ~353K LUTs in -nodsp mode (over K325T's 203K). The check now lives
           in the multi-cycle FSM defined as Rule "chsh_lassert_fsm" below.
           That rule shares ONE 384x384 multiplier across 22 phases, dropping
           the steady-state DSP footprint by an order of magnitude. The step
           rule below reads the FSM's committed boolean from a register and
           treats the trap as never-firing from this rule (the FSM phase 23
           commit overrides PC / err / error_code when the check fails). *)
        LET chsh_lassert_check_ok <- #chsh_check_result_v;
        LET chsh_lassert_trap     <- $$false;

        (* REVEAL: legacy tensor index is op_a[3:0].
           FMT_TENSOR_EXT overrides it with ext0[3:0], providing the first
           live upper-lane execution path in hardware. *)
        LET legacy_tensor_idx : Bit MuTensorIdxSz <- UniBit (Trunc MuTensorIdxSz _) #op_a;
        LET ext_tensor_idx : Bit MuTensorIdxSz <- UniBit (Trunc MuTensorIdxSz 28) #ext0;
        LET tensor_idx : Bit MuTensorIdxSz <-
          IF ((#opcode == $$(OP_REVEAL)) && (#format_id == $$(FMT_TENSOR_EXT)))
          then #ext_tensor_idx
          else #legacy_tensor_idx;
        LET tensor_old : Bit WordSz <- #mu_tensor_v@[#tensor_idx];
        LET tensor_new_val : Bit WordSz <- #tensor_old + #op_b_32;

        (* Per-module tensor addressing, canonical encoding:
             TENSOR_SET: op_a[7:4] = module, op_a[3:0] = i*4+j, op_b = value
             TENSOR_GET: op_a[3:0] = dst, op_b[7:4] = module, op_b[3:0] = i*4+j *)
        LET tset_mod : Bit ModTensorIdxSz <- UniBit (ConstExtract 4 4 0) #op_a;
        LET tset_idx : Bit MuTensorIdxSz <- UniBit (Trunc 4 4) #op_a;
        LET tget_mod : Bit ModTensorIdxSz <- UniBit (ConstExtract 4 4 0) #op_b;
        LET tget_idx : Bit MuTensorIdxSz <- UniBit (Trunc 4 4) #op_b;
        LET tset_row : Vector (Bit WordSz) MuTensorIdxSz <- #module_tensors_v@[#tset_mod];
        LET tget_row : Vector (Bit WordSz) MuTensorIdxSz <- #module_tensors_v@[#tget_mod];
        LET tget_val : Bit WordSz <- #tget_row@[#tget_idx];

        (* ============================================================
           Determine new PC
           *)
        LET new_pc : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #trap_vector_v
          else (IF (#opcode == $$(OP_HALT))
                then #pc_v
                else (IF (#opcode == $$(OP_JUMP))
                      then #jump_target
                      else (IF (#opcode == $$(OP_CALL))
                            then #jump_target
                            else (IF (#opcode == $$(OP_RET))
                                  then #ret_pc
                                  else (IF ((#opcode == $$(OP_JNEZ)) && #jnez_taken)
                                        then #jnez_target
                                        else (IF (#opcode == $$(OP_LASSERT))
                                              then (IF #lassert_is_sat then #pc_v else #trap_vector_v)
                                              else (IF #chsh_lassert_trap
                                                    then #trap_vector_v
                                                    else #pc_plus_1)))))));

        (* Pre-compute XOR_SWAP result: write both dst<-src and src<-dst *)
        LET swap_regs : Vector (Bit WordSz) RegIdxSz <-
          (#regs_v@[#dst_idx <- #src_val])@[#src_idx <- #dst_val];

        LET morph_result_regs : Vector (Bit WordSz) RegIdxSz <-
          IF #morph_allocates
          then #regs_v@[#dst_idx <- #morph_slot_word]
          else (IF #morph_get_success
                then #regs_v@[#dst_idx <- #morph_get_value]
                else #regs_v);

        (* ============================================================
           Determine new register file
           *)
        LET new_regs : Vector (Bit WordSz) RegIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #regs_v
          else (IF (#opcode == $$(OP_LOAD_IMM))
          then #regs_v@[#dst_idx <- #imm32]
          else (IF (#opcode == $$(OP_ADD))
                then #regs_v@[#dst_idx <- #add_result]
          else (IF (#opcode == $$(OP_SUB))
                then #regs_v@[#dst_idx <- #sub_result]
          else (IF (#opcode == $$(OP_XFER))
                then #regs_v@[#dst_idx <- #src_val]
          else (IF (#opcode == $$(OP_LOAD))
                then #regs_v@[#dst_idx <- #mem_val]
          else (IF (#opcode == $$(OP_XOR_LOAD))
                then #regs_v@[#dst_idx <- #mem_val_imm]
          else (IF (#opcode == $$(OP_XOR_ADD))
                then #regs_v@[#dst_idx <- #xor_result]
          else (IF (#opcode == $$(OP_XOR_SWAP))
                then #swap_regs
          else (IF (#opcode == $$(OP_XOR_RANK))
                then #regs_v@[#dst_idx <- #popcount]
          else (IF (#opcode == $$(OP_CALL))
                then #regs_v@[$$(SP_IDX) <- #sp_inc]
          else (IF (#opcode == $$(OP_RET))
                then #regs_v@[$$(SP_IDX) <- #sp_dec]
          else (IF (#opcode == $$(OP_PDISCOVER))
                then #regs_v@[#dst_idx <- #pt_probe_size]
          else (IF (#opcode == $$(OP_HEAP_LOAD))
                then #regs_v@[#dst_idx <- #heap_val]
          else (IF (#opcode == $$(OP_READ_PORT))
                then #regs_v@[#dst_idx <- $0]
          else (IF (#opcode == $$(OP_AND))
                then #regs_v@[#dst_idx <- #and_result]
          else (IF (#opcode == $$(OP_OR))
                then #regs_v@[#dst_idx <- #or_result]
          else (IF (#opcode == $$(OP_SHL))
                then #regs_v@[#dst_idx <- #shl_result]
          else (IF (#opcode == $$(OP_SHR))
                then #regs_v@[#dst_idx <- #shr_result]
          else (IF (#opcode == $$(OP_MUL))
                then #regs_v@[#dst_idx <- #mul_result]
          else (IF (#opcode == $$(OP_LUI))
                then #regs_v@[#dst_idx <- #lui_result]
          else (IF (#opcode == $$(OP_TENSOR_GET))
                then #regs_v@[#dst_idx <- #tget_val]
          else #morph_result_regs)))))))))))))))))))));
        (* ============================================================
           Determine new memory
           *)
        LET new_mem : Vector (Bit WordSz) MemAddrSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #mem_v
          else (IF (#opcode == $$(OP_STORE))
          then write_mem #mem_addr_a #src_val #mem_v
          else (IF (#opcode == $$(OP_CALL))
                then write_mem #sp_addr #pc_plus_1 #mem_v
          else (IF (#opcode == $$(OP_HEAP_STORE))
                then write_mem #heap_addr_a #src_val #mem_v
          else #mem_v)));

        (* Determine halted state *)
        LET new_halted <-
          #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || (#opcode == $$(OP_HALT));

        (* Determine error state: protocol violations set err. *)
        LET new_err <-
          #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation ||
          #rich_fault || #morph_runtime_fault ||
          ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad) ||
          #lassert_unsat_trap || #chsh_lassert_trap;

        (* Determine error code *)
        LET new_error_code : Bit WordSz <-
          IF #bianchi_violation
          then $$(ERR_BIANCHI_VAL)
          else (IF #locality_violation
                then $$(ERR_LOCALITY_VAL)
                else (IF #ptable_overflow_violation
                      then $$(ERR_PARTITION_VAL)
                      else (IF #nfi_violation
                            then $$(ERR_LOGIC_VAL)
                            else (IF #rich_fault
                                  then #rich_fault_error_code
                            else (IF #morph_runtime_fault
                                  then #morph_runtime_error_code
                            else (IF #high_value_locked
                                  then $$(ERR_LOGIC_VAL)
                                  else (IF ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad)
                                        then $$(ERR_CHSH_VAL)
                                        else (IF #lassert_unsat_trap
                                              then $$(ERR_LOGIC_VAL)
                                              else (IF #chsh_lassert_trap
                                                    then $$(ERR_CHSH_VAL)
                                                    else #error_code_v)))))))));

        (* Determine new mu — only charge if not a bianchi violation. *)
        LET rich_fault_mu : Bit WordSz <-
          IF (#opcode == $$(OP_CERTIFY))
          then #mu_v + #cost32 + $1
          else (IF (#opcode == $$(OP_MORPH_ASSERT))
                then #mu_v + #cost32 + $1
                else (IF (#opcode == $$(OP_CHSH_LASSERT))
                      then #mu_v + #cost32 + $1
                else (IF (#opcode == $$(OP_LASSERT))
                      then #new_mu + $1
                      else (IF ((#opcode == $$(OP_EMIT)) ||
                                (#opcode == $$(OP_REVEAL)) ||
                                (#opcode == $$(OP_READ_PORT)))
                            then #bit_priced_mu
                            else (IF (#opcode == $$(OP_LJOIN))
                                  then #new_mu + $1
                                  else #new_mu)))));
        LET normal_step_mu : Bit WordSz <-
          IF ((#opcode == $$(OP_CHSH_TRIAL)) && (#is_x1_trial))
                then #new_mu + $$(CHSH_X1_SURCHARGE)
                else (IF (#opcode == $$(OP_CERTIFY))
                      then #mu_v + #cost32 + $1
                      else (IF (#opcode == $$(OP_MORPH_ASSERT))
                            then #mu_v + #cost32 + $1
                            else (IF (#opcode == $$(OP_CHSH_LASSERT))
                                  then #mu_v + #cost32 + $1
                            else (IF (#opcode == $$(OP_LASSERT))
                                  then (IF #lassert_is_sat then #mu_v else #new_mu + $1)
                                  else (IF ((#opcode == $$(OP_EMIT)) ||
                                            (#opcode == $$(OP_REVEAL)) ||
                                            (#opcode == $$(OP_READ_PORT)))
                                        then #bit_priced_mu
                                        else (IF (#opcode == $$(OP_LJOIN))
                                              then #new_mu + $1
                                              else #new_mu))))));
        LET final_mu : Bit WordSz <-
          IF (#bianchi_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #mu_v
          else (IF #rich_fault then #rich_fault_mu else #normal_step_mu);

        (* ============================================================
           CERTIFY flag update — set by CERTIFY opcode only
           *)
        LET new_certified : Bool <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #certified_v
          else (IF (#opcode == $$(OP_CERTIFY))
                then $$true
                else #certified_v);

        (* ============================================================
           Partition table updates (PNEW / PSPLIT / PMERGE)
           Matches handwritten RTL module_table / region_table semantics.
           pt_sizes[id] = region_size (0 = unallocated).
           pt_next_id grows monotonically.
           *)

        (* Truncate pt_next_id to PTableIdxSz bits for vector indexing *)
        LET pt_slot : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #pt_next_id_v;

        (* PNEW encoding carries start in op_a and length in op_b.
           The partition wall stores the local range [0, length). *)
        LET pnew_region_size : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;
        LET pt_after_pnew : Vector (Bit WordSz) PTableIdxSz <-
          #pt_sizes_v@[#pt_slot <- #pnew_region_size];
        LET next_after_pnew : Bit PTableNextIdSz <- #pt_next_id_v + $1;

        (* PSPLIT: split module op_a into two children at next two free slots.
           Left child gets old_size >> 1, right child gets the remainder.
           Original slot is zeroed (deallocated). *)
        LET psplit_id : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #op_a;
        LET psplit_orig_sz : Bit WordSz <- #pt_sizes_v@[#psplit_id];
        LET psplit_left_sz : Bit WordSz <-
          BinBit (Srl _ _) #psplit_orig_sz ($$(WO~0~0~0~0~1));
        LET psplit_right_sz : Bit WordSz <- #psplit_orig_sz - #psplit_left_sz;
        LET psplit_slot1 : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #pt_next_id_v;
        LET psplit_slot2 : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) (#pt_next_id_v + $1);
        LET pt_after_psplit : Vector (Bit WordSz) PTableIdxSz <-
          ((#pt_sizes_v@[#psplit_id <- $0])@[#psplit_slot1 <- #psplit_left_sz])
            @[#psplit_slot2 <- #psplit_right_sz];
        LET next_after_psplit : Bit PTableNextIdSz <- #pt_next_id_v + $2;

        (* PMERGE: merge modules op_a and op_b.
           Both source slots are zeroed; merged size allocated at pt_next_id. *)
        LET pmerge_m1 : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #op_a;
        LET pmerge_m2 : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #op_b;
        LET pmerge_m1_sz : Bit WordSz <- #pt_sizes_v@[#pmerge_m1];
        LET pmerge_m2_sz : Bit WordSz <- #pt_sizes_v@[#pmerge_m2];
        LET pmerge_merged_sz : Bit WordSz <- #pmerge_m1_sz + #pmerge_m2_sz;
        LET pmerge_slot : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #pt_next_id_v;
        LET pt_after_pmerge : Vector (Bit WordSz) PTableIdxSz <-
          ((#pt_sizes_v@[#pmerge_m1 <- $0])@[#pmerge_m2 <- $0])
            @[#pmerge_slot <- #pmerge_merged_sz];
        LET next_after_pmerge : Bit PTableNextIdSz <- #pt_next_id_v + $1;

        (* Select partition table update based on opcode *)
        LET new_pt_sizes : Vector (Bit WordSz) PTableIdxSz <-
          IF (#bianchi_violation || #ptable_overflow_violation || #rich_fault || #morph_runtime_fault)
          then #pt_sizes_v
          else (IF (#opcode == $$(OP_PNEW))
                then #pt_after_pnew
                else (IF (#opcode == $$(OP_PSPLIT))
                      then #pt_after_psplit
                      else (IF (#opcode == $$(OP_PMERGE))
                            then #pt_after_pmerge
                            else #pt_sizes_v)));

        LET new_pt_next_id : Bit PTableNextIdSz <-
          IF (#bianchi_violation || #ptable_overflow_violation || #rich_fault || #morph_runtime_fault)
          then #pt_next_id_v
          else (IF (#opcode == $$(OP_PNEW))
                then #next_after_pnew
                else (IF (#opcode == $$(OP_PSPLIT))
                      then #next_after_psplit
                      else (IF (#opcode == $$(OP_PMERGE))
                            then #next_after_pmerge
                            else #pt_next_id_v)));

        (* ============================================================
           Counter updates
           *)
        LET is_partition_op <-
          (#opcode == $$(OP_PNEW)) || (#opcode == $$(OP_PSPLIT)) || (#opcode == $$(OP_PMERGE));
        LET new_partition_ops : Bit WordSz <-
          IF (#is_partition_op && !#bianchi_violation && !#rich_fault && !#morph_runtime_fault)
          then #partition_ops_v + $1
          else #partition_ops_v;

        LET new_mdl_ops : Bit WordSz <-
          IF ((#opcode == $$(OP_MDLACC)) && !#bianchi_violation && !#rich_fault && !#morph_runtime_fault)
          then #mdl_ops_v + $1
          else #mdl_ops_v;

        (* info_gain increments only when No-Free-Insight bound is satisfied. *)
        LET new_info_gain : Bit WordSz <-
          IF (#is_info_gain_op && !#bianchi_violation && !#locality_violation &&
              !#ptable_overflow_violation && !#high_value_locked && !#nfi_violation &&
              !#rich_fault && !#morph_runtime_fault)
          then #info_gain_v + #op_b_32
          else #info_gain_v;

        (* ============================================================
           Witness counter updates (CHSH_TRIAL increments the right bucket)
           *)
        LET new_wc_same_00 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_00 && #chsh_outcomes_same)
          then #wc_same_00_v + $1 else #wc_same_00_v;
        LET new_wc_diff_00 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_00 && !#chsh_outcomes_same)
          then #wc_diff_00_v + $1 else #wc_diff_00_v;
        LET new_wc_same_01 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_01 && #chsh_outcomes_same)
          then #wc_same_01_v + $1 else #wc_same_01_v;
        LET new_wc_diff_01 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_01 && !#chsh_outcomes_same)
          then #wc_diff_01_v + $1 else #wc_diff_01_v;
        LET new_wc_same_10 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_10 && #chsh_outcomes_same)
          then #wc_same_10_v + $1 else #wc_same_10_v;
        LET new_wc_diff_10 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_10 && !#chsh_outcomes_same)
          then #wc_diff_10_v + $1 else #wc_diff_10_v;
        LET new_wc_same_11 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_11 && #chsh_outcomes_same)
          then #wc_same_11_v + $1 else #wc_same_11_v;
        LET new_wc_diff_11 : Bit WordSz <-
          IF (#is_chsh_valid && #is_bucket_11 && !#chsh_outcomes_same)
          then #wc_diff_11_v + $1 else #wc_diff_11_v;

        (* ============================================================
           μ-tensor update (REVEAL charges tensor entry,
                            TENSOR_SET writes register value to entry)
           *)
        LET new_mu_tensor : Vector (Bit WordSz) MuTensorIdxSz <-
          IF ((#opcode == $$(OP_REVEAL)) && !#bianchi_violation && !#high_value_locked && !#rich_fault && !#morph_runtime_fault)
          then #mu_tensor_v@[#tensor_idx <- #tensor_new_val]
          else #mu_tensor_v;

        LET new_module_tensors : Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz <-
          IF ((#opcode == $$(OP_TENSOR_SET)) &&
              !(#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
                #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault))
          then #module_tensors_v@[#tset_mod <- #tset_row@[#tset_idx <- #op_b_32]]
          else #module_tensors_v;

        LET new_morph_src_table : Vector (Bit PTableIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_src_table_v
          else (IF #morph_allocates
                then #morph_src_table_v@[#morph_slot <- #morph_alloc_src]
                else #morph_src_table_v);
        LET new_morph_dst_table : Vector (Bit PTableIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_dst_table_v
          else (IF #morph_allocates
                then #morph_dst_table_v@[#morph_slot <- #morph_alloc_dst]
                else #morph_dst_table_v);
        LET new_morph_coupling_desc_table : Vector (Bit DescIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_coupling_desc_table_v
          else (IF #morph_allocates
                then #morph_coupling_desc_table_v@[#morph_slot <- #morph_alloc_coupling]
                else #morph_coupling_desc_table_v);
        LET new_morph_identity_table : Vector Bool MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_identity_table_v
          else (IF #morph_allocates
                then #morph_identity_table_v@[#morph_slot <- #morph_alloc_identity]
                else #morph_identity_table_v);
        LET new_morph_valid_table : Vector Bool MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_valid_table_v
          else (IF #morph_allocates
                then #morph_valid_table_v@[#morph_slot <- $$true]
                else (IF #morph_delete_success
                      then #morph_valid_table_v@[#morph_delete_idx <- $$false]
                      else #morph_valid_table_v));
        LET new_morph_next_id : Bit MorphTableNextIdSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_next_id_v
          else (IF #morph_allocates then #morph_next_id_v + $1 else #morph_next_id_v);

        LET new_logic_acc : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation || #rich_fault || #morph_runtime_fault)
          then #logic_acc_v
          else (IF (#opcode == $$(OP_LASSERT))
                then #logic_acc_v ~+ $$(LOGIC_GATE_KEY)
                else #logic_acc_v);
        LET new_cert_addr : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #cert_addr_v
          else (IF #is_morph_assert_ext && #morph_assert_success
                then #ext_assert_property_checksum
                else (IF #is_morph_assert_legacy && #morph_assert_success
                      then $0  (* legacy path: no inline checksum in 32-bit word *)
                      else #cert_addr_v));


        (* CSR telemetry: cycle and retired instruction counters. *)
        LET mcycle_lo_next : Bit WordSz <- #mcycle_lo_v + $1;
        LET mcycle_lo_wrap <- #mcycle_lo_next == $0;
        LET mcycle_hi_next : Bit WordSz <- IF #mcycle_lo_wrap then #mcycle_hi_v + $1 else #mcycle_hi_v;

        LET retire_this_step <-
          !#locality_violation && !#ptable_overflow_violation && !#high_value_locked &&
          !#nfi_violation && !#rich_fault && !#morph_runtime_fault;
        LET minstret_lo_inc : Bit WordSz <- IF #retire_this_step then #minstret_lo_v + $1 else #minstret_lo_v;
        LET minstret_lo_wrap <- #retire_this_step && (#minstret_lo_inc == $0);
        LET minstret_hi_next : Bit WordSz <- IF #minstret_lo_wrap then #minstret_hi_v + $1 else #minstret_hi_v;

        LET new_mstatus : Bit WordSz <-
          IF #logic_key_ok then $$(MSTATUS_THIELE) else $$(MSTATUS_TURING);

        (* Write back *)
        Write "pc"             <- #new_pc;
        Write "mu"             <- #final_mu;
        Write "regs"           <- #new_regs;
        Write "mem"            <- #new_mem;
        Write "halted"         <- #new_halted;
        Write "err"            <- #new_err;
        Write "error_code"     <- #new_error_code;
        Write "logic_acc"      <- #new_logic_acc;
        Write "cert_addr"      <- #new_cert_addr;
        Write "mstatus"        <- #new_mstatus;
        Write "mcycle_lo"      <- #mcycle_lo_next;
        Write "mcycle_hi"      <- #mcycle_hi_next;
        Write "minstret_lo"    <- #minstret_lo_inc;
        Write "minstret_hi"    <- #minstret_hi_next;
        Write "partition_ops"  <- #new_partition_ops;
        Write "mdl_ops"        <- #new_mdl_ops;
        Write "info_gain"      <- #new_info_gain;
        Write "mu_tensor"      <- #new_mu_tensor;
        Write "module_tensors" <- #new_module_tensors;
        Write "ptTable"        <- #new_pt_sizes;
        Write "pt_next_id"     <- #new_pt_next_id;
        Write "morph_src_table" <- #new_morph_src_table;
        Write "morph_dst_table" <- #new_morph_dst_table;
        Write "morph_coupling_desc_table" <- #new_morph_coupling_desc_table;
        Write "morph_identity_table" <- #new_morph_identity_table;
        Write "morph_valid_table" <- #new_morph_valid_table;
        Write "morph_next_id"  <- #new_morph_next_id;
        Write "certified"      <- #new_certified;
        Write "wc_same_00"     <- #new_wc_same_00;
        Write "wc_diff_00"     <- #new_wc_diff_00;
        Write "wc_same_01"     <- #new_wc_same_01;
        Write "wc_diff_01"     <- #new_wc_diff_01;
        Write "wc_same_10"     <- #new_wc_same_10;
        Write "wc_diff_10"     <- #new_wc_diff_10;
        Write "wc_same_11"     <- #new_wc_same_11;
        Write "wc_diff_11"     <- #new_wc_diff_11;

        (* ============================================================
           LASSERT FSM dispatch — initialize on-chip SAT checker state.
           When opcode == OP_LASSERT and kind=SAT: enter phase 1.
           lassert_cptr repurposed as cost field for FSM commit.
           freg base = dst_val (regs[op_a[4:0]]), creg base = src_val.
           *)
        (* Rejected dispatch cannot start a background assertion engine:
           later FSM commits must not overwrite the rejection's PC/error. *)
        LET assertion_dispatch_allowed <-
          !(#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
            #high_value_locked || #nfi_violation || #rich_fault || #morph_runtime_fault);
        LET lassert_zero : Bit WordSz <- $$(natToWord WordSz 0);
        Write "lassert_phase"      <- IF (#is_lassert && #lassert_is_sat && #assertion_dispatch_allowed) then $$(WO~0~0~1) else $$(WO~0~0~0);
        Write "lassert_kind"       <- IF (#is_lassert && #assertion_dispatch_allowed) then #lassert_is_sat else $$false;
        Write "lassert_fbase"      <- IF (#is_lassert && #lassert_is_sat && #assertion_dispatch_allowed) then #dst_val else #lassert_zero;
        Write "lassert_cbase"      <- IF (#is_lassert && #lassert_is_sat && #assertion_dispatch_allowed) then #src_val else #lassert_zero;
        Write "lassert_cptr"       <- IF (#is_lassert && #lassert_is_sat && #assertion_dispatch_allowed) then #cost32 else #lassert_zero;
        Write "lassert_fptr"       <- #lassert_zero;
        Write "lassert_flen"       <- #lassert_zero;
        Write "lassert_clen"       <- #lassert_zero;
        Write "lassert_nvars"      <- #lassert_zero;
        Write "lassert_clause_sat" <- $$false;
        Write "lassert_counter_clause_sat" <- $$false;
        Write "lassert_counter_seen_fail" <- $$false;

        (* CHSH_LASSERT FSM dispatch:
           When the step rule sees instr_chsh_lassert (opcode == OP_CHSH_LASSERT),
           latch the witness counters into the FSM-owned registers and set
           chsh_phase = 1. The FSM rule then runs 22 cycles of one-multiply-
           per-cycle arithmetic and on phase 23 commits the result (overriding
           PC/err/error_code on trap). When the step rule sees any other
           opcode, chsh_phase is held at 0 — the latches still update (cheap
           additions over the witness counters, no DSPs) but the FSM stays
           idle. *)
        Write "chsh_phase"  <- IF (#is_chsh_lassert && #assertion_dispatch_allowed) then $$(WO~0~0~0~0~1) else $$(WO~0~0~0~0~0);
        Write "chsh_n00"    <- #ll_n00;
        Write "chsh_n01"    <- #ll_n01;
        Write "chsh_n10"    <- #ll_n10;
        Write "chsh_n11"    <- #ll_n11;
        Write "chsh_d00"    <- #ll_abs_d00;
        Write "chsh_d01"    <- #ll_abs_d01;
        Write "chsh_d10"    <- #ll_abs_d10;
        Write "chsh_d11"    <- #ll_abs_d11;
        Write "chsh_sign00" <- #ll_sign00;
        Write "chsh_sign01" <- #ll_sign01;
        Write "chsh_sign10" <- #ll_sign10;
        Write "chsh_sign11" <- #ll_sign11;

        (* ============================================================
           Morphism-coupling FSM (M5) dispatch. pc/mu/registers/morph
           tables have already committed above, same cycle, exactly as
           before this feature existed; morph_coupling_desc_table already
           points the new morphism at coupling_desc_next_id_v (see
           morph_alloc_coupling above). What's left is to actually
           populate that descriptor's base/count and the underlying pair
           table, which this FSM does in the background over the next
           few cycles while mc_phase is nonzero, mirroring the LASSERT
           and CHSH_LASSERT FSMs' own Assert-guard pattern above. *)
        LET mc_zero_pidx : Bit CouplingPairIdxSz <- $0;
        LET mc_zero_cnt : Bit CouplingPairCountSz <- $0;
        LET mc_zero_word : Bit WordSz <- $0;
        Write "mc_phase"      <- IF (#bianchi_violation || #locality_violation ||
          #ptable_overflow_violation || #high_value_locked || #nfi_violation ||
          #rich_fault || #morph_runtime_fault) then $0 else #mc_new_phase;
        Write "mc_mem_base"   <- IF #morph_alloc_success
                                  then UniBit (ZeroExtendTrunc MemAddrSz WordSz) #ext_coupling_base
                                  else #mc_zero_word;
        Write "mc_write_base" <- #mc_write_base_d;
        Write "mc_write_ptr"  <- #coupling_pair_next_id_v;
        Write "mc_src1_base"  <- #mc_src1_base_d;
        Write "mc_src1_count" <- #mc_src1_count_d;
        Write "mc_src2_base"  <- #mc_src2_base_d;
        Write "mc_src2_count" <- #mc_src2_count_d;
        Write "mc_i"          <- #mc_zero_cnt;
        Write "mc_j"          <- #mc_zero_cnt;
        Write "mc_pair_count" <- #mc_zero_cnt;
        Write "mc_read_ptr"   <- #mc_zero_word;
        Retv)%kami_action.
Lemma dispatch_fetch_factoring_exact :
  nth_error (getRules thieleCore) 0 =
  Some {| attrName := "step"; attrType := dispatch_before_fetch_factoring |}.
Proof. reflexivity. Qed.
Print Assumptions dispatch_fetch_factoring_exact.
