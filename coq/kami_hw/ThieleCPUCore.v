(** ThieleCPUCore.v — Complete Thiele CPU in Kami (47-opcode synth-realised ISA).

    Implements the full ISA from VMStep.v:
      - Every instruction uses the μ cost table from VMStep.v
      - PC advances to PC+1 (sequential) or target (branch)
      - HALT latches the halted flag
      - CERTIFY sets the certified flag and charges S(cost) mu (structurally positive)

    ISA v2 transport is 128 bits wide. Decode in this phase still reads the
    legacy low lane:
      [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost

    Encoding conventions:
      XFER:      op_a = dst, op_b = src
      LOAD_IMM:  op_a = dst, op_b = immediate value
      LOAD:      op_a = dst, op_b = src register (address from register value)
      STORE:     op_a = addr register, op_b = src register
      ADD/SUB:   op_a = dst, op_b[7:4] = rs1, op_b[3:0] = rs2
      AND/OR/SHL/SHR/MUL: same as ADD/SUB encoding
      LUI:       op_a = dst, op_b = immediate (shifted left by 8)
      JUMP:      {op_a, op_b} = 16-bit target address
      JNEZ:      op_a = register to test, op_b = target address
      CALL:      {op_a, op_b} = 16-bit target address; r31 = SP
      RET:       no operands; r31 = SP
      XOR_LOAD:  op_a = dst, op_b = memory address
      XOR_ADD:   op_a = dst, op_b = src (dst ^= src)
      XOR_SWAP:  op_a = reg a, op_b = reg b
      XOR_RANK:  op_a = dst, op_b = src (popcount)
      CHSH_TRIAL: op_a[1:0] = setting (x,y), op_b[1:0] = outcome (a,b)
      REVEAL:    op_a[3:0] = tensor flat index (0-15), cost = charge amount
      PNEW/PSPLIT/PMERGE/PDISCOVER/LASSERT/LJOIN/MDLACC/EMIT:
        charge μ through the same cost policy as VMStep.v.
      CHECKPOINT: advances PC; label managed externally (NOP in hardware)
      READ_PORT:  op_a = dst; writes port value (hardware always provides 0)
      WRITE_PORT: op_a = channel, op_b = src; NOP in hardware (no I/O bus)
      HEAP_LOAD:  op_a = dst, op_b = addr register (address from register value)
      HEAP_STORE: op_a = addr register, op_b = src register
      CERTIFY:    no operands; cost = delta_mu; actual charge = S(cost) = cost+1


    Kami Vector notes: Vector K n stores 2^n elements, indexed by Bit n.
    So "regs" is Vector (Bit 32) 4 = 2^4 = 16 registers, indexed by Bit 4 (RegIdxSz).
    And "mem" is Vector (Bit 32) 7 = 2^7 = 128 memory words, indexed by Bit 7 (MemAddrSz).
    And "imem" is Vector (Bit InstrSz) 7 = 2^7 = 128 instruction words.
    And "mu_tensor" is Vector (Bit 32) 4 = 2^4 = 16 tensor entries.

    LASSERT/LJOIN ON-CHIP MODEL:
    Formula and certificate strings are stored in VM data memory (vm_mem).
    Registers freg/creg hold base addresses; the on-chip FSM reads them
    directly via mem_to_string. No external coprocessor; no stall cycle.
    LASSERT charges flen*8 + S(cost), matching VMStep.v. SAT mode requires
    both a satisfying model and a falsifying countermodel, so tautologies do
    not become free certificate events.
    See LogicEngineEquivalence.v for the equivalence proof. *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import ThieleTypes.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ThieleCPU.

  Definition LoadInstrPort :=
    STRUCT {
      "addr" :: Bit MemAddrSz ;
      "data" :: Bit InstrSz
    }.

  Definition APBBusWritePort :=
    STRUCT {
      "addr" :: Bit WordSz ;
      "data" :: Bit InstrSz
    }.

  Definition COUPLING_DESC_NEXT_ID_INIT : word DescTableNextIdSz :=
    WO~0~0~0~0~1.

  (** Stack pointer register index (r31) *)
  Definition SP_IDX : word RegIdxSz := WO~1~1~1~1.   (* RegIdxSz=4, SP=15 *)

  (** Physical locality helper: address must stay within active partition size. *)
  Definition check_bounds
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (active_partition_size : Expr ty (SyntaxKind (Bit WordSz)))
    : Expr ty (SyntaxKind Bool) :=
    BinBitBool (Lt WordSz) (UniBit (ZeroExtendTrunc _ _) addr) active_partition_size.


  (** Direct vector read: memv[addr].
      Uses Kami's native ReadIndex which BSC compiles to a simple array index. *)
  Definition read_mem
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Bit WordSz)) :=
    ReadIndex addr memv.

  (** Direct vector write: memv[addr] <- val.
      Uses Kami's native UpdateVector which BSC compiles to a simple array update. *)
  Definition write_mem
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (val : Expr ty (SyntaxKind (Bit WordSz)))
             (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)) :=
    UpdateVector memv addr val.

  (** Pure factoring of the actual dispatch action after its one instruction
      fetch. The decoded action receives the fetched word, never imem. *)
  Definition dispatch_decoded {ty : Kind -> Type}
    (chsh_check_result_v : ty (Bool))
    (pc_v : ty (Bit WordSz))
    (mu_v : ty (Bit WordSz))
    (regs_v : ty (Vector (Bit WordSz) RegIdxSz))
    (mem_v : ty (Vector (Bit WordSz) MemAddrSz))
    (partition_ops_v : ty (Bit WordSz))
    (mdl_ops_v : ty (Bit WordSz))
    (info_gain_v : ty (Bit WordSz))
    (error_code_v : ty (Bit WordSz))
    (logic_acc_v : ty (Bit WordSz))
    (cert_addr_v : ty (Bit WordSz))
    (active_module_v : ty (Bit PTableIdxSz))
    (mcycle_lo_v : ty (Bit WordSz))
    (mcycle_hi_v : ty (Bit WordSz))
    (minstret_lo_v : ty (Bit WordSz))
    (minstret_hi_v : ty (Bit WordSz))
    (trap_vector_v : ty (Bit WordSz))
    (mu_tensor_v : ty (Vector (Bit WordSz) MuTensorIdxSz))
    (module_tensors_v : ty (Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz))
    (csr_heap_base_v : ty (Bit WordSz))
    (pt_sizes_v : ty (Vector (Bit WordSz) PTableIdxSz))
    (pt_next_id_v : ty (Bit PTableNextIdSz))
    (certified_v : ty (Bool))
    (morph_src_table_v : ty (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_dst_table_v : ty (Vector (Bit PTableIdxSz) MorphTableIdxSz))
    (morph_valid_table_v : ty (Vector Bool MorphTableIdxSz))
    (morph_coupling_desc_table_v : ty (Vector (Bit DescIdxSz) MorphTableIdxSz))
    (morph_identity_table_v : ty (Vector Bool MorphTableIdxSz))
    (morph_next_id_v : ty (Bit MorphTableNextIdSz))
    (coupling_desc_valid_table_v : ty (Vector Bool CouplingDescIdxSz))
    (coupling_desc_count_table_v : ty (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz))
    (coupling_desc_base_table_v : ty (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz))
    (coupling_desc_label_table_v : ty (Vector (Bit WordSz) CouplingDescIdxSz))
    (coupling_desc_label_len_table_v : ty (Vector (Bit 6) CouplingDescIdxSz))
    (coupling_desc_next_id_v : ty (Bit DescTableNextIdSz))
    (coupling_pair_next_id_v : ty (Bit DescTableNextIdSz))
    (formula_desc_valid_table_v : ty (Vector Bool FormulaDescIdxSz))
    (formula_desc_next_id_v : ty (Bit DescTableNextIdSz))
    (cert_desc_valid_table_v : ty (Vector Bool CertDescIdxSz))
    (cert_desc_next_id_v : ty (Bit DescTableNextIdSz))
    (desc_meta_valid_table_v : ty (Vector Bool DescMetaIdxSz))
    (desc_meta_next_id_v : ty (Bit DescTableNextIdSz))
    (wc_same_00_v : ty (Bit WordSz))
    (wc_diff_00_v : ty (Bit WordSz))
    (wc_same_01_v : ty (Bit WordSz))
    (wc_diff_01_v : ty (Bit WordSz))
    (wc_same_10_v : ty (Bit WordSz))
    (wc_diff_10_v : ty (Bit WordSz))
    (wc_same_11_v : ty (Bit WordSz))
    (wc_diff_11_v : ty (Bit WordSz))
    (tensor_total : ty (Bit WordSz))
    (instr_v : ty (Bit InstrSz))
    (bianchi_violation : ty (Bool))
    : ActionT ty Void :=
    (
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
          (#opcode == $$(OP_MORPH_ID));
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
        LET lassert_header_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#regs_v@[UniBit (Trunc RegIdxSz _) #op_a]);
        LET lassert_header_x8 : Bit WordSz <-
          BinBit (Sll _ _) (#mem_v@[#lassert_header_addr]) ($$(WO~0~0~0~0~1~1));
        LET lassert_unsat_mu : Bit WordSz <- #mu_v + #lassert_header_x8 + #cost32 + $1;
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


        (* Capacity guards: never wrap partition table indices. *)
        LET ptable_full <- #pt_next_id_v >= $64;
        LET ptable_room_one <- !#ptable_full;
        LET ptable_room_two <- (#pt_next_id_v + $2) <= $64;
        LET pnew_overflow <- (#opcode == $$(OP_PNEW)) && !#ptable_room_one;
        LET psplit_overflow <- (#opcode == $$(OP_PSPLIT)) && !#ptable_room_two;
        LET pmerge_overflow <- (#opcode == $$(OP_PMERGE)) && !#ptable_room_one;
        LET ptable_overflow_violation <- #pnew_overflow || #psplit_overflow || #pmerge_overflow;

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
           are documented per opcode below. MORPH_TENSOR always faults. *)
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
        (* MORPH_TENSOR never succeeds: module regions are the prefixes
           [0, size), so no two regions are disjoint and the kernel's tensor
           product always reports a missing morphism. *)
        LET morph_tensor_fault <- #is_morph_tensor;
        LET morph_runtime_fault <-
          #morph_ext_endpoint_fault || #morph_legacy_endpoint_fault ||
          #compose_lookup_fault || #compose_type_fault ||
          #morph_delete_fault || #morph_get_fault || #morph_get_coupling_fault ||
          #morph_assert_fault || #morph_tensor_fault;
        LET morph_runtime_error_code : Bit WordSz <-
          IF (#compose_type_fault)
          then $$(ERR_COMPOSE_TYPE)
          else (IF (#compose_lookup_fault || #morph_delete_fault || #morph_get_fault ||
                    #morph_assert_fault || #morph_tensor_fault)
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
          #compose_success || #legacy_compose_success;

        (* Allocation fields: select src/dst/coupling/identity for the new morph slot. *)
        LET morph_alloc_src : Bit PTableIdxSz <-
          IF #morph_alloc_success then #morph_src_mod_idx
          else (IF #legacy_morph_alloc_success then #morph_src_mod_idx  (* self: src=op_b module *)
          else (IF (#morph_id_success || #morph_id_legacy_success) then #morph_identity_mod_idx
          else (IF #compose_success then #compose_m1_src
          else (IF #legacy_compose_success then #compose_m1_src
          else #morph_identity_mod_idx))));
        LET morph_alloc_dst : Bit PTableIdxSz <-
          IF #morph_alloc_success then #ext_morph_dst_mod
          else (IF #legacy_morph_alloc_success then #morph_src_mod_idx  (* self: dst=op_b module *)
          else (IF (#morph_id_success || #morph_id_legacy_success) then #morph_identity_mod_idx
          else (IF #compose_success then #compose_m2_dst
          else (IF #legacy_compose_success then #legacy_compose_m2_dst
          else #morph_identity_mod_idx))));
        (* Morphism-coupling FSM (M5) dispatch: MORPH and COMPOSE each
           allocate a fresh descriptor for their coupling
           data rather than writing $0 (empty) unconditionally. The
           descriptor id is known immediately, coupling_desc_next_id_v,
           before the FSM runs; the FSM's own job is to populate that
           descriptor's base/count/pairs and advance the two next-id
           counters, in the background, while pc/mu/registers/morph tables
           already commit this same cycle exactly as before. *)
        LET mc_enters_fsm <-
          #morph_alloc_success || #compose_success || #legacy_compose_success;
        LET morph_alloc_coupling : Bit DescIdxSz <-
          IF #mc_enters_fsm
          then UniBit (Trunc DescIdxSz _) #coupling_desc_next_id_v
          else $0;
        LET morph_alloc_identity <- #morph_id_success || #morph_id_legacy_success;

        (* Morphism-coupling FSM (M5): which existing descriptors COMPOSE
           reads from. m1 always comes from morph_lookup_idx; m2 comes from
           ext_compose_m2 (extended COMPOSE) or morph_zero_idx (legacy
           COMPOSE, m2 is always slot 0). Identity morphisms always carry empty
           coupling by construction (MORPH_ID always allocates coupling_desc
           0), so COMPOSE's identity shortcut is realized by zeroing that
           side's pair count rather than by a separate code path: the shared
           copy loop then naturally copies only the non-identity side. *)
        LET mc_compose_active <- #compose_success || #legacy_compose_success;
        LET mc_m1_id : Bit MorphTableIdxSz <- #morph_lookup_idx;
        LET mc_m2_id : Bit MorphTableIdxSz <-
          IF #is_compose_ext then #ext_compose_m2 else #morph_zero_idx;

        LET mc_compose_is_id1 <- #morph_identity_table_v@[#mc_m1_id];
        LET mc_compose_is_id2 <- #morph_identity_table_v@[#mc_m2_id];
        LET mc_needs_join <-
          #mc_compose_active && !#mc_compose_is_id1 && !#mc_compose_is_id2;
        LET mc_needs_copy <-
          #mc_compose_active && (#mc_compose_is_id1 || #mc_compose_is_id2);

        LET mc_src1_desc : Bit DescIdxSz <- #morph_coupling_desc_table_v@[#mc_m1_id];
        LET mc_src2_desc : Bit DescIdxSz <- #morph_coupling_desc_table_v@[#mc_m2_id];

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

        (* Labels of the source descriptors as atom lists: a count of atoms
           and a mask whose bit k marks atom k as "empty". A descriptor that is
           not valid has the kernel's single "empty" label. A composed label
           joins the two lists with ";". *)
        LET mc_label1_valid <- #coupling_desc_valid_table_v@[#mc_src1_desc];
        LET mc_label2_valid <- #coupling_desc_valid_table_v@[#mc_src2_desc];
        LET mc_len1 : Bit 6 <-
          IF #mc_label1_valid then #coupling_desc_label_len_table_v@[#mc_src1_desc] else $1;
        LET mc_len2 : Bit 6 <-
          IF #mc_label2_valid then #coupling_desc_label_len_table_v@[#mc_src2_desc] else $1;
        LET mc_mask1 : Bit WordSz <-
          IF #mc_label1_valid then #coupling_desc_label_table_v@[#mc_src1_desc] else $1;
        LET mc_mask2 : Bit WordSz <-
          IF #mc_label2_valid then #coupling_desc_label_table_v@[#mc_src2_desc] else $1;
        LET mc_new_len : Bit 6 <-
          IF #mc_compose_active then (#mc_len1 + #mc_len2) else $1;
        LET mc_new_label : Bit WordSz <-
          IF #mc_compose_active then (#mc_mask1 + BinBit (Sll WordSz 6) #mc_mask2 #mc_len1) else $0;

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
        LET is_chsh_valid <- (#opcode == $$(OP_CHSH_TRIAL)) &&
          !#bianchi_violation && !#locality_violation && !#ptable_overflow_violation &&
          !#nfi_violation && !#rich_fault;

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
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #nfi_violation || #rich_fault)
          then #trap_vector_v
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
                                                    else #pc_plus_1))))));

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
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #nfi_violation || #rich_fault || #morph_runtime_fault)
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
          else #morph_result_regs))))))))))))))))))));
        (* ============================================================
           Determine new memory
           *)
        LET new_mem : Vector (Bit WordSz) MemAddrSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #nfi_violation || #rich_fault || #morph_runtime_fault)
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
          #locality_violation || #ptable_overflow_violation || #nfi_violation || (#opcode == $$(OP_HALT));

        (* Determine error state: protocol violations set err. *)
        LET new_err <-
          #locality_violation || #ptable_overflow_violation || #nfi_violation ||
          #rich_fault || #morph_runtime_fault ||
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
                            else (IF #lassert_unsat_trap
                                  then $$(ERR_LOGIC_VAL)
                                  else (IF #chsh_lassert_trap
                                        then $$(ERR_CHSH_VAL)
                                        else #error_code_v)))))));

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
          IF (#opcode == $$(OP_CERTIFY))
          then #mu_v + #cost32 + $1
          else (IF (#opcode == $$(OP_MORPH_ASSERT))
                then #mu_v + #cost32 + $1
                else (IF (#opcode == $$(OP_CHSH_LASSERT))
                      then #mu_v + #cost32 + $1
                else (IF (#opcode == $$(OP_LASSERT))
                      then (IF #lassert_is_sat then #mu_v else #lassert_unsat_mu)
                      else (IF ((#opcode == $$(OP_EMIT)) ||
                                (#opcode == $$(OP_REVEAL)) ||
                                (#opcode == $$(OP_READ_PORT)))
                            then #bit_priced_mu
                            else (IF (#opcode == $$(OP_LJOIN))
                                  then #new_mu + $1
                                  else #new_mu)))));
        LET final_mu : Bit WordSz <-
          IF (#bianchi_violation || #ptable_overflow_violation || #nfi_violation)
          then #mu_v
          else (IF #rich_fault then #rich_fault_mu else #normal_step_mu);

        (* ============================================================
           CERTIFY flag update — set by CERTIFY opcode only
           *)
        LET new_certified : Bool <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #nfi_violation || #rich_fault || #morph_runtime_fault)
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
              !#ptable_overflow_violation && !#nfi_violation &&
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
          IF ((#opcode == $$(OP_REVEAL)) && !#bianchi_violation && !#rich_fault && !#morph_runtime_fault)
          then #mu_tensor_v@[#tensor_idx <- #tensor_new_val]
          else #mu_tensor_v;

        LET new_module_tensors : Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz <-
          IF ((#opcode == $$(OP_TENSOR_SET)) &&
              !(#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
                #nfi_violation || #rich_fault || #morph_runtime_fault))
          then #module_tensors_v@[#tset_mod <- #tset_row@[#tset_idx <- #op_b_32]]
          else #module_tensors_v;

        LET new_morph_src_table : Vector (Bit PTableIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_src_table_v
          else (IF #morph_allocates
                then #morph_src_table_v@[#morph_slot <- #morph_alloc_src]
                else #morph_src_table_v);
        LET new_morph_dst_table : Vector (Bit PTableIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_dst_table_v
          else (IF #morph_allocates
                then #morph_dst_table_v@[#morph_slot <- #morph_alloc_dst]
                else #morph_dst_table_v);
        LET new_morph_coupling_desc_table : Vector (Bit DescIdxSz) MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_coupling_desc_table_v
          else (IF #morph_allocates
                then #morph_coupling_desc_table_v@[#morph_slot <- #morph_alloc_coupling]
                else #morph_coupling_desc_table_v);
        LET new_morph_identity_table : Vector Bool MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_identity_table_v
          else (IF #morph_allocates
                then #morph_identity_table_v@[#morph_slot <- #morph_alloc_identity]
                else #morph_identity_table_v);
        LET new_morph_valid_table : Vector Bool MorphTableIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_valid_table_v
          else (IF #morph_allocates
                then #morph_valid_table_v@[#morph_slot <- $$true]
                else (IF #morph_delete_success
                      then #morph_valid_table_v@[#morph_delete_idx <- $$false]
                      else #morph_valid_table_v));
        LET new_morph_next_id : Bit MorphTableNextIdSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
          then #morph_next_id_v
          else (IF #morph_allocates then #morph_next_id_v + $1 else #morph_next_id_v);

        LET new_cert_addr : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation ||
              #nfi_violation || #rich_fault || #morph_runtime_fault)
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
          !#locality_violation && !#ptable_overflow_violation &&
          !#nfi_violation && !#rich_fault && !#morph_runtime_fault;
        LET minstret_lo_inc : Bit WordSz <- IF #retire_this_step then #minstret_lo_v + $1 else #minstret_lo_v;
        LET minstret_lo_wrap <- #retire_this_step && (#minstret_lo_inc == $0);
        LET minstret_hi_next : Bit WordSz <- IF #minstret_lo_wrap then #minstret_hi_v + $1 else #minstret_hi_v;


        (* Write back *)
        Write "pc"             <- #new_pc;
        Write "mu"             <- #final_mu;
        Write "regs"           <- #new_regs;
        Write "mem"            <- #new_mem;
        Write "halted"         <- #new_halted;
        Write "err"            <- #new_err;
        Write "error_code"     <- #new_error_code;
        Write "cert_addr"      <- #new_cert_addr;
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
            #nfi_violation || #rich_fault || #morph_runtime_fault);
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
          #ptable_overflow_violation || #nfi_violation ||
          #rich_fault || #morph_runtime_fault) then $0 else #mc_new_phase;
        Write "mc_mem_base"   <- IF #morph_alloc_success
                                  then UniBit (ZeroExtendTrunc MemAddrSz WordSz) #ext_coupling_base
                                  else #mc_zero_word;
        Write "mc_write_base" <- #mc_write_base_d;
        Write "coupling_desc_label_table" <-
          IF #mc_enters_fsm
          then #coupling_desc_label_table_v@[#morph_alloc_coupling <- #mc_new_label]
          else #coupling_desc_label_table_v;
        Write "coupling_desc_label_len_table" <-
          IF #mc_enters_fsm
          then #coupling_desc_label_len_table_v@[#morph_alloc_coupling <- #mc_new_len]
          else #coupling_desc_label_len_table_v;
        Write "mc_write_ptr"  <- #coupling_pair_next_id_v;
        Write "mc_src1_base"  <- #mc_src1_base_d;
        Write "mc_src1_count" <- #mc_src1_count_d;
        Write "mc_src2_base"  <- #mc_src2_base_d;
        Write "mc_src2_count" <- #mc_src2_count_d;
        Write "mc_i"          <- #mc_zero_cnt;
        Write "mc_j"          <- #mc_zero_cnt;
        Write "mc_pair_count" <- #mc_zero_cnt;
        Write "mc_read_ptr"   <- #mc_zero_word;
        Retv
    )%kami_action.

  (** Pure factoring of the CHSH_LASSERT FSM rule after its register reads.
      The rule reads every register first; Kami reads observe the pre-state,
      so reading pc, err, error_code and trap_vector before the scratch
      writes rather than after them does not change the rule. *)
  Definition chsh_fsm_decoded {ty : Kind -> Type}
    (chsh_phase_v : ty (Bit 5))
    (chsh_n00_v : ty (Bit 64))
    (chsh_n01_v : ty (Bit 64))
    (chsh_n10_v : ty (Bit 64))
    (chsh_n11_v : ty (Bit 64))
    (chsh_d00_v : ty (Bit 64))
    (chsh_d01_v : ty (Bit 64))
    (chsh_d10_v : ty (Bit 64))
    (chsh_d11_v : ty (Bit 64))
    (chsh_sign00_v : ty (Bool))
    (chsh_sign01_v : ty (Bool))
    (chsh_sign10_v : ty (Bool))
    (chsh_sign11_v : ty (Bool))
    (chsh_n00sq_v : ty (Bit 128))
    (chsh_n01sq_v : ty (Bit 128))
    (chsh_n10sq_v : ty (Bit 128))
    (chsh_n11sq_v : ty (Bit 128))
    (chsh_d00sq_v : ty (Bit 128))
    (chsh_d01sq_v : ty (Bit 128))
    (chsh_d10sq_v : ty (Bit 128))
    (chsh_d11sq_v : ty (Bit 128))
    (chsh_A_pos_v : ty (Bit 256))
    (chsh_A_neg_a_v : ty (Bit 256))
    (chsh_A_neg_b_v : ty (Bit 256))
    (chsh_B_pos_v : ty (Bit 256))
    (chsh_B_neg_a_v : ty (Bit 256))
    (chsh_B_neg_b_v : ty (Bit 256))
    (chsh_d00d01_v : ty (Bit 128))
    (chsh_n10n11_v : ty (Bit 128))
    (chsh_d10d11_v : ty (Bit 128))
    (chsh_n00n01_v : ty (Bit 128))
    (chsh_abs_C1_v : ty (Bit 256))
    (chsh_abs_C2_v : ty (Bit 256))
    (chsh_C_sq_v : ty (Bit 384))
    (chsh_A_times_B_v : ty (Bit 384))
    (chsh_check_result_v : ty (Bool))
    (pc_v_fsm : ty (Bit WordSz))
    (err_v_fsm : ty (Bool))
    (error_code_v_fsm : ty (Bit WordSz))
    (trap_vector_v_fsm : ty (Bit WordSz))
    : ActionT ty Void :=
    (
        (* Zero-extend smaller operands to 384 bits so one shared multiplier
           handles every phase. The shared multiplier is one BinBit Mul. *)
        LET n00_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_n00_v;
        LET n01_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_n01_v;
        LET n10_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_n10_v;
        LET n11_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_n11_v;
        LET d00_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_d00_v;
        LET d01_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_d01_v;
        LET d10_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_d10_v;
        LET d11_384 : Bit 384 <- UniBit (ZeroExtendTrunc 64  384) #chsh_d11_v;
        LET n00sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n00sq_v;
        LET n01sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n01sq_v;
        LET n10sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n10sq_v;
        LET n11sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n11sq_v;
        LET d00sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d00sq_v;
        LET d01sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d01sq_v;
        LET d10sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d10sq_v;
        LET d11sq_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d11sq_v;
        LET d00d01_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d00d01_v;
        LET n10n11_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n10n11_v;
        LET d10d11_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_d10d11_v;
        LET n00n01_384 : Bit 384 <- UniBit (ZeroExtendTrunc 128 384) #chsh_n00n01_v;

        (* For phase 21 (|C|²) we need abs_C derived from abs_C1, abs_C2 and
           the latched signs (signs are XOR of d-signs per term). *)
        LET signC1_v   <- #chsh_sign00_v != #chsh_sign01_v;
        LET signC2_v   <- #chsh_sign10_v != #chsh_sign11_v;
        LET signs_agree_v <- #signC1_v == #signC2_v;
        LET C_terms_sum   : Bit 256 <- #chsh_abs_C1_v + #chsh_abs_C2_v;
        LET C1_ge_C2_v <- #chsh_abs_C1_v >= #chsh_abs_C2_v;
        LET C_terms_diff  : Bit 256 <-
          IF #C1_ge_C2_v then (#chsh_abs_C1_v - #chsh_abs_C2_v)
          else (#chsh_abs_C2_v - #chsh_abs_C1_v);
        LET abs_C_256 : Bit 256 <-
          IF #signs_agree_v then #C_terms_sum else #C_terms_diff;
        LET abs_C_384 : Bit 384 <- UniBit (ZeroExtendTrunc 256 384) #abs_C_256;

        (* For phase 22 (A·B) we need abs_A, abs_B derived from A_pos/neg, B_pos/neg. *)
        LET A_neg_v   : Bit 256 <- #chsh_A_neg_a_v + #chsh_A_neg_b_v;
        LET A_ge0_v   <- #chsh_A_pos_v >= #A_neg_v;
        LET abs_A_256 : Bit 256 <-
          IF #A_ge0_v then (#chsh_A_pos_v - #A_neg_v) else (#A_neg_v - #chsh_A_pos_v);
        LET abs_A_384 : Bit 384 <- UniBit (ZeroExtendTrunc 256 384) #abs_A_256;
        LET B_neg_v   : Bit 256 <- #chsh_B_neg_a_v + #chsh_B_neg_b_v;
        LET B_ge0_v   <- #chsh_B_pos_v >= #B_neg_v;
        LET abs_B_256 : Bit 256 <-
          IF #B_ge0_v then (#chsh_B_pos_v - #B_neg_v) else (#B_neg_v - #chsh_B_pos_v);
        LET abs_B_384 : Bit 384 <- UniBit (ZeroExtendTrunc 256 384) #abs_B_256;

        (* Phase-muxed operands for the single shared multiplier. *)
        LET phase_eq_1  <- #chsh_phase_v == $$(WO~0~0~0~0~1);
        LET phase_eq_2  <- #chsh_phase_v == $$(WO~0~0~0~1~0);
        LET phase_eq_3  <- #chsh_phase_v == $$(WO~0~0~0~1~1);
        LET phase_eq_4  <- #chsh_phase_v == $$(WO~0~0~1~0~0);
        LET phase_eq_5  <- #chsh_phase_v == $$(WO~0~0~1~0~1);
        LET phase_eq_6  <- #chsh_phase_v == $$(WO~0~0~1~1~0);
        LET phase_eq_7  <- #chsh_phase_v == $$(WO~0~0~1~1~1);
        LET phase_eq_8  <- #chsh_phase_v == $$(WO~0~1~0~0~0);
        LET phase_eq_9  <- #chsh_phase_v == $$(WO~0~1~0~0~1);
        LET phase_eq_10 <- #chsh_phase_v == $$(WO~0~1~0~1~0);
        LET phase_eq_11 <- #chsh_phase_v == $$(WO~0~1~0~1~1);
        LET phase_eq_12 <- #chsh_phase_v == $$(WO~0~1~1~0~0);
        LET phase_eq_13 <- #chsh_phase_v == $$(WO~0~1~1~0~1);
        LET phase_eq_14 <- #chsh_phase_v == $$(WO~0~1~1~1~0);
        LET phase_eq_15 <- #chsh_phase_v == $$(WO~0~1~1~1~1);
        LET phase_eq_16 <- #chsh_phase_v == $$(WO~1~0~0~0~0);
        LET phase_eq_17 <- #chsh_phase_v == $$(WO~1~0~0~0~1);
        LET phase_eq_18 <- #chsh_phase_v == $$(WO~1~0~0~1~0);
        LET phase_eq_19 <- #chsh_phase_v == $$(WO~1~0~0~1~1);
        LET phase_eq_20 <- #chsh_phase_v == $$(WO~1~0~1~0~0);
        LET phase_eq_21 <- #chsh_phase_v == $$(WO~1~0~1~0~1);
        LET phase_eq_22 <- #chsh_phase_v == $$(WO~1~0~1~1~0);
        LET phase_eq_23 <- #chsh_phase_v == $$(WO~1~0~1~1~1);

        LET op_a_384 : Bit 384 <-
          IF #phase_eq_1  then #n00_384
          else IF #phase_eq_2  then #n01_384
          else IF #phase_eq_3  then #n10_384
          else IF #phase_eq_4  then #n11_384
          else IF #phase_eq_5  then #d00_384
          else IF #phase_eq_6  then #d01_384
          else IF #phase_eq_7  then #d10_384
          else IF #phase_eq_8  then #d11_384
          else IF #phase_eq_9  then #n00sq_384
          else IF #phase_eq_10 then #d00sq_384
          else IF #phase_eq_11 then #d10sq_384
          else IF #phase_eq_12 then #n01sq_384
          else IF #phase_eq_13 then #d01sq_384
          else IF #phase_eq_14 then #d11sq_384
          else IF #phase_eq_15 then #d00_384
          else IF #phase_eq_16 then #n10_384
          else IF #phase_eq_17 then #d10_384
          else IF #phase_eq_18 then #n00_384
          else IF #phase_eq_19 then #d00d01_384
          else IF #phase_eq_20 then #d10d11_384
          else IF #phase_eq_21 then #abs_C_384
          else IF #phase_eq_22 then #abs_A_384
          else $0;

        LET op_b_384 : Bit 384 <-
          IF #phase_eq_1  then #n00_384
          else IF #phase_eq_2  then #n01_384
          else IF #phase_eq_3  then #n10_384
          else IF #phase_eq_4  then #n11_384
          else IF #phase_eq_5  then #d00_384
          else IF #phase_eq_6  then #d01_384
          else IF #phase_eq_7  then #d10_384
          else IF #phase_eq_8  then #d11_384
          else IF #phase_eq_9  then #n10sq_384
          else IF #phase_eq_10 then #n10sq_384
          else IF #phase_eq_11 then #n00sq_384
          else IF #phase_eq_12 then #n11sq_384
          else IF #phase_eq_13 then #n11sq_384
          else IF #phase_eq_14 then #n01sq_384
          else IF #phase_eq_15 then #d01_384
          else IF #phase_eq_16 then #n11_384
          else IF #phase_eq_17 then #d11_384
          else IF #phase_eq_18 then #n01_384
          else IF #phase_eq_19 then #n10n11_384
          else IF #phase_eq_20 then #n00n01_384
          else IF #phase_eq_21 then #abs_C_384
          else IF #phase_eq_22 then #abs_B_384
          else $0;

        (* THE single shared multiplier. yosys infers one mult instance. *)
        LET mult_result_768 : Bit 768 <-
          BinBit (Mul 768 SignUU)
            (UniBit (ZeroExtendTrunc 384 768) #op_a_384)
            (UniBit (ZeroExtendTrunc 384 768) #op_b_384);

        LET mult_128 : Bit 128 <- UniBit (Trunc 128 _) #mult_result_768;
        LET mult_256 : Bit 256 <- UniBit (Trunc 256 _) #mult_result_768;
        LET mult_384 : Bit 384 <- UniBit (Trunc 384 _) #mult_result_768;

        (* Final boolean for phase 23. *)
        LET all_n_pos <- (#chsh_n00_v != $0) && (#chsh_n01_v != $0)
                         && (#chsh_n10_v != $0) && (#chsh_n11_v != $0);
        LET ab_ge_csq <- #chsh_C_sq_v <= #chsh_A_times_B_v;
        LET final_ok  <- #all_n_pos && #A_ge0_v && #B_ge0_v && #ab_ge_csq;

        (* Phase-demuxed writes to intermediate result registers. Each phase
           updates exactly one register; others keep their current value. *)
        Write "chsh_n00sq"   <- IF #phase_eq_1  then #mult_128 else #chsh_n00sq_v;
        Write "chsh_n01sq"   <- IF #phase_eq_2  then #mult_128 else #chsh_n01sq_v;
        Write "chsh_n10sq"   <- IF #phase_eq_3  then #mult_128 else #chsh_n10sq_v;
        Write "chsh_n11sq"   <- IF #phase_eq_4  then #mult_128 else #chsh_n11sq_v;
        Write "chsh_d00sq"   <- IF #phase_eq_5  then #mult_128 else #chsh_d00sq_v;
        Write "chsh_d01sq"   <- IF #phase_eq_6  then #mult_128 else #chsh_d01sq_v;
        Write "chsh_d10sq"   <- IF #phase_eq_7  then #mult_128 else #chsh_d10sq_v;
        Write "chsh_d11sq"   <- IF #phase_eq_8  then #mult_128 else #chsh_d11sq_v;
        Write "chsh_A_pos"   <- IF #phase_eq_9  then #mult_256 else #chsh_A_pos_v;
        Write "chsh_A_neg_a" <- IF #phase_eq_10 then #mult_256 else #chsh_A_neg_a_v;
        Write "chsh_A_neg_b" <- IF #phase_eq_11 then #mult_256 else #chsh_A_neg_b_v;
        Write "chsh_B_pos"   <- IF #phase_eq_12 then #mult_256 else #chsh_B_pos_v;
        Write "chsh_B_neg_a" <- IF #phase_eq_13 then #mult_256 else #chsh_B_neg_a_v;
        Write "chsh_B_neg_b" <- IF #phase_eq_14 then #mult_256 else #chsh_B_neg_b_v;
        Write "chsh_d00d01"  <- IF #phase_eq_15 then #mult_128 else #chsh_d00d01_v;
        Write "chsh_n10n11"  <- IF #phase_eq_16 then #mult_128 else #chsh_n10n11_v;
        Write "chsh_d10d11"  <- IF #phase_eq_17 then #mult_128 else #chsh_d10d11_v;
        Write "chsh_n00n01"  <- IF #phase_eq_18 then #mult_128 else #chsh_n00n01_v;
        Write "chsh_abs_C1"  <- IF #phase_eq_19 then #mult_256 else #chsh_abs_C1_v;
        Write "chsh_abs_C2"  <- IF #phase_eq_20 then #mult_256 else #chsh_abs_C2_v;
        Write "chsh_C_sq"    <- IF #phase_eq_21 then #mult_384 else #chsh_C_sq_v;
        Write "chsh_A_times_B" <- IF #phase_eq_22 then #mult_384 else #chsh_A_times_B_v;

        (* Phase 23: commit the final boolean. *)
        Write "chsh_check_result" <- IF #phase_eq_23 then #final_ok else #chsh_check_result_v;

        (* Phase 23: if the check failed, override PC / err / error_code to trap.
           If the check passed, leave those fields alone — the step rule already
           advanced PC by 1 and charged μ on the dispatch cycle (cert-setter
           discipline charges μ regardless of outcome). The trap-on-fail path
           mirrors what the original combinational chsh_lassert_trap branch
           did when it lived in the step rule. *)
        LET commit_trap <- #phase_eq_23 && !#final_ok;
        Write "pc"         <- IF #commit_trap then #trap_vector_v_fsm else #pc_v_fsm;
        Write "err"        <- IF #commit_trap then $$true            else #err_v_fsm;
        Write "error_code" <- IF #commit_trap then $$(ERR_LOGIC_VAL) else #error_code_v_fsm;

        (* Advance phase, wrap to 0 after phase 23. *)
        Write "chsh_phase" <-
          IF #phase_eq_23 then $$(WO~0~0~0~0~0)
          else (#chsh_phase_v + $$(WO~0~0~0~0~1));
        Retv
    )%kami_action.

  Definition thieleCore :=
    MODULE {
      (* Core registers matching VMState *)
      Register "pc"     : Bit WordSz <- Default
      with Register "mu"     : Bit WordSz <- Default
      with Register "err"    : Bool <- false
      with Register "halted" : Bool <- false
      with Register "regs"  : Vector (Bit WordSz) RegIdxSz <- Default
      with Register "mem"   : Vector (Bit WordSz) MemAddrSz <- Default
      with Register "imem"   : Vector (Bit InstrSz) MemAddrSz <- Default (* 2^MemAddrSz=128 instrs *)

      (* Diagnostic counters — needed for test parity with handwritten RTL *)
      with Register "partition_ops" : Bit WordSz <- Default
      with Register "mdl_ops"       : Bit WordSz <- Default
      with Register "info_gain"     : Bit WordSz <- Default

      (* Error code register — specific error condition identifier *)
      with Register "error_code"    : Bit WordSz <- Default

      (* In-core logic engine accumulator: deterministic certificate/logic state. *)
      with Register "logic_acc"     : Bit WordSz <- Default
      (* Hardware-visible certificate-address witness for cert-setting rich ops. *)
      with Register "cert_addr"     : Bit WordSz <- Default

      (* Active module and CSR telemetry (RISC-V style management plane). *)
      with Register "active_module" : Bit PTableIdxSz <- ACTIVE_MODULE_INIT
      with Register "mstatus"       : Bit WordSz <- MSTATUS_THIELE
      with Register "mcycle_lo"     : Bit WordSz <- Default
      with Register "mcycle_hi"     : Bit WordSz <- Default
      with Register "minstret_lo"   : Bit WordSz <- Default
      with Register "minstret_hi"   : Bit WordSz <- Default
      with Register "trap_vector"   : Bit WordSz <- TRAP_VEC_INIT

      (* Certification flag — set by the CERTIFY opcode (state-based certification). *)
      with Register "certified" : Bool <- false

      (* On-chip LASSERT FSM state — replaces external coprocessor interface.
         phase=0: idle; phase>0: multi-cycle formula/cert read in progress.
         fbase/cbase: base addresses of formula/cert in vm_mem.
         flen/clen/nvars: formula length, remaining clauses, variable count.
         fptr/cptr: current read pointers during FSM traversal.
         kind: true = SAT check, false = UNSAT check.
         fbuf/cbuf: bounded backing buffers that M3 exposes architecturally and
         later rich-state paths can target directly. *)
      with Register "lassert_phase" : Bit 3 <- Default
      with Register "lassert_kind"  : Bool <- false
      with Register "lassert_fbase" : Bit WordSz <- Default
      with Register "lassert_cbase" : Bit WordSz <- Default
      with Register "lassert_flen"  : Bit WordSz <- Default
      with Register "lassert_clen"  : Bit WordSz <- Default
      with Register "lassert_nvars" : Bit WordSz <- Default
      with Register "lassert_fptr"  : Bit WordSz <- Default
      with Register "lassert_cptr"  : Bit WordSz <- Default
      (* fbuf/cbuf reduced to 2^6 = 64 backing words from early Arty A7 fit;
         kept on Kintex-7 K325T target for test/cosim parity *)
      with Register "lassert_fbuf"  : Vector (Bit WordSz) 6 <- Default
      with Register "lassert_cbuf"  : Vector (Bit WordSz) 6 <- Default
      (* Scratch flag: has any literal in the current clause been satisfied? *)
      with Register "lassert_clause_sat" : Bool <- false
      with Register "lassert_counter_clause_sat" : Bool <- false
      with Register "lassert_counter_seen_fail" : Bool <- false

      (* CHSH_LASSERT multi-cycle FSM registers.
         The witness check (column-contractive) needs ~22 wide integer
         multiplications. Doing them combinationally inside the step rule
         maps to ~1131 DSP48E1 slices, which (a) overflows K325T's 840 DSP
         budget and (b) takes openXC7's nextpnr-xilinx placer >2h. We
         restructure the check as a 22-cycle FSM that shares ONE 384x384
         multiplier across all phases, with the operand mux indexed by
         `chsh_phase`. Total DSP cost drops to ~64.

         chsh_phase encoding (Bit 5 = 32 values, use 0..23):
           0  : idle (step rule may fire)
           1  : compute n00² (witness already latched in step rule dispatch)
           2  : compute n01²
           3  : n10²
           4  : n11²
           5  : d00²        — chsh_d_xy values are pre-computed absolute diffs
           6  : d01²
           7  : d10²
           8  : d11²
           9  : A_pos     = n00²·n10²
           10 : A_neg_a   = d00²·n10²
           11 : A_neg_b   = d10²·n00²
           12 : B_pos     = n01²·n11²
           13 : B_neg_a   = d01²·n11²
           14 : B_neg_b   = d11²·n01²
           15 : d00d01    = d00·d01    (128-bit helper for C)
           16 : n10n11    = n10·n11
           17 : d10d11    = d10·d11
           18 : n00n01    = n00·n01
           19 : abs_C1    = d00d01·n10n11
           20 : abs_C2    = d10d11·n00n01
           21 : C_sq      = |C|²
           22 : A_times_B = A·B
           23 : commit (final compare + PC/mu/err writes)

         While chsh_phase > 0 the main step rule is inhibited (Assert
         chsh_phase == 0), same pattern as the LASSERT FSM. *)
      with Register "chsh_phase"   : Bit 5  <- Default
      (* Latched witness counters at dispatch (single source of truth for FSM) *)
      with Register "chsh_n00"     : Bit 64 <- Default
      with Register "chsh_n01"     : Bit 64 <- Default
      with Register "chsh_n10"     : Bit 64 <- Default
      with Register "chsh_n11"     : Bit 64 <- Default
      with Register "chsh_d00"     : Bit 64 <- Default  (* |d_xy|, sign in chsh_sign_xy *)
      with Register "chsh_d01"     : Bit 64 <- Default
      with Register "chsh_d10"     : Bit 64 <- Default
      with Register "chsh_d11"     : Bit 64 <- Default
      with Register "chsh_sign00"  : Bool   <- false
      with Register "chsh_sign01"  : Bool   <- false
      with Register "chsh_sign10"  : Bool   <- false
      with Register "chsh_sign11"  : Bool   <- false
      (* Phase 1..8 outputs: 8 squarings at 128 bits each *)
      with Register "chsh_n00sq"   : Bit 128 <- Default
      with Register "chsh_n01sq"   : Bit 128 <- Default
      with Register "chsh_n10sq"   : Bit 128 <- Default
      with Register "chsh_n11sq"   : Bit 128 <- Default
      with Register "chsh_d00sq"   : Bit 128 <- Default
      with Register "chsh_d01sq"   : Bit 128 <- Default
      with Register "chsh_d10sq"   : Bit 128 <- Default
      with Register "chsh_d11sq"   : Bit 128 <- Default
      (* Phase 9..14 outputs: A and B sub-products at 256 bits each *)
      with Register "chsh_A_pos"   : Bit 256 <- Default
      with Register "chsh_A_neg_a" : Bit 256 <- Default
      with Register "chsh_A_neg_b" : Bit 256 <- Default
      with Register "chsh_B_pos"   : Bit 256 <- Default
      with Register "chsh_B_neg_a" : Bit 256 <- Default
      with Register "chsh_B_neg_b" : Bit 256 <- Default
      (* Phase 15..18 outputs: 4 narrow C-helper products at 128 bits each *)
      with Register "chsh_d00d01"  : Bit 128 <- Default
      with Register "chsh_n10n11"  : Bit 128 <- Default
      with Register "chsh_d10d11"  : Bit 128 <- Default
      with Register "chsh_n00n01"  : Bit 128 <- Default
      (* Phase 19..20 outputs: 2 wide C-term magnitudes at 256 bits each *)
      with Register "chsh_abs_C1"  : Bit 256 <- Default
      with Register "chsh_abs_C2"  : Bit 256 <- Default
      (* Phase 21..22 outputs: final 384-bit products for the comparison *)
      with Register "chsh_C_sq"      : Bit 384 <- Default
      with Register "chsh_A_times_B" : Bit 384 <- Default
      (* Phase 23 output: final boolean result (true = check passed). Step rule
         reads this after FSM completes to decide trap vs advance. *)
      with Register "chsh_check_result" : Bool <- false

      with Register "bus_load_instr_addr" : Bit MemAddrSz <- Default
      with Register "bus_load_instr_data" : Bit InstrSz <- Default
      with Register "bus_load_instr_kick" : Bool <- false

      (* μ-tensor: 4×4 flattened (16 entries) for revelation direction tracking *)
      with Register "mu_tensor"     : Vector (Bit WordSz) MuTensorIdxSz <- Default

      (* Per-module 4x4 metric tensors: 16 module slots (the width of the
         tensor module field) with 16 flattened entries each. *)
      with Register "module_tensors" : Vector (Vector (Bit WordSz) MuTensorIdxSz) ModTensorIdxSz <- Default

      (* CSR status and heap base.  No instruction writes either register;
         HEAP_LOAD and HEAP_STORE address data memory relative to the heap base. *)
      with Register "csr_status"    : Bit WordSz <- Default
      with Register "csr_heap_base" : Bit WordSz <- Default

      (* Partition table — bounded to 64 slots by PTableIdxSz=6.
         pt_sizes[id] = region_size for that module slot (0 = unallocated/invalid).
         pt_next_id is the next free module ID to assign; initialized to 1 to match
         empty_graph.pg_next_id = 1 from VMState.v. *)
      with Register "ptTable"  : Vector (Bit WordSz) PTableIdxSz <- Default
      with Register "pt_next_id"    : Bit PTableNextIdSz <- PT_NEXT_ID_INIT

      (* Bounded rich-state tables (M3):
         - morph_* tables store per-morphism source/target/descriptor metadata
         - coupling_desc_* tables describe contiguous ranges in the pair table
         - coupling_pair_* tables store concrete source/target coupling pairs
         M4 will make the rich opcodes mutate these tables directly. *)
      with Register "morph_src_table" : Vector (Bit PTableIdxSz) MorphTableIdxSz <- Default
      with Register "morph_dst_table" : Vector (Bit PTableIdxSz) MorphTableIdxSz <- Default
      with Register "morph_coupling_desc_table" : Vector (Bit DescIdxSz) MorphTableIdxSz <- Default
      with Register "morph_valid_table" : Vector Bool MorphTableIdxSz <- Default
      with Register "morph_identity_table" : Vector Bool MorphTableIdxSz <- Default
      with Register "morph_next_id" : Bit MorphTableNextIdSz <- MORPH_NEXT_ID_INIT
      with Register "coupling_desc_base_table" : Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz <- Default
      with Register "coupling_desc_count_table" : Vector (Bit CouplingPairCountSz) CouplingDescIdxSz <- Default
      with Register "coupling_desc_valid_table" : Vector Bool CouplingDescIdxSz <- Default
      (* Label of each coupling descriptor as a list of atoms joined by ";":
         the length table counts the atoms and bit k of the mask marks atom k
         as the kernel's "empty" label, otherwise the empty string. MORPH
         commits one "" atom; COMPOSE appends the second list to the first. *)
      with Register "coupling_desc_label_table" : Vector (Bit WordSz) CouplingDescIdxSz <- Default
      with Register "coupling_desc_label_len_table" : Vector (Bit 6) CouplingDescIdxSz <- Default
      (* Descriptor zero is reserved for empty and identity couplings. *)
      with Register "coupling_desc_next_id" : Bit DescTableNextIdSz <- COUPLING_DESC_NEXT_ID_INIT
      with Register "coupling_pair_src_table" : Vector (Bit WordSz) CouplingPairIdxSz <- Default
      with Register "coupling_pair_dst_table" : Vector (Bit WordSz) CouplingPairIdxSz <- Default
      with Register "coupling_pair_valid_table" : Vector Bool CouplingPairIdxSz <- Default
      with Register "coupling_pair_next_id" : Bit DescTableNextIdSz <- DESC_NEXT_ID_INIT

      (* Morphism-coupling FSM (M5): real coupling data for MORPH (decoded from
         a serialized memory block), COMPOSE (relational composition of two
         existing morphisms' pairs). mc_phase=0: idle, main step rule dispatches.
         mc_phase>0: multi-cycle coupling computation in progress; main step
         rule is inhibited while the FSM runs. PC, mu, and the morphism table
         are updated at dispatch; coupling descriptors become valid at the
         terminal phase. Retirement observations must wait for that phase. mc_op selects which of the three shapes mc_phase
         walks through. *)
      with Register "mc_phase"     : Bit 4 <- Default
      with Register "mc_op"        : Bit 2 <- Default  (* 0=morph mem-decode, 1=compose, 2=tensor *)
      with Register "mc_mem_base"  : Bit WordSz <- Default
      with Register "mc_pair_count" : Bit CouplingPairCountSz <- Default
      with Register "mc_read_ptr"  : Bit WordSz <- Default
      with Register "mc_src1_base"  : Bit CouplingPairIdxSz <- Default
      with Register "mc_src1_count" : Bit CouplingPairCountSz <- Default
      with Register "mc_src2_base"  : Bit CouplingPairIdxSz <- Default
      with Register "mc_src2_count" : Bit CouplingPairCountSz <- Default
      with Register "mc_i"          : Bit CouplingPairCountSz <- Default
      with Register "mc_j"          : Bit CouplingPairCountSz <- Default
      with Register "mc_is_id1"     : Bool <- Default
      with Register "mc_is_id2"     : Bool <- Default
      with Register "mc_write_base" : Bit DescTableNextIdSz <- Default
      with Register "mc_write_ptr"  : Bit DescTableNextIdSz <- Default
      with Register "mc_norm_ptr" : Bit DescTableNextIdSz <- Default
      with Register "mc_duplicate" : Bool <- Default
      with Register "mc_dst_reg"      : Bit RegIdxSz <- Default
      with Register "mc_morph_slot"   : Bit MorphTableIdxSz <- Default
      with Register "mc_new_src_mod"  : Bit PTableIdxSz <- Default
      with Register "mc_new_dst_mod"  : Bit PTableIdxSz <- Default
      with Register "mc_cost"         : Bit WordSz <- Default
      with Register "formula_desc_base_table" : Vector (Bit WordSz) FormulaDescIdxSz <- Default
      with Register "formula_desc_count_table" : Vector (Bit WordSz) FormulaDescIdxSz <- Default
      with Register "formula_desc_valid_table" : Vector Bool FormulaDescIdxSz <- Default
      with Register "formula_desc_next_id" : Bit DescTableNextIdSz <- DESC_NEXT_ID_INIT
      with Register "cert_desc_base_table" : Vector (Bit WordSz) CertDescIdxSz <- Default
      with Register "cert_desc_count_table" : Vector (Bit WordSz) CertDescIdxSz <- Default
      with Register "cert_desc_valid_table" : Vector Bool CertDescIdxSz <- Default
      with Register "cert_desc_next_id" : Bit DescTableNextIdSz <- DESC_NEXT_ID_INIT
      with Register "desc_meta_subtype_table" : Vector (Bit FormatSubtypeSz) DescMetaIdxSz <- Default
      with Register "desc_meta_kind_table" : Vector (Bit DescKindFieldSz) DescMetaIdxSz <- Default
      with Register "desc_meta_inline_len_table" : Vector (Bit InlineLenSz) DescMetaIdxSz <- Default
      with Register "desc_meta_aux_table" : Vector (Bit WordSz) DescMetaIdxSz <- Default
      with Register "desc_meta_valid_table" : Vector Bool DescMetaIdxSz <- Default
      with Register "desc_meta_next_id" : Bit DescTableNextIdSz <- DESC_NEXT_ID_INIT

      (* Witness counters — 8-bucket CHSH trial recorder matching VMState.WitnessCounts.
        Each setting pair (x,y) has same/diff counters tracking whether
        outputs (a,b) matched. Updated by CHSH_TRIAL on valid bits. *)
      with Register "wc_same_00" : Bit WordSz <- Default
      with Register "wc_diff_00" : Bit WordSz <- Default
      with Register "wc_same_01" : Bit WordSz <- Default
      with Register "wc_diff_01" : Bit WordSz <- Default
      with Register "wc_same_10" : Bit WordSz <- Default
      with Register "wc_diff_10" : Bit WordSz <- Default
      with Register "wc_same_11" : Bit WordSz <- Default
      with Register "wc_diff_11" : Bit WordSz <- Default

      (** The single step rule: fetch-decode-execute in one atomic action.
          This matches the Coq vm_step relation which is also atomic. *)
      with Rule "step" :=
        Read halted_v : Bool <- "halted";
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
        dispatch_decoded chsh_check_result_v pc_v mu_v regs_v mem_v partition_ops_v mdl_ops_v info_gain_v error_code_v logic_acc_v cert_addr_v active_module_v mcycle_lo_v mcycle_hi_v minstret_lo_v minstret_hi_v trap_vector_v mu_tensor_v module_tensors_v csr_heap_base_v pt_sizes_v pt_next_id_v certified_v morph_src_table_v morph_dst_table_v morph_valid_table_v morph_coupling_desc_table_v morph_identity_table_v morph_next_id_v coupling_desc_valid_table_v coupling_desc_count_table_v coupling_desc_base_table_v coupling_desc_label_table_v coupling_desc_label_len_table_v coupling_desc_next_id_v coupling_pair_next_id_v formula_desc_valid_table_v formula_desc_next_id_v cert_desc_valid_table_v cert_desc_next_id_v desc_meta_valid_table_v desc_meta_next_id_v wc_same_00_v wc_diff_00_v wc_same_01_v wc_diff_01_v wc_same_10_v wc_diff_10_v wc_same_11_v wc_diff_11_v tensor_total instr_v bianchi_violation


      (** LASSERT FSM: multi-cycle on-chip SAT witness checker.

          Fires only when lassert_phase > 0 (step rule is inhibited by its
          own Assert (#lassert_phase_v == $0) guard).

          Binary memory layout (established by software before LASSERT):
            mem[fbase + 0] : flen (count of literal words following header)
            mem[fbase + 1] : num_vars
            mem[fbase + 2] : num_clauses
            mem[fbase + 3..3+flen-1] : literal words, 0 = end-of-clause
            mem[cbase + k] : satisfying assignment for variable k
            mem[cbase + num_vars + k] : falsifying assignment for variable k

          Phases:
            1 — Read header: latch flen and num_clauses, set fptr to fbase+3.
            2 — Scan literals one per cycle:
                  nonzero literal → check both assignments
                  zero (0)        → end of clause:
                    if model failed any clause → FAIL
                    if final countermodel never falsified a clause → FAIL
                    if last clause → SUCCESS (PC+1, charge flen*8+S(cost))
                    otherwise      → decrement clause counter, reset clause_sat, advance fptr

          lassert_cptr register is repurposed at dispatch to hold the cost field.
          The backing buffers are now architecturally exposed for the rich-state
          path even though this FSM still streams directly from memory today. *)
      with Rule "lassert_fsm_header" :=
        Read lassert_phase_v : Bit 3 <- "lassert_phase";
        Assert (#lassert_phase_v == $$(WO~0~0~1));

        Read mem_v         : Vector (Bit WordSz) MemAddrSz <- "mem";
        Read lassert_fbase_v     : Bit WordSz <- "lassert_fbase";

        (* Read formula header. *)
        LET fbase_a0 : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #lassert_fbase_v;
        LET fbase_a1 : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#lassert_fbase_v + $1);
        LET fbase_a2 : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#lassert_fbase_v + $2);
        LET hdr_flen     : Bit WordSz <- read_mem #fbase_a0 #mem_v;
        LET hdr_nvars    : Bit WordSz <- read_mem #fbase_a1 #mem_v;
        LET hdr_nclauses : Bit WordSz <- read_mem #fbase_a2 #mem_v;

        Write "lassert_phase"      <- $$(WO~0~1~0);
        Write "lassert_flen"       <- #hdr_flen;
        Write "lassert_clen"       <- #hdr_nclauses;
        Write "lassert_nvars"      <- #hdr_nvars;
        Write "lassert_fptr"       <- #lassert_fbase_v + $3;
        Write "lassert_clause_sat" <- $$false;
        Write "lassert_counter_clause_sat" <- $$false;
        Write "lassert_counter_seen_fail" <- $$false;
        Retv

      with Rule "lassert_fsm_scan" :=
        Read lassert_phase_v : Bit 3 <- "lassert_phase";
        Assert (#lassert_phase_v == $$(WO~0~1~0));

        Read mem_v         : Vector (Bit WordSz) MemAddrSz <- "mem";
        Read mu_v          : Bit WordSz <- "mu";
        Read pc_v          : Bit WordSz <- "pc";
        Read trap_vector_v : Bit WordSz <- "trap_vector";
        Read err_v         : Bool <- "err";
        Read error_code_v  : Bit WordSz <- "error_code";

        Read lassert_cbase_v     : Bit WordSz <- "lassert_cbase";
        Read lassert_flen_v      : Bit WordSz <- "lassert_flen";
        Read lassert_clen_v      : Bit WordSz <- "lassert_clen";
        Read lassert_nvars_v     : Bit WordSz <- "lassert_nvars";
        Read lassert_fptr_v      : Bit WordSz <- "lassert_fptr";
        Read lassert_cptr_v      : Bit WordSz <- "lassert_cptr";
        Read lassert_clause_sat_v : Bool <- "lassert_clause_sat";
        Read lassert_counter_clause_sat_v : Bool <- "lassert_counter_clause_sat";
        Read lassert_counter_seen_fail_v : Bool <- "lassert_counter_seen_fail";

        (* Current literal from formula *)
        LET fptr_a : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #lassert_fptr_v;
        LET literal : Bit WordSz <- read_mem #fptr_a #mem_v;

        (* Literal analysis: sign bit = bit 31, absolute value via 2's complement *)
        LET lit_sign   : Bit 1 <- UniBit (ConstExtract 31 1 0) #literal;
        LET lit_is_zero <- #literal == $0;
        LET lit_is_neg  <- (#lit_sign == $$(WO~1)) && !#lit_is_zero;
        LET lit_abs : Bit WordSz <- IF #lit_is_neg then ($0 - #literal) else #literal;

        (* Assignment lookup:
           model[k] lives at cbase+k.
           countermodel[k] lives at cbase+nvars+k. *)
        LET caddr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) (#lassert_cbase_v + #lit_abs);
        LET counter_caddr : Bit MemAddrSz <-
          UniBit (Trunc MemAddrSz _) (#lassert_cbase_v + #lassert_nvars_v + #lit_abs);
        LET asgn_word : Bit WordSz <- read_mem #caddr #mem_v;
        LET counter_asgn_word : Bit WordSz <- read_mem #counter_caddr #mem_v;
        LET asgn_t <- #asgn_word != $0;
        LET counter_asgn_t <- #counter_asgn_word != $0;
        LET lit_sat <- !#lit_is_zero && (IF #lit_is_neg then !#asgn_t else #asgn_t);
        LET counter_lit_sat <- !#lit_is_zero &&
          (IF #lit_is_neg then !#counter_asgn_t else #counter_asgn_t);

        (* End-of-clause logic (phase 2 only) *)
        LET end_of_clause <- #lit_is_zero;
        LET last_clause   <- #lassert_clen_v <= $1;
        LET model_clause_fail <- #end_of_clause && !#lassert_clause_sat_v;
        LET counter_clause_fail <- #end_of_clause && !#lassert_counter_clause_sat_v;
        LET counter_seen_fail_next <- #lassert_counter_seen_fail_v || #counter_clause_fail;
        LET final_counter_fail <- #end_of_clause && #lassert_clause_sat_v &&
          #last_clause && !#counter_seen_fail_next;
        LET clause_fail   <- #model_clause_fail || #final_counter_fail;
        LET all_done      <- #end_of_clause && #lassert_clause_sat_v &&
          #last_clause && #counter_seen_fail_next;
        LET clause_ok_cont <- #end_of_clause && #lassert_clause_sat_v && !#last_clause;

        (* μ at commit: success and failure both pay flen*8 + S(cost).
           You pay for the measurement even when the witness fails. *)
        LET cost_v   : Bit WordSz <- #lassert_cptr_v;
        LET flen_x8  : Bit WordSz <- BinBit (Sll _ _) #lassert_flen_v ($$(WO~0~0~0~0~1~1));
        LET mu_success : Bit WordSz <- #mu_v + #flen_x8 + #cost_v + $1;
        LET mu_fail    : Bit WordSz <- #mu_v + #flen_x8 + #cost_v + $1;

        (* Next FSM state *)
        LET next_phase : Bit 3 <-
          IF (#all_done || #clause_fail) then $$(WO~0~0~0)
          else $$(WO~0~1~0);

        LET next_clen : Bit WordSz <-
          IF #clause_ok_cont then (#lassert_clen_v - $1)
          else #lassert_clen_v;

        LET next_fptr : Bit WordSz <-
          #lassert_fptr_v + $1;

        LET next_clause_sat <-
          IF #end_of_clause then $$false
          else (IF #lit_sat then $$true
                else #lassert_clause_sat_v);

        LET next_counter_clause_sat <-
          IF #end_of_clause then $$false
          else (IF #counter_lit_sat then $$true
                else #lassert_counter_clause_sat_v);

        LET next_counter_seen_fail <-
          #counter_seen_fail_next;

        (* PC/mu commit — only fire on terminal transitions *)
        LET new_pc : Bit WordSz <-
          IF #all_done then (#pc_v + $1)
          else (IF #clause_fail then #trap_vector_v
                else #pc_v);

        LET new_mu : Bit WordSz <-
          IF #all_done then #mu_success
          else (IF #clause_fail then #mu_fail
                else #mu_v);

        LET new_err <-
          IF #clause_fail then $$true else #err_v;

        LET new_error_code_fsm : Bit WordSz <-
          IF #clause_fail then $$(ERR_LOGIC_VAL) else #error_code_v;

        Write "lassert_phase"      <- #next_phase;
        Write "lassert_clen"       <- #next_clen;
        Write "lassert_fptr"       <- #next_fptr;
        Write "lassert_clause_sat" <- #next_clause_sat;
        Write "lassert_counter_clause_sat" <- #next_counter_clause_sat;
        Write "lassert_counter_seen_fail" <- #next_counter_seen_fail;
        Write "pc"                 <- #new_pc;
        Write "mu"                 <- #new_mu;
        Write "err"                <- #new_err;
        Write "error_code"         <- #new_error_code_fsm;
        Retv

      (** Morphism-coupling FSM (M5): real coupling data for MORPH (decoded
          from a serialized memory block), COMPOSE (relational composition
          of two existing morphisms' pairs). Dispatched by the step rule
          above (mc_phase, mc_mem_base, mc_write_base/ptr, mc_src1/2_base/
          count already latched there); pc/mu/registers/morph tables have
          already committed. This FSM's only job is to populate the
          coupling_pair_* and coupling_desc_* tables for the descriptor id
          the morph table already points at, then release mc_phase back to
          0 so the step rule can fire again.

          Two differences from the software spec
          (ThieleMachineComplete.load_coupling_from_mem): no region-
          restriction filter (hardware's ptTable tracks only a region size
          per module, not actual cell membership, so there is no hardware
          representation to filter pairs against), and no label decoding
          from memory. MORPH admits only in-region pairs and the empty label;
          the label length and mask tables, written by the step rule, record
          composed labels as atom lists.

          Phase encoding (Bit 4):
            0     : idle (step rule fires)
            1     : MORPH header: validate pair count, space, and memory extent
            2     : MORPH loop — read one (source,target) pair per cycle
            4     : COPY loop — concatenate two existing pair ranges
                    (COMPOSE when either source is a
                    flagged identity morphism, which always carries empty
                    coupling by construction, so this reduces to copying
                    just the non-identity side)
            7     : JOIN loop — relational composition of two existing pair
                    ranges (COMPOSE when neither source is identity)
            5     : initialize last-occurrence normalization
            8,9   : scan suffix and compact each retained pair
            11    : shared commit — allocate the descriptor, advance the
                    two next-id counters, phase back to 0 *)
      with Rule "mc_morph_header" :=
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $$(WO~0~0~0~1));

        Read mem_v         : Vector (Bit WordSz) MemAddrSz <- "mem";
        Read mc_mem_base_v : Bit WordSz <- "mc_mem_base";
        Read coupling_pair_next_id_v : Bit DescTableNextIdSz <- "coupling_pair_next_id";

        LET mc_base_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz 25) #mc_mem_base_v;
        LET mc_raw_count : Bit WordSz <- read_mem #mc_base_addr #mem_v;
        LET mc_room : Bit WordSz <-
          UniBit (ZeroExtendTrunc DescTableNextIdSz WordSz)
            ($$(natToWord DescTableNextIdSz 16) - #coupling_pair_next_id_v);
        Read mc_err_v : Bool <- "err";
        Read mc_error_v : Bit WordSz <- "error_code";
        LET mc_fits <- (#mc_raw_count <= #mc_room) &&
          (#mc_raw_count <= (BinBit (Srl WordSz WordSz) ($127 - #mc_mem_base_v) $1));
        LET mc_empty <- #mc_raw_count == $0;

        Write "err" <- #mc_err_v || !#mc_fits;
        Write "error_code" <- IF #mc_fits then #mc_error_v else $$(ERR_COUPLING_INVALID);
        Write "mc_pair_count" <- UniBit (Trunc CouplingPairCountSz 27) #mc_raw_count;
        Write "mc_read_ptr"   <- #mc_mem_base_v + $1;
        Write "mc_i"          <- $$(natToWord CouplingPairCountSz 0);
        Write "mc_phase" <- IF !#mc_fits then $$(natToWord 4 0)
          else (IF #mc_empty then $$(WO~0~1~0~1) else $$(WO~0~0~1~0));
        Retv

      with Rule "mc_morph_loop" :=
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $$(WO~0~0~1~0));

        Read mem_v            : Vector (Bit WordSz) MemAddrSz <- "mem";
        Read mc_read_ptr_v    : Bit WordSz <- "mc_read_ptr";
        Read mc_write_ptr_v   : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read mc_i_v           : Bit CouplingPairCountSz <- "mc_i";
        Read mc_pair_count_v  : Bit CouplingPairCountSz <- "mc_pair_count";
        Read coupling_pair_src_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Read coupling_pair_dst_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        Read coupling_pair_valid_table_v : Vector Bool CouplingPairIdxSz <- "coupling_pair_valid_table";

        LET mc_src_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz 25) #mc_read_ptr_v;
        LET mc_dst_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz 25) (#mc_read_ptr_v + $1);
        LET mc_pair_src : Bit WordSz <- read_mem #mc_src_addr #mem_v;
        LET mc_pair_dst : Bit WordSz <- read_mem #mc_dst_addr #mem_v;

        LET mc_i_next : Bit CouplingPairCountSz <- #mc_i_v + $1;
        LET mc_last : Bool <- (#mc_i_next == #mc_pair_count_v);

        Write "coupling_pair_src_table" <- #coupling_pair_src_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_pair_src];
        Write "coupling_pair_dst_table" <- #coupling_pair_dst_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_pair_dst];
        Write "coupling_pair_valid_table" <- #coupling_pair_valid_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- $$true];
        Write "mc_read_ptr"  <- #mc_read_ptr_v + $2;
        Write "mc_write_ptr" <- #mc_write_ptr_v + $1;
        Write "mc_i"         <- #mc_i_next;
        Write "mc_phase"     <- IF #mc_last then $$(WO~0~1~0~1) else $$(WO~0~0~1~0);
        Retv

      with Rule "mc_copy_loop" :=
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $$(WO~0~1~0~0));

        Read mc_i_v          : Bit CouplingPairCountSz <- "mc_i";
        Read mc_j_v          : Bit CouplingPairCountSz <- "mc_j";
        Read mc_src1_base_v  : Bit CouplingPairIdxSz <- "mc_src1_base";
        Read mc_src1_count_v : Bit CouplingPairCountSz <- "mc_src1_count";
        Read mc_src2_base_v  : Bit CouplingPairIdxSz <- "mc_src2_base";
        Read mc_src2_count_v : Bit CouplingPairCountSz <- "mc_src2_count";
        Read mc_write_ptr_v  : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read coupling_pair_src_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Read coupling_pair_dst_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        Read coupling_pair_valid_table_v : Vector Bool CouplingPairIdxSz <- "coupling_pair_valid_table";

        Read mc_err_v : Bool <- "err";
        Read mc_error_v : Bit WordSz <- "error_code";

        LET mc_in_range1 <- #mc_i_v < #mc_src1_count_v;
        LET mc_in_range2 <- #mc_j_v < #mc_src2_count_v;
        LET mc_read_idx : Bit CouplingPairIdxSz <-
          IF #mc_in_range1 then (#mc_src1_base_v + UniBit (Trunc CouplingPairIdxSz 1) #mc_i_v)
          else (#mc_src2_base_v + UniBit (Trunc CouplingPairIdxSz 1) #mc_j_v);
        LET mc_copy_src : Bit WordSz <- #coupling_pair_src_table_v@[#mc_read_idx];
        LET mc_copy_dst : Bit WordSz <- #coupling_pair_dst_table_v@[#mc_read_idx];

        LET mc_j_next : Bit CouplingPairCountSz <- #mc_j_v + $1;
        LET mc_done <- !#mc_in_range1 && !#mc_in_range2;
        LET mc_full <- #mc_write_ptr_v == $$(natToWord DescTableNextIdSz 16);
        LET mc_blocked <- #mc_done || #mc_full;
        LET mc_overflow <- !#mc_done && #mc_full;
        Write "err" <- #mc_err_v || #mc_overflow;
        Write "error_code" <- IF #mc_overflow then $$(ERR_COUPLING_INVALID) else #mc_error_v;

        Write "coupling_pair_src_table" <-
          IF #mc_blocked then #coupling_pair_src_table_v
          else #coupling_pair_src_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_copy_src];
        Write "coupling_pair_dst_table" <-
          IF #mc_blocked then #coupling_pair_dst_table_v
          else #coupling_pair_dst_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_copy_dst];
        Write "coupling_pair_valid_table" <-
          IF #mc_blocked then #coupling_pair_valid_table_v
          else #coupling_pair_valid_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- $$true];
        Write "mc_i" <- IF #mc_in_range1 then (#mc_i_v + $1) else #mc_i_v;
        Write "mc_j" <- IF #mc_in_range1 then #mc_j_v else #mc_j_next;
        Write "mc_write_ptr" <- IF #mc_blocked then #mc_write_ptr_v else (#mc_write_ptr_v + $1);
        Write "mc_phase" <- IF #mc_overflow then $$(natToWord 4 0) else (IF #mc_done then $$(WO~0~1~0~1) else $$(WO~0~1~0~0));
        Retv

      with Rule "mc_join_loop" :=
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $$(WO~0~1~1~1));

        Read mc_i_v          : Bit CouplingPairCountSz <- "mc_i";
        Read mc_j_v          : Bit CouplingPairCountSz <- "mc_j";
        Read mc_src1_base_v  : Bit CouplingPairIdxSz <- "mc_src1_base";
        Read mc_src1_count_v : Bit CouplingPairCountSz <- "mc_src1_count";
        Read mc_src2_base_v  : Bit CouplingPairIdxSz <- "mc_src2_base";
        Read mc_src2_count_v : Bit CouplingPairCountSz <- "mc_src2_count";
        Read mc_write_ptr_v  : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read coupling_pair_src_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Read coupling_pair_dst_table_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        Read coupling_pair_valid_table_v : Vector Bool CouplingPairIdxSz <- "coupling_pair_valid_table";

        Read mc_err_v : Bool <- "err";
        Read mc_error_v : Bit WordSz <- "error_code";
        LET mc_empty <- (#mc_src1_count_v == $0) || (#mc_src2_count_v == $0);

        LET mc_idx1 : Bit CouplingPairIdxSz <-
          #mc_src1_base_v + UniBit (Trunc CouplingPairIdxSz 1) #mc_i_v;
        LET mc_idx2 : Bit CouplingPairIdxSz <-
          #mc_src2_base_v + UniBit (Trunc CouplingPairIdxSz 1) #mc_j_v;
        LET mc_p1_src : Bit WordSz <- #coupling_pair_src_table_v@[#mc_idx1];
        LET mc_p1_dst : Bit WordSz <- #coupling_pair_dst_table_v@[#mc_idx1];
        LET mc_p2_src : Bit WordSz <- #coupling_pair_src_table_v@[#mc_idx2];
        LET mc_p2_dst : Bit WordSz <- #coupling_pair_dst_table_v@[#mc_idx2];
        (* Relational join key: emit (p1.src, p2.dst) exactly when
           p1.dst == p2.src, matching the software's relational_compose. *)
        LET mc_match <- #mc_p1_dst == #mc_p2_src;
        LET mc_room <- #mc_write_ptr_v < $$(natToWord DescTableNextIdSz 16);
        LET mc_emits <- !#mc_empty && #mc_match && #mc_room;
        LET mc_overflow <- !#mc_empty && #mc_match && !#mc_room;
        Write "err" <- #mc_err_v || #mc_overflow;
        Write "error_code" <- IF #mc_overflow then $$(ERR_COUPLING_INVALID) else #mc_error_v;

        LET mc_j_next : Bit CouplingPairCountSz <- #mc_j_v + $1;
        LET mc_j_wraps <- (#mc_j_next == #mc_src2_count_v);
        LET mc_i_next : Bit CouplingPairCountSz <- #mc_i_v + $1;
        LET mc_i_done <- #mc_j_wraps && (#mc_i_next == #mc_src1_count_v);

        Write "coupling_pair_src_table" <-
          IF #mc_emits then #coupling_pair_src_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_p1_src]
          else #coupling_pair_src_table_v;
        Write "coupling_pair_dst_table" <-
          IF #mc_emits then #coupling_pair_dst_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- #mc_p2_dst]
          else #coupling_pair_dst_table_v;
        Write "coupling_pair_valid_table" <-
          IF #mc_emits then #coupling_pair_valid_table_v@[UniBit (Trunc CouplingPairIdxSz 1) #mc_write_ptr_v <- $$true]
          else #coupling_pair_valid_table_v;
        Write "mc_write_ptr" <- IF #mc_emits then (#mc_write_ptr_v + $1) else #mc_write_ptr_v;
        Write "mc_j" <- IF #mc_j_wraps then $0 else #mc_j_next;
        Write "mc_i" <- IF #mc_j_wraps then #mc_i_next else #mc_i_v;
        Write "mc_phase" <- IF #mc_overflow then $$(natToWord 4 0) else (IF (#mc_empty || #mc_i_done) then $$(WO~0~1~0~1) else $$(WO~0~1~1~1));
        Retv

      (* Compact only the newly allocated range. Scanning the untouched suffix
         before copying keeps the LAST occurrence, exactly as Coq's nodup.
         The output pointer never exceeds the input pointer. *)
      with Rule "mc_normalize_start" :=
        Read phase_v : Bit 4 <- "mc_phase";
        Assert (#phase_v == $$(natToWord 4 5));
        Read base_v : Bit DescTableNextIdSz <- "mc_write_base";
        Read end_v : Bit DescTableNextIdSz <- "mc_write_ptr";
        Write "mc_i" <- #base_v;
        Write "mc_j" <- #base_v + $1;
        Write "mc_norm_ptr" <- #base_v;
        Write "mc_duplicate" <- $$false;
        Write "mc_phase" <- IF (#base_v == #end_v) then $$(natToWord 4 11) else $$(natToWord 4 8);
        Retv

      with Rule "mc_normalize_scan" :=
        Read phase_v : Bit 4 <- "mc_phase";
        Assert (#phase_v == $$(natToWord 4 8));
        Read i_v : Bit CouplingPairCountSz <- "mc_i";
        Read j_v : Bit CouplingPairCountSz <- "mc_j";
        Read end_v : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read duplicate_v : Bool <- "mc_duplicate";
        Read src_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Read dst_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        LET i_idx : Bit CouplingPairIdxSz <- UniBit (Trunc CouplingPairIdxSz 1) #i_v;
        LET j_idx : Bit CouplingPairIdxSz <- UniBit (Trunc CouplingPairIdxSz 1) #j_v;
        LET in_range <- #j_v < #end_v;
        LET same_pair <- (#src_v@[#i_idx] == #src_v@[#j_idx]) && (#dst_v@[#i_idx] == #dst_v@[#j_idx]);
        Write "mc_duplicate" <- #duplicate_v || (#in_range && #same_pair);
        Write "mc_j" <- #j_v + $1;
        Write "mc_phase" <- IF #in_range then $$(natToWord 4 8) else $$(natToWord 4 9);
        Retv

      with Rule "mc_normalize_emit" :=
        Read phase_v : Bit 4 <- "mc_phase";
        Assert (#phase_v == $$(natToWord 4 9));
        Read i_v : Bit CouplingPairCountSz <- "mc_i";
        Read end_v : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read out_v : Bit DescTableNextIdSz <- "mc_norm_ptr";
        Read duplicate_v : Bool <- "mc_duplicate";
        Read src_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Read dst_v : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        LET i_idx : Bit CouplingPairIdxSz <- UniBit (Trunc CouplingPairIdxSz 1) #i_v;
        LET out_idx : Bit CouplingPairIdxSz <- UniBit (Trunc CouplingPairIdxSz 1) #out_v;
        LET out_next : Bit DescTableNextIdSz <- IF #duplicate_v then #out_v else (#out_v + $1);
        LET i_next : Bit CouplingPairCountSz <- #i_v + $1;
        LET done <- #i_next == #end_v;
        Write "coupling_pair_src_table" <- IF #duplicate_v then #src_v else #src_v@[#out_idx <- #src_v@[#i_idx]];
        Write "coupling_pair_dst_table" <- IF #duplicate_v then #dst_v else #dst_v@[#out_idx <- #dst_v@[#i_idx]];
        Write "mc_norm_ptr" <- #out_next;
        Write "mc_write_ptr" <- IF #done then #out_next else #end_v;
        Write "mc_i" <- #i_next;
        Write "mc_j" <- #i_next + $1;
        Write "mc_duplicate" <- $$false;
        Write "mc_phase" <- IF #done then $$(natToWord 4 11) else $$(natToWord 4 8);
        Retv

      with Rule "mc_commit" :=
        Read mc_phase_v : Bit 4 <- "mc_phase";
        Assert (#mc_phase_v == $$(natToWord 4 11));

        Read mc_write_base_v : Bit DescTableNextIdSz <- "mc_write_base";
        Read mc_write_ptr_v  : Bit DescTableNextIdSz <- "mc_write_ptr";
        Read coupling_desc_next_id_v : Bit DescTableNextIdSz <- "coupling_desc_next_id";
        Read coupling_desc_base_table_v : Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz <- "coupling_desc_base_table";
        Read coupling_desc_count_table_v : Vector (Bit CouplingPairCountSz) CouplingDescIdxSz <- "coupling_desc_count_table";
        Read coupling_desc_valid_table_v : Vector Bool CouplingDescIdxSz <- "coupling_desc_valid_table";

        LET mc_desc_id : Bit CouplingDescIdxSz <-
          UniBit (Trunc CouplingDescIdxSz 1) #coupling_desc_next_id_v;
        LET mc_final_count : Bit CouplingPairCountSz <-
          #mc_write_ptr_v - #mc_write_base_v;

        Write "coupling_desc_base_table" <-
          #coupling_desc_base_table_v@[#mc_desc_id <- UniBit (Trunc CouplingPairIdxSz 1) #mc_write_base_v];
        Write "coupling_desc_count_table" <-
          #coupling_desc_count_table_v@[#mc_desc_id <- #mc_final_count];
        Write "coupling_desc_valid_table" <-
          #coupling_desc_valid_table_v@[#mc_desc_id <- $$true];
        Write "coupling_desc_next_id" <- #coupling_desc_next_id_v + $1;
        Write "coupling_pair_next_id" <- #mc_write_ptr_v;
        Write "mc_phase" <- $$(natToWord 4 0);
        Retv

      (** CHSH_LASSERT multi-cycle FSM: pipelines the column-contractive
          witness check across 23 cycles using one shared 384×384 multiplier.

          Phase encoding (Bit 5):
            0          : idle (step rule fires)
            1..8       : compute n00² ... d11² (8 squarings)
            9..14      : compute A_pos, A_neg_a, A_neg_b, B_pos, B_neg_a, B_neg_b
            15..18     : compute d00·d01, n10·n11, d10·d11, n00·n01
            19..20     : compute abs_C1, abs_C2
            21         : compute |C|² (uses abs_C derived combinationally from
                                       abs_C1, abs_C2 and the latched signs)
            22         : compute A·B (uses abs_A, abs_B derived from regs)
            23         : final compare + commit (writes chsh_check_result)

          Step rule is inhibited (Assert chsh_phase == 0) while the FSM runs.

          One BinBit (Mul 768 SignUU) instance lives in this rule; operands are
          phase-muxed; result is phase-demuxed to the correct intermediate reg.
          yosys synthesizes this as one shared multiplier rather than 22
          combinational instances. *)
      with Rule "chsh_lassert_fsm" :=
        Read chsh_phase_v : Bit 5 <- "chsh_phase";
        Assert (!(#chsh_phase_v == $$(WO~0~0~0~0~0)));
        Read chsh_n00_v     : Bit 64  <- "chsh_n00";
        Read chsh_n01_v     : Bit 64  <- "chsh_n01";
        Read chsh_n10_v     : Bit 64  <- "chsh_n10";
        Read chsh_n11_v     : Bit 64  <- "chsh_n11";
        Read chsh_d00_v     : Bit 64  <- "chsh_d00";
        Read chsh_d01_v     : Bit 64  <- "chsh_d01";
        Read chsh_d10_v     : Bit 64  <- "chsh_d10";
        Read chsh_d11_v     : Bit 64  <- "chsh_d11";
        Read chsh_sign00_v  : Bool    <- "chsh_sign00";
        Read chsh_sign01_v  : Bool    <- "chsh_sign01";
        Read chsh_sign10_v  : Bool    <- "chsh_sign10";
        Read chsh_sign11_v  : Bool    <- "chsh_sign11";
        Read chsh_n00sq_v   : Bit 128 <- "chsh_n00sq";
        Read chsh_n01sq_v   : Bit 128 <- "chsh_n01sq";
        Read chsh_n10sq_v   : Bit 128 <- "chsh_n10sq";
        Read chsh_n11sq_v   : Bit 128 <- "chsh_n11sq";
        Read chsh_d00sq_v   : Bit 128 <- "chsh_d00sq";
        Read chsh_d01sq_v   : Bit 128 <- "chsh_d01sq";
        Read chsh_d10sq_v   : Bit 128 <- "chsh_d10sq";
        Read chsh_d11sq_v   : Bit 128 <- "chsh_d11sq";
        Read chsh_A_pos_v   : Bit 256 <- "chsh_A_pos";
        Read chsh_A_neg_a_v : Bit 256 <- "chsh_A_neg_a";
        Read chsh_A_neg_b_v : Bit 256 <- "chsh_A_neg_b";
        Read chsh_B_pos_v   : Bit 256 <- "chsh_B_pos";
        Read chsh_B_neg_a_v : Bit 256 <- "chsh_B_neg_a";
        Read chsh_B_neg_b_v : Bit 256 <- "chsh_B_neg_b";
        Read chsh_d00d01_v  : Bit 128 <- "chsh_d00d01";
        Read chsh_n10n11_v  : Bit 128 <- "chsh_n10n11";
        Read chsh_d10d11_v  : Bit 128 <- "chsh_d10d11";
        Read chsh_n00n01_v  : Bit 128 <- "chsh_n00n01";
        Read chsh_abs_C1_v  : Bit 256 <- "chsh_abs_C1";
        Read chsh_abs_C2_v  : Bit 256 <- "chsh_abs_C2";
        Read chsh_C_sq_v    : Bit 384 <- "chsh_C_sq";
        Read chsh_A_times_B_v : Bit 384 <- "chsh_A_times_B";
        Read chsh_check_result_v : Bool <- "chsh_check_result";
        Read pc_v_fsm        : Bit WordSz <- "pc";
        Read err_v_fsm       : Bool       <- "err";
        Read error_code_v_fsm : Bit WordSz <- "error_code";
        Read trap_vector_v_fsm : Bit WordSz <- "trap_vector";
        chsh_fsm_decoded chsh_phase_v chsh_n00_v chsh_n01_v chsh_n10_v chsh_n11_v chsh_d00_v chsh_d01_v chsh_d10_v chsh_d11_v chsh_sign00_v chsh_sign01_v chsh_sign10_v chsh_sign11_v chsh_n00sq_v chsh_n01sq_v chsh_n10sq_v chsh_n11sq_v chsh_d00sq_v chsh_d01sq_v chsh_d10sq_v chsh_d11sq_v chsh_A_pos_v chsh_A_neg_a_v chsh_A_neg_b_v chsh_B_pos_v chsh_B_neg_a_v chsh_B_neg_b_v chsh_d00d01_v chsh_n10n11_v chsh_d10d11_v chsh_n00n01_v chsh_abs_C1_v chsh_abs_C2_v chsh_C_sq_v chsh_A_times_B_v chsh_check_result_v pc_v_fsm err_v_fsm error_code_v_fsm trap_vector_v_fsm

      (** Method to load a program word into instruction memory;
          This is the external interface for program loading. *)
      with Method "loadInstr" (arg : Struct LoadInstrPort) : Void :=
        Read imem_v : Vector (Bit InstrSz) MemAddrSz <- "imem";
        LET addr_v <- #arg!LoadInstrPort@."addr";
        LET data_v <- #arg!LoadInstrPort@."data";
        Write "imem" <- #imem_v@[#addr_v <- #data_v];
        Retv

      (** Output methods — create proper Verilog output ports for state observation *)
      with Method "getPC" () : Bit WordSz :=
        Read v : Bit WordSz <- "pc"; Ret #v

      with Method "getMu" () : Bit WordSz :=
        Read v : Bit WordSz <- "mu"; Ret #v

      with Method "getErr" () : Bool :=
        Read v : Bool <- "err"; Ret #v

      with Method "getHalted" () : Bool :=
        Read v : Bool <- "halted"; Ret #v

      with Method "getCertified" () : Bool :=
        Read v : Bool <- "certified"; Ret #v

      with Method "getWcSame00" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_same_00"; Ret #v
      with Method "getWcDiff00" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_diff_00"; Ret #v
      with Method "getWcSame01" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_same_01"; Ret #v
      with Method "getWcDiff01" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_diff_01"; Ret #v
      with Method "getWcSame10" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_same_10"; Ret #v
      with Method "getWcDiff10" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_diff_10"; Ret #v
      with Method "getWcSame11" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_same_11"; Ret #v
      with Method "getWcDiff11" () : Bit WordSz :=
        Read v : Bit WordSz <- "wc_diff_11"; Ret #v

      with Method "getPartitionOps" () : Bit WordSz :=
        Read v : Bit WordSz <- "partition_ops"; Ret #v

      with Method "getMdlOps" () : Bit WordSz :=
        Read v : Bit WordSz <- "mdl_ops"; Ret #v

      with Method "getInfoGain" () : Bit WordSz :=
        Read v : Bit WordSz <- "info_gain"; Ret #v

      with Method "getErrorCode" () : Bit WordSz :=
        Read v : Bit WordSz <- "error_code"; Ret #v

      with Method "getMstatus" () : Bit WordSz :=
        Read v : Bit WordSz <- "mstatus"; Ret #v

      with Method "getMcycleLo" () : Bit WordSz :=
        Read v : Bit WordSz <- "mcycle_lo"; Ret #v

      with Method "getMcycleHi" () : Bit WordSz :=
        Read v : Bit WordSz <- "mcycle_hi"; Ret #v

      with Method "getMinstretLo" () : Bit WordSz :=
        Read v : Bit WordSz <- "minstret_lo"; Ret #v

      with Method "getMinstretHi" () : Bit WordSz :=
        Read v : Bit WordSz <- "minstret_hi"; Ret #v

      with Method "getLogicAcc" () : Bit WordSz :=
        Read v : Bit WordSz <- "logic_acc"; Ret #v

      with Method "getCertAddr" () : Bit WordSz :=
        Read v : Bit WordSz <- "cert_addr"; Ret #v

      with Method "getMuTensor0" () : Bit WordSz :=
        Read t : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        LET s : Bit WordSz <-
          #t@[$$(WO~0~0~0~0)] + #t@[$$(WO~0~0~0~1)] +
          #t@[$$(WO~0~0~1~0)] + #t@[$$(WO~0~0~1~1)];
        Ret #s

      with Method "getMuTensor1" () : Bit WordSz :=
        Read t : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        LET s : Bit WordSz <-
          #t@[$$(WO~0~1~0~0)] + #t@[$$(WO~0~1~0~1)] +
          #t@[$$(WO~0~1~1~0)] + #t@[$$(WO~0~1~1~1)];
        Ret #s

      with Method "getMuTensor2" () : Bit WordSz :=
        Read t : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        LET s : Bit WordSz <-
          #t@[$$(WO~1~0~0~0)] + #t@[$$(WO~1~0~0~1)] +
          #t@[$$(WO~1~0~1~0)] + #t@[$$(WO~1~0~1~1)];
        Ret #s

      with Method "getMuTensor3" () : Bit WordSz :=
        Read t : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        LET s : Bit WordSz <-
          #t@[$$(WO~1~1~0~0)] + #t@[$$(WO~1~1~0~1)] +
          #t@[$$(WO~1~1~1~0)] + #t@[$$(WO~1~1~1~1)];
        Ret #s

      with Method "setActiveModule" (mid : Bit PTableIdxSz) : Void :=
        Write "active_module" <- #mid; Retv

      with Method "setTrapVector" (tv : Bit WordSz) : Void :=
        Write "trap_vector" <- #tv; Retv

      with Method "apbReadData" (addr : Bit WordSz) : Bit WordSz :=
        Read pc_v : Bit WordSz <- "pc";
        Read mu_v : Bit WordSz <- "mu";
        Read err_v : Bool <- "err";
        Read halted_v : Bool <- "halted";
        Read partition_ops_v : Bit WordSz <- "partition_ops";
        Read mdl_ops_v : Bit WordSz <- "mdl_ops";
        Read info_gain_v : Bit WordSz <- "info_gain";
        Read error_code_v : Bit WordSz <- "error_code";
        Read mstatus_v : Bit WordSz <- "mstatus";
        Read mcycle_lo_v : Bit WordSz <- "mcycle_lo";
        Read mcycle_hi_v : Bit WordSz <- "mcycle_hi";
        Read minstret_lo_v : Bit WordSz <- "minstret_lo";
        Read minstret_hi_v : Bit WordSz <- "minstret_hi";
        Read logic_acc_v : Bit WordSz <- "logic_acc";
        Read cert_addr_v : Bit WordSz <- "cert_addr";
        Read mu_tensor_v : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        Read pt_next_id_v : Bit PTableNextIdSz <- "pt_next_id";
        Read pt_sizes_v : Vector (Bit WordSz) PTableIdxSz <- "ptTable";
        LET mu_tensor0 : Bit WordSz <-
          #mu_tensor_v@[$$(WO~0~0~0~0)] + #mu_tensor_v@[$$(WO~0~0~0~1)] +
          #mu_tensor_v@[$$(WO~0~0~1~0)] + #mu_tensor_v@[$$(WO~0~0~1~1)];
        LET mu_tensor1 : Bit WordSz <-
          #mu_tensor_v@[$$(WO~0~1~0~0)] + #mu_tensor_v@[$$(WO~0~1~0~1)] +
          #mu_tensor_v@[$$(WO~0~1~1~0)] + #mu_tensor_v@[$$(WO~0~1~1~1)];
        LET mu_tensor2 : Bit WordSz <-
          #mu_tensor_v@[$$(WO~1~0~0~0)] + #mu_tensor_v@[$$(WO~1~0~0~1)] +
          #mu_tensor_v@[$$(WO~1~0~1~0)] + #mu_tensor_v@[$$(WO~1~0~1~1)];
        LET mu_tensor3 : Bit WordSz <-
          #mu_tensor_v@[$$(WO~1~1~0~0)] + #mu_tensor_v@[$$(WO~1~1~0~1)] +
          #mu_tensor_v@[$$(WO~1~1~1~0)] + #mu_tensor_v@[$$(WO~1~1~1~1)];
        LET tensor_total : Bit WordSz <- #mu_tensor0 + #mu_tensor1 + #mu_tensor2 + #mu_tensor3;
        LET bianchi_alarm_v <- #tensor_total > #mu_v;
        LET pt_next_id32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #pt_next_id_v;
        LET pt_size0 : Bit WordSz <- #pt_sizes_v@[$$(natToWord PTableIdxSz 0)];
        LET rdata : Bit WordSz <-
          IF (#addr == $$(natToWord WordSz 0)) then #pc_v
          else (IF (#addr == $$(natToWord WordSz 4)) then #mu_v
          else (IF (#addr == $$(natToWord WordSz 8)) then (IF #err_v then $1 else $0)
          else (IF (#addr == $$(natToWord WordSz 12)) then (IF #halted_v then $1 else $0)
          else (IF (#addr == $$(natToWord WordSz 16)) then #partition_ops_v
          else (IF (#addr == $$(natToWord WordSz 20)) then #mdl_ops_v
          else (IF (#addr == $$(natToWord WordSz 24)) then #info_gain_v
          else (IF (#addr == $$(natToWord WordSz 28)) then #error_code_v
          else (IF (#addr == $$(natToWord WordSz 32)) then #mstatus_v
          else (IF (#addr == $$(natToWord WordSz 36)) then #mcycle_lo_v
          else (IF (#addr == $$(natToWord WordSz 40)) then #mcycle_hi_v
          else (IF (#addr == $$(natToWord WordSz 44)) then #minstret_lo_v
          else (IF (#addr == $$(natToWord WordSz 48)) then #minstret_hi_v
          else (IF (#addr == $$(natToWord WordSz 52)) then #logic_acc_v
          else (IF (#addr == $$(natToWord WordSz 56)) then #cert_addr_v
          else (IF (#addr == $$(natToWord WordSz 68)) then #mu_tensor0
          else (IF (#addr == $$(natToWord WordSz 72)) then #mu_tensor1
          else (IF (#addr == $$(natToWord WordSz 76)) then #mu_tensor2
          else (IF (#addr == $$(natToWord WordSz 80)) then #mu_tensor3
          else (IF (#addr == $$(natToWord WordSz 84)) then (IF #bianchi_alarm_v then $1 else $0)
          else (IF (#addr == $$(natToWord WordSz 88)) then #pt_next_id32
          else (IF (#addr == $$(natToWord WordSz 92)) then #pt_size0 else $0)))))))))))))))))))));
        Ret #rdata

      with Method "apbReadErr" (addr : Bit WordSz) : Bool :=
        LET is_readable <-
          (#addr == $$(natToWord WordSz 0)) ||
          (#addr == $$(natToWord WordSz 4)) ||
          (#addr == $$(natToWord WordSz 8)) ||
          (#addr == $$(natToWord WordSz 12)) ||
          (#addr == $$(natToWord WordSz 16)) ||
          (#addr == $$(natToWord WordSz 20)) ||
          (#addr == $$(natToWord WordSz 24)) ||
          (#addr == $$(natToWord WordSz 28)) ||
          (#addr == $$(natToWord WordSz 32)) ||
          (#addr == $$(natToWord WordSz 36)) ||
          (#addr == $$(natToWord WordSz 40)) ||
          (#addr == $$(natToWord WordSz 44)) ||
          (#addr == $$(natToWord WordSz 48)) ||
          (#addr == $$(natToWord WordSz 52)) ||
          (#addr == $$(natToWord WordSz 56)) ||
          (#addr == $$(natToWord WordSz 68)) ||
          (#addr == $$(natToWord WordSz 72)) ||
          (#addr == $$(natToWord WordSz 76)) ||
          (#addr == $$(natToWord WordSz 80)) ||
          (#addr == $$(natToWord WordSz 84)) ||
          (#addr == $$(natToWord WordSz 88)) ||
          (#addr == $$(natToWord WordSz 92));
        Ret (!#is_readable)

      with Method "apbWrite" (arg : Struct APBBusWritePort) : Bool :=
        Read imem_v : Vector (Bit InstrSz) MemAddrSz <- "imem";
        Read active_module_v : Bit PTableIdxSz <- "active_module";
        Read trap_vector_v : Bit WordSz <- "trap_vector";
        Read bus_load_instr_addr_v : Bit MemAddrSz <- "bus_load_instr_addr";
        Read bus_load_instr_data_v : Bit InstrSz <- "bus_load_instr_data";
        Read bus_load_instr_kick_v : Bool <- "bus_load_instr_kick";
        LET addr <- #arg!APBBusWritePort@."addr";
        LET data <- #arg!APBBusWritePort@."data";
        LET data32 : Bit WordSz <- UniBit (Trunc WordSz InstrUpperSz) #data;
        LET wr_load_instr_addr <- #addr == $$(natToWord WordSz 128);
        LET wr_load_instr_data <- #addr == $$(natToWord WordSz 132);
        LET wr_load_instr_kick <- #addr == $$(natToWord WordSz 136);
        LET wr_set_active_module <- #addr == $$(natToWord WordSz 152);
        LET wr_set_trap_vector <- #addr == $$(natToWord WordSz 156);
        LET wr_any <-
          #wr_load_instr_addr ||
          #wr_load_instr_data ||
          #wr_load_instr_kick ||
          #wr_set_active_module ||
          #wr_set_trap_vector;
        LET data_mem_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #data32;
        LET data_instr : Bit InstrSz <- #data;
        LET data_nonzero <- #data != $0;
        LET next_load_instr_addr : Bit MemAddrSz <-
          IF #wr_load_instr_addr then #data_mem_addr else #bus_load_instr_addr_v;
        LET next_load_instr_data : Bit InstrSz <-
          IF #wr_load_instr_data then #data_instr else #bus_load_instr_data_v;
        LET next_load_instr_kick <-
          IF #wr_load_instr_kick then #data_nonzero else #bus_load_instr_kick_v;
        LET do_instr_commit <- #wr_load_instr_kick && #data_nonzero;
        LET next_imem : Vector (Bit InstrSz) MemAddrSz <-
          IF #do_instr_commit
          then #imem_v@[#next_load_instr_addr <- #next_load_instr_data]
          else #imem_v;
        LET next_active_module : Bit PTableIdxSz <-
          IF #wr_set_active_module
          then UniBit (Trunc PTableIdxSz _) #data32
          else #active_module_v;
        LET next_trap_vector : Bit WordSz <-
          IF #wr_set_trap_vector then #data32 else #trap_vector_v;
        Write "imem" <- #next_imem;
        Write "bus_load_instr_addr" <- #next_load_instr_addr;
        Write "bus_load_instr_data" <- #next_load_instr_data;
        Write "bus_load_instr_kick" <- #next_load_instr_kick;
        Write "active_module" <- #next_active_module;
        Write "trap_vector" <- #next_trap_vector;
        Ret (!#wr_any)

      with Method "getBianchiAlarm" () : Bool :=
        Read t : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        Read m : Bit WordSz <- "mu";
        LET total : Bit WordSz <-
          #t@[$$(WO~0~0~0~0)] + #t@[$$(WO~0~0~0~1)] +
          #t@[$$(WO~0~0~1~0)] + #t@[$$(WO~0~0~1~1)] +
          #t@[$$(WO~0~1~0~0)] + #t@[$$(WO~0~1~0~1)] +
          #t@[$$(WO~0~1~1~0)] + #t@[$$(WO~0~1~1~1)] +
          #t@[$$(WO~1~0~0~0)] + #t@[$$(WO~1~0~0~1)] +
          #t@[$$(WO~1~0~1~0)] + #t@[$$(WO~1~0~1~1)] +
          #t@[$$(WO~1~1~0~0)] + #t@[$$(WO~1~1~0~1)] +
          #t@[$$(WO~1~1~1~0)] + #t@[$$(WO~1~1~1~1)];
        Ret (#total > #m)

      (** Partition table output methods — expose pt_next_id and slot sizes for verification *)
      with Method "getPtNextId" () : Bit WordSz :=
        Read v : Bit PTableNextIdSz <- "pt_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getPtSize" (idx : Bit PTableIdxSz) : Bit WordSz :=
        Read pt_sizes_v : Vector (Bit WordSz) PTableIdxSz <- "ptTable";
        Ret (#pt_sizes_v@[#idx])

      with Method "getMorphNextId" () : Bit WordSz :=
        Read v : Bit MorphTableNextIdSz <- "morph_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getMorphSrc" (idx : Bit MorphTableIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit PTableIdxSz) MorphTableIdxSz <- "morph_src_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getMorphDst" (idx : Bit MorphTableIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit PTableIdxSz) MorphTableIdxSz <- "morph_dst_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getMorphCouplingDesc" (idx : Bit MorphTableIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit DescIdxSz) MorphTableIdxSz <- "morph_coupling_desc_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getMorphValid" (idx : Bit MorphTableIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool MorphTableIdxSz <- "morph_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getMorphIdentity" (idx : Bit MorphTableIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool MorphTableIdxSz <- "morph_identity_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getCouplingDescBase" (idx : Bit CouplingDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz <- "coupling_desc_base_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getCouplingDescCount" (idx : Bit CouplingDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit CouplingPairCountSz) CouplingDescIdxSz <- "coupling_desc_count_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getCouplingDescValid" (idx : Bit CouplingDescIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool CouplingDescIdxSz <- "coupling_desc_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getCouplingDescNextId" () : Bit WordSz :=
        Read v : Bit DescTableNextIdSz <- "coupling_desc_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getCouplingPairSrc" (idx : Bit CouplingPairIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_src_table";
        Ret (#tbl@[#idx])

      with Method "getCouplingPairDst" (idx : Bit CouplingPairIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) CouplingPairIdxSz <- "coupling_pair_dst_table";
        Ret (#tbl@[#idx])

      with Method "getCouplingPairValid" (idx : Bit CouplingPairIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool CouplingPairIdxSz <- "coupling_pair_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getCouplingPairNextId" () : Bit WordSz :=
        Read v : Bit DescTableNextIdSz <- "coupling_pair_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getFormulaDescBase" (idx : Bit FormulaDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) FormulaDescIdxSz <- "formula_desc_base_table";
        Ret (#tbl@[#idx])

      with Method "getFormulaDescCount" (idx : Bit FormulaDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) FormulaDescIdxSz <- "formula_desc_count_table";
        Ret (#tbl@[#idx])

      with Method "getFormulaDescValid" (idx : Bit FormulaDescIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool FormulaDescIdxSz <- "formula_desc_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getFormulaDescNextId" () : Bit WordSz :=
        Read v : Bit DescTableNextIdSz <- "formula_desc_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getCertDescBase" (idx : Bit CertDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) CertDescIdxSz <- "cert_desc_base_table";
        Ret (#tbl@[#idx])

      with Method "getCertDescCount" (idx : Bit CertDescIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) CertDescIdxSz <- "cert_desc_count_table";
        Ret (#tbl@[#idx])

      with Method "getCertDescValid" (idx : Bit CertDescIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool CertDescIdxSz <- "cert_desc_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getCertDescNextId" () : Bit WordSz :=
        Read v : Bit DescTableNextIdSz <- "cert_desc_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getDescMetaSubtype" (idx : Bit DescMetaIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit FormatSubtypeSz) DescMetaIdxSz <- "desc_meta_subtype_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getDescMetaKind" (idx : Bit DescMetaIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit DescKindFieldSz) DescMetaIdxSz <- "desc_meta_kind_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getDescMetaInlineLen" (idx : Bit DescMetaIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit InlineLenSz) DescMetaIdxSz <- "desc_meta_inline_len_table";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) (#tbl@[#idx]);
        Ret #v32

      with Method "getDescMetaAux" (idx : Bit DescMetaIdxSz) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) DescMetaIdxSz <- "desc_meta_aux_table";
        Ret (#tbl@[#idx])

      with Method "getDescMetaValid" (idx : Bit DescMetaIdxSz) : Bit WordSz :=
        Read tbl : Vector Bool DescMetaIdxSz <- "desc_meta_valid_table";
        Ret (IF #tbl@[#idx] then $1 else $0)

      with Method "getDescMetaNextId" () : Bit WordSz :=
        Read v : Bit DescTableNextIdSz <- "desc_meta_next_id";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getLassertPhase" () : Bit WordSz :=
        Read v : Bit 3 <- "lassert_phase";
        LET v32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #v;
        Ret #v32

      with Method "getLassertKind" () : Bit WordSz :=
        Read v : Bool <- "lassert_kind";
        Ret (IF #v then $1 else $0)

      with Method "getLassertFBase" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_fbase"; Ret #v

      with Method "getLassertCBase" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_cbase"; Ret #v

      with Method "getLassertFLen" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_flen"; Ret #v

      with Method "getLassertCLen" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_clen"; Ret #v

      with Method "getLassertFPtr" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_fptr"; Ret #v

      with Method "getLassertCPtr" () : Bit WordSz :=
        Read v : Bit WordSz <- "lassert_cptr"; Ret #v

      with Method "getLassertClauseSat" () : Bit WordSz :=
        Read v : Bool <- "lassert_clause_sat";
        Ret (IF #v then $1 else $0)

      with Method "getLassertFbufWord" (idx : Bit 6) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) 6 <- "lassert_fbuf";
        Ret (#tbl@[#idx])

      with Method "getLassertCbufWord" (idx : Bit 6) : Bit WordSz :=
        Read tbl : Vector (Bit WordSz) 6 <- "lassert_cbuf";
        Ret (#tbl@[#idx])
    }.

  (** Extraction targets *)
  Definition thieleCoreS := getModuleS thieleCore.
  Definition thieleCoreB := ModulesSToBModules thieleCoreS.

End ThieleCPU.

#[global] Hint Unfold thieleCore : ModuleDefs.
