(** ThieleCPUCore.v — Complete Thiele CPU in Kami (38-instruction ISA).

    Implements the full ISA from VMStep.v:
      - Every instruction increments mu by its cost field (μ-monotonicity)
      - PC advances to PC+1 (sequential) or target (branch)
      - HALT latches the halted flag
      - CERTIFY sets the certified flag and charges S(cost) mu (structurally positive)

    Instruction encoding: [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost

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
      PNEW/PSPLIT/PMERGE/PDISCOVER/LASSERT/LJOIN/MDLACC/EMIT/ORACLE_HALTS:
        charge mu + advance PC (partition graph managed externally per Abstraction.v)
      CHECKPOINT: advances PC; label managed externally (NOP in hardware)
      READ_PORT:  op_a = dst; writes port value (hardware always provides 0)
      WRITE_PORT: op_a = channel, op_b = src; NOP in hardware (no I/O bus)
      HEAP_LOAD:  op_a = dst, op_b = addr register (address from register value)
      HEAP_STORE: op_a = addr register, op_b = src register
      CERTIFY:    no operands; cost = delta_mu; actual charge = S(cost) = cost+1


    Kami Vector notes: Vector K n stores 2^n elements, indexed by Bit n.
    So "regs" is Vector (Bit 32) 5 = 2^5 = 32 registers, indexed by Bit 5.
    And "mem" is Vector (Bit 32) 12 = 2^12 = 4096 memory words, indexed by Bit 12.
    And "imem" is Vector (Bit 32) 12 = 2^12 = 4096 instruction words.
    And "mu_tensor" is Vector (Bit 32) 4 = 2^4 = 16 tensor entries.

    LJOIN DESIGN DECISION:
    The RTL encoding packs {cert1, cert2} into a 16-bit payload — there is
    no string data in the 32-bit instruction word. At the hardware level,
    LJOIN delegates to the external coprocessor (same stall/response protocol
    as LASSERT). The coprocessor compares the two certificate indices and
    returns a match/mismatch result. The Coq kernel does String.eqb inline.
    These are proven equivalent in LogicEngineEquivalence.v given a correct
    oracle (ljoin_oracle_correct). See Section 3.2.5: "The kernel verifies
    the certificate but does not search for solutions." *)

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

  Definition LogicRespPort :=
    STRUCT {
      "valid" :: Bool ;
      "error" :: Bool ;
      "value" :: Bit WordSz
    }.

  Definition APBBusWritePort :=
    STRUCT {
      "addr" :: Bit WordSz ;
      "data" :: Bit WordSz
    }.

  (** Stack pointer register index (r31) *)
  Definition SP_IDX : word RegIdxSz := WO~1~1~1~1~1.

  (** Physical locality helper: address must stay within active partition size. *)
  Definition check_bounds
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (active_partition_size : Expr ty (SyntaxKind (Bit WordSz)))
    : Expr ty (SyntaxKind Bool) :=
    BinBitBool (Lt WordSz) (UniBit (ZeroExtendTrunc _ _) addr) active_partition_size.


  (** Direct vector read: memv[addr].
      Uses Kami's native ReadIndex which BSC compiles to a simple array index.
      Previous implementation used a depth-N binary search tree that generated
      2^N Kami nodes — untenable at MemAddrSz=12 (4096 elements). *)
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

  Definition thieleCore :=
    MODULE {
      (* Core registers matching VMState *)
      Register "pc"     : Bit WordSz <- Default
      with Register "mu"     : Bit WordSz <- Default
      with Register "err"    : Bool <- false
      with Register "halted" : Bool <- false
      with Register "regs"  : Vector (Bit WordSz) RegIdxSz <- Default
      with Register "mem"   : Vector (Bit WordSz) MemAddrSz <- Default
      with Register "imem"   : Vector (Bit InstrSz) MemAddrSz <- Default (* 2^12=4096 instrs *)

      (* Diagnostic counters — needed for test parity with handwritten RTL *)
      with Register "partition_ops" : Bit WordSz <- Default
      with Register "mdl_ops"       : Bit WordSz <- Default
      with Register "info_gain"     : Bit WordSz <- Default

      (* Error code register — specific error condition identifier *)
      with Register "error_code"    : Bit WordSz <- Default

      (* In-core logic engine accumulator: deterministic certificate/logic state. *)
      with Register "logic_acc"     : Bit WordSz <- Default

      (* Active module and CSR telemetry (RISC-V style management plane). *)
      with Register "active_module" : Bit PTableIdxSz <- ACTIVE_MODULE_INIT
      with Register "mstatus"       : Bit WordSz <- MSTATUS_THIELE
      with Register "mcycle_lo"     : Bit WordSz <- Default
      with Register "mcycle_hi"     : Bit WordSz <- Default
      with Register "minstret_lo"   : Bit WordSz <- Default
      with Register "minstret_hi"   : Bit WordSz <- Default
      with Register "trap_vector"   : Bit WordSz <- TRAP_VEC_INIT

      (* Explicit L-coprocessor request/response interface state (in-core ports). *)
      with Register "logic_req_valid"   : Bool <- false
      with Register "logic_req_opcode"  : Bit OpcodeSz <- Default
      with Register "logic_req_payload" : Bit WordSz <- Default
      with Register "logic_resp_valid"  : Bool <- false
      with Register "logic_resp_error"  : Bool <- false
      with Register "logic_resp_value"  : Bit WordSz <- Default
      with Register "logic_stall"       : Bool <- false
      with Register "bus_load_instr_addr" : Bit MemAddrSz <- Default
      with Register "bus_load_instr_data" : Bit InstrSz <- Default
      with Register "bus_load_instr_kick" : Bool <- false

      (* μ-tensor: 4×4 flattened (16 entries) for revelation direction tracking *)
      with Register "mu_tensor"     : Vector (Bit WordSz) MuTensorIdxSz <- Default

      (* Partition table — bounded to 16 slots by PTableIdxSz=4.
         pt_sizes[id] = region_size for that module slot (0 = unallocated/invalid).
         pt_next_id is the next free module ID to assign; initialized to 1 to match
         empty_graph.pg_next_id = 1 from VMState.v. *)
      with Register "ptTable"  : Vector (Bit WordSz) PTableIdxSz <- Default
      with Register "pt_next_id"    : Bit PTableNextIdSz <- PT_NEXT_ID_INIT

      (* Certification flag — set by CERTIFY opcode (Phase 4 state-based cert) *)
      with Register "certified" : Bool <- false

      (* Witness counters — 8-bucket CHSH trial recorder matching VMState.WitnessCounts.
         Each (setting_a, setting_b) pair has same/diff counters tracking whether
         outcomes (x,y) matched. Updated by CHSH_TRIAL on valid bits. *)
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

        Read logic_stall_v : Bool <- "logic_stall";

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
        Read active_module_v : Bit PTableIdxSz <- "active_module";
        Read mstatus_v : Bit WordSz <- "mstatus";
        Read mcycle_lo_v : Bit WordSz <- "mcycle_lo";
        Read mcycle_hi_v : Bit WordSz <- "mcycle_hi";
        Read minstret_lo_v : Bit WordSz <- "minstret_lo";
        Read minstret_hi_v : Bit WordSz <- "minstret_hi";
        Read trap_vector_v : Bit WordSz <- "trap_vector";
        Read logic_req_valid_v : Bool <- "logic_req_valid";
        Read logic_req_opcode_v : Bit OpcodeSz <- "logic_req_opcode";
        Read logic_req_payload_v : Bit WordSz <- "logic_req_payload";
        Read logic_resp_valid_v : Bool <- "logic_resp_valid";
        Read logic_resp_error_v : Bool <- "logic_resp_error";
        Read logic_resp_value_v : Bit WordSz <- "logic_resp_value";
        Read mu_tensor_v : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        Read pt_sizes_v : Vector (Bit WordSz) PTableIdxSz <- "ptTable";
        Read pt_next_id_v : Bit PTableNextIdSz <- "pt_next_id";
        Read certified_v : Bool <- "certified";

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

        (* Decode: extract fields from 32-bit instruction *)
        LET opcode : Bit OpcodeSz <- UniBit (ConstExtract 24 8 0) #instr_v;
        LET op_a   : Bit 8        <- UniBit (ConstExtract 16 8 8) #instr_v;
        LET op_b   : Bit 8        <- UniBit (ConstExtract 8 8 16) #instr_v;
        LET cost_v : Bit CostSz   <- UniBit (Trunc 8 24) #instr_v;

        (* Zero-extend cost to 32 bits for mu addition *)
        LET cost32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #cost_v;

        (* Compute new mu (always: mu' = mu + cost).
           This is the μ-monotonicity mechanism from VMStep.v:apply_cost *)
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
        LET mem_val_imm : Bit WordSz <- read_mem #mem_addr_imm #mem_v;

        (* Stack pointer (r31) for CALL/RET *)
        LET sp_val : Bit WordSz <- #regs_v@[$$(SP_IDX)];
        LET sp_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_val;
        LET sp_inc : Bit WordSz <- #sp_val + $1;
        LET sp_dec : Bit WordSz <- #sp_val - $1;
        LET sp_dec_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_dec;

        (* Partition wall enforcement: LOAD/STORE/CALL/RET may only access active module region. *)
        LET active_region_size : Bit WordSz <- #pt_sizes_v@[#active_module_v];
        LET load_in_bounds <- check_bounds #mem_addr #active_region_size;
        LET store_in_bounds <- check_bounds #mem_addr_a #active_region_size;
        LET call_in_bounds <- check_bounds #sp_addr #active_region_size;
        LET ret_in_bounds <- check_bounds #sp_dec_addr #active_region_size;
        LET is_load_op <- (#opcode == $$(OP_LOAD)) || (#opcode == $$(OP_XOR_LOAD)) ||
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

        (* Popcount for XOR_RANK: tree-based bit count *)
        LET pop_val : Bit WordSz <- #src_val;
        (* Step 1: pairs - (v & 0x55555555) + ((v >> 1) & 0x55555555) *)
        LET pop_mask1 : Bit WordSz <- $$(WO~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1~0~1);
        LET pop_s1a : Bit WordSz <- #pop_val ~& #pop_mask1;
        LET pop_s1b : Bit WordSz <- (BinBit (Srl _ _) #pop_val ($$(WO~0~0~0~0~1))) ~& #pop_mask1;
        LET pop_2 : Bit WordSz <- #pop_s1a + #pop_s1b;
        (* Step 2: nibbles - (v & 0x33333333) + ((v >> 2) & 0x33333333) *)
        LET pop_mask2 : Bit WordSz <- $$(WO~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1~0~0~1~1);
        LET pop_n1 : Bit WordSz <- #pop_2 ~& #pop_mask2;
        LET pop_n2 : Bit WordSz <- (BinBit (Srl _ _) #pop_2 ($$(WO~0~0~0~1~0))) ~& #pop_mask2;
        LET pop_4 : Bit WordSz <- #pop_n1 + #pop_n2;
        (* Step 3: bytes - (v & 0x0F0F0F0F) + ((v >> 4) & 0x0F0F0F0F) *)
        LET pop_mask3 : Bit WordSz <- $$(WO~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1~0~0~0~0~1~1~1~1);
        LET pop_b1 : Bit WordSz <- #pop_4 ~& #pop_mask3;
        LET pop_b2 : Bit WordSz <- (BinBit (Srl _ _) #pop_4 ($$(WO~0~0~1~0~0))) ~& #pop_mask3;
        LET pop_8 : Bit WordSz <- #pop_b1 + #pop_b2;
        (* Step 4: 16-bit halves *)
        LET pop_mask4 : Bit WordSz <- $$(WO~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1);
        LET pop_h1 : Bit WordSz <- #pop_8 ~& #pop_mask4;
        LET pop_h2 : Bit WordSz <- (BinBit (Srl _ _) #pop_8 ($$(WO~0~1~0~0~0))) ~& #pop_mask4;
        LET pop_16 : Bit WordSz <- #pop_h1 + #pop_h2;
        (* Step 5: final 32-bit sum *)
        LET pop_mask5 : Bit WordSz <- $$(WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1);
        LET popcount : Bit WordSz <- (#pop_16 + (BinBit (Srl _ _) #pop_16 ($$(WO~1~0~0~0~0)))) ~& #pop_mask5;

        (* CHSH_TRIAL certificate gate:
           - packed outcomes op_b are 2-bit values (0..3)
           - x=1 settings (op_a[1]) require non-zero mu_tensor evidence from REVEAL *)
        LET chsh_outcomes_bad <- #op_b > $$(WO~0~0~0~0~0~0~1~1);
        LET is_x1_trial <- #op_a > $$(WO~0~0~0~0~0~0~0~1);
        LET chsh_cert_missing <- (#is_x1_trial) && (#tensor_total == $0);
        LET chsh_bits_bad <- #chsh_cert_missing;

        (* CHSH_TRIAL witness counter update:
           op_a[1:0] = setting (a,b) → selects bucket (00/01/10/11)
           op_b[1:0] = outcome (x,y) → same when x==y, diff otherwise
           We use 2-bit truncations and compare to 2-bit constants. *)
        LET chsh_settings : Bit 2 <- UniBit (Trunc 2 _) #op_a;
        LET chsh_outcomes : Bit 2 <- UniBit (Trunc 2 _) #op_b;
        (* Outcomes same when both bits equal: 00 or 11 → same; 01 or 10 → diff *)
        LET chsh_outcomes_same <- (#chsh_outcomes == $$(WO~0~0)) || (#chsh_outcomes == $$(WO~1~1));
        LET is_bucket_00 <- #chsh_settings == $$(WO~0~0);
        LET is_bucket_01 <- #chsh_settings == $$(WO~0~1);
        LET is_bucket_10 <- #chsh_settings == $$(WO~1~0);
        LET is_bucket_11 <- #chsh_settings == $$(WO~1~1);

        (* L-coprocessor request/response interface semantics *)
        LET is_logic_op <- (#opcode == $$(OP_LASSERT)) || (#opcode == $$(OP_LJOIN));
        LET lpayload16 : Bit 16 <- {#op_a, #op_b};
        LET lpayload32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #lpayload16;
        LET logic_rsp_pending <- #logic_req_valid_v && !#logic_resp_valid_v;
        LET logic_rsp_fire <- #logic_req_valid_v && #logic_resp_valid_v;
        LET logic_issue <- #is_logic_op && !#logic_req_valid_v;

        (* No-Free-Insight guard for info-bearing instructions. *)
        LET op_b_32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;
        LET is_info_gain_op <-
          (#opcode == $$(OP_PDISCOVER)) || (#opcode == $$(OP_EMIT));
        LET nfi_violation <- #is_info_gain_op && (#cost32 < #op_b_32);

        (* CHSH_TRIAL is valid only when opcode matches and no violations *)
        LET is_chsh_valid <- (#opcode == $$(OP_CHSH_TRIAL)) && !#chsh_bits_bad &&
          !#bianchi_violation && !#locality_violation && !#ptable_overflow_violation &&
          !#high_value_locked && !#nfi_violation;

        (* REVEAL: tensor index from op_a[3:0] *)
        LET tensor_idx : Bit MuTensorIdxSz <- UniBit (Trunc MuTensorIdxSz _) #op_a;
        LET tensor_old : Bit WordSz <- #mu_tensor_v@[#tensor_idx];
        LET tensor_new_val : Bit WordSz <- #tensor_old + #cost32;

        (* ============================================================
           Determine new PC
           ============================================================ *)
        LET new_pc : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #trap_vector_v
          else (IF #logic_rsp_pending
                then #pc_v
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
                                        else #pc_plus_1))))));

        (* Pre-compute XOR_SWAP result: write both dst<-src and src<-dst *)
        LET swap_regs : Vector (Bit WordSz) RegIdxSz <-
          (#regs_v@[#dst_idx <- #src_val])@[#src_idx <- #dst_val];

        (* ============================================================
           Determine new register file
           ============================================================ *)
        LET new_regs : Vector (Bit WordSz) RegIdxSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
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
                then #regs_v@[#dst_idx <- #mem_val]
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
          else #regs_v))))))))))))))))))));
        (* ============================================================
           Determine new memory
           ============================================================ *)
        LET new_mem : Vector (Bit WordSz) MemAddrSz <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #mem_v
          else (IF (#opcode == $$(OP_STORE))
          then write_mem #mem_addr_a #src_val #mem_v
          else (IF (#opcode == $$(OP_CALL))
                then write_mem #sp_addr #pc_plus_1 #mem_v
          else (IF (#opcode == $$(OP_HEAP_STORE))
                then write_mem #mem_addr_a #src_val #mem_v
          else #mem_v)));

        (* Determine halted state *)
        LET new_halted <-
          #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation || (#opcode == $$(OP_HALT));

        (* Determine error state: protocol errors set err; logic errors come from coprocessor response. *)
        LET logic_resp_fail <- #logic_rsp_fire && #logic_resp_error_v;
        LET new_err <-
          #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation ||
          ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad) || #logic_resp_fail;

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
                            else (IF (#high_value_locked || #logic_resp_fail)
                                  then $$(ERR_LOGIC_VAL)
                                  else (IF ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad)
                                        then $$(ERR_CHSH_VAL)
                                        else #error_code_v)))));

        (* Determine new mu — only charge if not a bianchi violation.
           ORACLE_HALTS (0x10) always charges 1,000,000 regardless of cost field. *)
        LET final_mu : Bit WordSz <-
          IF (#bianchi_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #mu_v
          else (IF #logic_rsp_pending
                then #mu_v
                else (IF (#opcode == $$(OP_ORACLE_HALTS))
                      then #mu_v + $1000000
                      else (IF ((#opcode == $$(OP_CHSH_TRIAL)) && (#is_x1_trial))
                            then #new_mu + $$(CHSH_X1_SURCHARGE)
                            else (IF (#opcode == $$(OP_CERTIFY))
                                  then #mu_v + #cost32 + $1
                                  else #new_mu))));

        (* ============================================================
           CERTIFY flag update — set by CERTIFY opcode only
           ============================================================ *)
        LET new_certified : Bool <-
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #certified_v
          else (IF (#opcode == $$(OP_CERTIFY))
                then $$true
                else #certified_v);

        (* ============================================================
           Partition table updates (PNEW / PSPLIT / PMERGE)
           Matches handwritten RTL module_table / region_table semantics.
           pt_sizes[id] = region_size (0 = unallocated).
           pt_next_id grows monotonically.
           ============================================================ *)

        (* Truncate pt_next_id to PTableIdxSz bits for vector indexing *)
        LET pt_slot : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #pt_next_id_v;

        (* PNEW: allocate new slot at pt_next_id with region_size = op_a *)
        LET pnew_region_size : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_a;
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
          IF (#bianchi_violation || #ptable_overflow_violation)
          then #pt_sizes_v
          else (IF (#opcode == $$(OP_PNEW))
                then #pt_after_pnew
                else (IF (#opcode == $$(OP_PSPLIT))
                      then #pt_after_psplit
                      else (IF (#opcode == $$(OP_PMERGE))
                            then #pt_after_pmerge
                            else #pt_sizes_v)));

        LET new_pt_next_id : Bit PTableNextIdSz <-
          IF (#bianchi_violation || #ptable_overflow_violation)
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
           ============================================================ *)
        LET is_partition_op <-
          (#opcode == $$(OP_PNEW)) || (#opcode == $$(OP_PSPLIT)) || (#opcode == $$(OP_PMERGE));
        LET new_partition_ops : Bit WordSz <-
          IF (#is_partition_op && !#bianchi_violation)
          then #partition_ops_v + $1
          else #partition_ops_v;

        LET new_mdl_ops : Bit WordSz <-
          IF ((#opcode == $$(OP_MDLACC)) && !#bianchi_violation)
          then #mdl_ops_v + $1
          else #mdl_ops_v;

        (* info_gain increments only when No-Free-Insight bound is satisfied. *)
        LET new_info_gain : Bit WordSz <-
          IF (#is_info_gain_op && !#bianchi_violation && !#locality_violation &&
              !#ptable_overflow_violation && !#high_value_locked && !#nfi_violation)
          then #info_gain_v + #op_b_32
          else #info_gain_v;

        (* ============================================================
           Witness counter updates (CHSH_TRIAL increments the right bucket)
           ============================================================ *)
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
           μ-tensor update (REVEAL charges tensor entry)
           ============================================================ *)
        LET new_mu_tensor : Vector (Bit WordSz) MuTensorIdxSz <-
          IF ((#opcode == $$(OP_REVEAL)) && !#bianchi_violation && !#high_value_locked)
          then #mu_tensor_v@[#tensor_idx <- #tensor_new_val]
          else #mu_tensor_v;

        LET new_logic_acc : Bit WordSz <-
          IF (#bianchi_violation || #locality_violation)
          then #logic_acc_v
          else (IF #logic_rsp_fire
                then #logic_acc_v + #logic_resp_value_v
                else (IF (#opcode == $$(OP_LASSERT))
                      then #logic_acc_v ~+ $$(LOGIC_GATE_KEY)
                      else (IF (#opcode == $$(OP_ORACLE_HALTS))
                            then #logic_acc_v + $1
                            else #logic_acc_v)));


        LET new_logic_stall <-
          IF #bianchi_violation
          then $$false
          else (IF #logic_rsp_fire then $$false else (IF #logic_issue then $$true else #logic_stall_v));
        LET new_logic_req_valid <-
          IF #bianchi_violation
          then $$false
          else (IF #logic_rsp_fire
                then $$false
                else (IF #logic_issue then $$true else #logic_req_valid_v));

        LET new_logic_req_opcode : Bit OpcodeSz <-
          IF #logic_issue then #opcode else #logic_req_opcode_v;

        LET new_logic_req_payload : Bit WordSz <-
          IF #logic_issue then #lpayload32 else #logic_req_payload_v;

        LET new_logic_resp_valid <-
          IF #bianchi_violation
          then $$false
          else (IF #logic_rsp_fire then $$false else #logic_resp_valid_v);

        (* CSR telemetry: cycle and retired instruction counters. *)
        LET mcycle_lo_next : Bit WordSz <- #mcycle_lo_v + $1;
        LET mcycle_lo_wrap <- #mcycle_lo_next == $0;
        LET mcycle_hi_next : Bit WordSz <- IF #mcycle_lo_wrap then #mcycle_hi_v + $1 else #mcycle_hi_v;

        LET retire_this_step <-
          !#logic_rsp_pending && !#locality_violation && !#ptable_overflow_violation && !#high_value_locked && !#nfi_violation;
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
        Write "mstatus"        <- #new_mstatus;
        Write "mcycle_lo"      <- #mcycle_lo_next;
        Write "mcycle_hi"      <- #mcycle_hi_next;
        Write "minstret_lo"    <- #minstret_lo_inc;
        Write "minstret_hi"    <- #minstret_hi_next;
        Write "logic_req_valid"   <- #new_logic_req_valid;
        Write "logic_req_opcode"  <- #new_logic_req_opcode;
        Write "logic_req_payload" <- #new_logic_req_payload;
        Write "logic_resp_valid"  <- #new_logic_resp_valid;
        Write "logic_stall"       <- #new_logic_stall;
        Write "partition_ops"  <- #new_partition_ops;
        Write "mdl_ops"        <- #new_mdl_ops;
        Write "info_gain"      <- #new_info_gain;
        Write "mu_tensor"      <- #new_mu_tensor;
        Write "ptTable"        <- #new_pt_sizes;
        Write "pt_next_id"     <- #new_pt_next_id;
        Write "certified"      <- #new_certified;
        Write "wc_same_00"     <- #new_wc_same_00;
        Write "wc_diff_00"     <- #new_wc_diff_00;
        Write "wc_same_01"     <- #new_wc_same_01;
        Write "wc_diff_01"     <- #new_wc_diff_01;
        Write "wc_same_10"     <- #new_wc_same_10;
        Write "wc_diff_10"     <- #new_wc_diff_10;
        Write "wc_same_11"     <- #new_wc_same_11;
        Write "wc_diff_11"     <- #new_wc_diff_11;
        Retv


      (** Method to load a program word into instruction memory.
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

      with Method "getLogicReqValid" () : Bool :=
        Read v : Bool <- "logic_req_valid"; Ret #v

      with Method "getLogicReqOpcode" () : Bit OpcodeSz :=
        Read v : Bit OpcodeSz <- "logic_req_opcode"; Ret #v

      with Method "getLogicReqPayload" () : Bit WordSz :=
        Read v : Bit WordSz <- "logic_req_payload"; Ret #v

      with Method "setLogicResp" (arg : Struct LogicRespPort) : Void :=
        LET valid_v <- #arg!LogicRespPort@."valid";
        LET error_v <- #arg!LogicRespPort@."error";
        LET value_v <- #arg!LogicRespPort@."value";
        Write "logic_resp_valid" <- #valid_v;
        Write "logic_resp_error" <- #error_v;
        Write "logic_resp_value" <- #value_v;
        Retv

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
        Read logic_req_valid_v : Bool <- "logic_req_valid";
        Read logic_req_opcode_v : Bit OpcodeSz <- "logic_req_opcode";
        Read logic_req_payload_v : Bit WordSz <- "logic_req_payload";
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
        LET logic_req_opcode32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #logic_req_opcode_v;
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
          else (IF (#addr == $$(natToWord WordSz 56)) then (IF #logic_req_valid_v then $1 else $0)
          else (IF (#addr == $$(natToWord WordSz 60)) then #logic_req_opcode32
          else (IF (#addr == $$(natToWord WordSz 64)) then #logic_req_payload_v
          else (IF (#addr == $$(natToWord WordSz 68)) then #mu_tensor0
          else (IF (#addr == $$(natToWord WordSz 72)) then #mu_tensor1
          else (IF (#addr == $$(natToWord WordSz 76)) then #mu_tensor2
          else (IF (#addr == $$(natToWord WordSz 80)) then #mu_tensor3
          else (IF (#addr == $$(natToWord WordSz 84)) then (IF #bianchi_alarm_v then $1 else $0)
          else (IF (#addr == $$(natToWord WordSz 88)) then #pt_next_id32
          else (IF (#addr == $$(natToWord WordSz 92)) then #pt_size0 else $0)))))))))))))))))))))));
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
          (#addr == $$(natToWord WordSz 60)) ||
          (#addr == $$(natToWord WordSz 64)) ||
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
        Read logic_resp_valid_v : Bool <- "logic_resp_valid";
        Read logic_resp_error_v : Bool <- "logic_resp_error";
        Read logic_resp_value_v : Bit WordSz <- "logic_resp_value";
        Read active_module_v : Bit PTableIdxSz <- "active_module";
        Read trap_vector_v : Bit WordSz <- "trap_vector";
        Read bus_load_instr_addr_v : Bit MemAddrSz <- "bus_load_instr_addr";
        Read bus_load_instr_data_v : Bit InstrSz <- "bus_load_instr_data";
        Read bus_load_instr_kick_v : Bool <- "bus_load_instr_kick";
        LET addr <- #arg!APBBusWritePort@."addr";
        LET data <- #arg!APBBusWritePort@."data";
        LET wr_load_instr_addr <- #addr == $$(natToWord WordSz 128);
        LET wr_load_instr_data <- #addr == $$(natToWord WordSz 132);
        LET wr_load_instr_kick <- #addr == $$(natToWord WordSz 136);
        LET wr_set_logic_resp_valid <- #addr == $$(natToWord WordSz 140);
        LET wr_set_logic_resp_error <- #addr == $$(natToWord WordSz 144);
        LET wr_set_logic_resp_value <- #addr == $$(natToWord WordSz 148);
        LET wr_set_active_module <- #addr == $$(natToWord WordSz 152);
        LET wr_set_trap_vector <- #addr == $$(natToWord WordSz 156);
        LET wr_any <-
          #wr_load_instr_addr ||
          #wr_load_instr_data ||
          #wr_load_instr_kick ||
          #wr_set_logic_resp_valid ||
          #wr_set_logic_resp_error ||
          #wr_set_logic_resp_value ||
          #wr_set_active_module ||
          #wr_set_trap_vector;
        LET data_mem_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #data;
        LET data_instr : Bit InstrSz <- UniBit (Trunc InstrSz _) #data;
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
        LET next_logic_resp_valid <-
          IF #wr_set_logic_resp_valid then #data_nonzero else #logic_resp_valid_v;
        LET next_logic_resp_error <-
          IF #wr_set_logic_resp_error then #data_nonzero else #logic_resp_error_v;
        LET next_logic_resp_value : Bit WordSz <-
          IF #wr_set_logic_resp_value then #data else #logic_resp_value_v;
        LET next_active_module : Bit PTableIdxSz <-
          IF #wr_set_active_module
          then UniBit (Trunc PTableIdxSz _) #data
          else #active_module_v;
        LET next_trap_vector : Bit WordSz <-
          IF #wr_set_trap_vector then #data else #trap_vector_v;
        Write "imem" <- #next_imem;
        Write "bus_load_instr_addr" <- #next_load_instr_addr;
        Write "bus_load_instr_data" <- #next_load_instr_data;
        Write "bus_load_instr_kick" <- #next_load_instr_kick;
        Write "logic_resp_valid" <- #next_logic_resp_valid;
        Write "logic_resp_error" <- #next_logic_resp_error;
        Write "logic_resp_value" <- #next_logic_resp_value;
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
    }.

  (** Extraction targets *)
  Definition thieleCoreS := getModuleS thieleCore.
  Definition thieleCoreB := ModulesSToBModules thieleCoreS.

End ThieleCPU.

#[global] Hint Unfold thieleCore : ModuleDefs.
