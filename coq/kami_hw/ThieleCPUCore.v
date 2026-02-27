(** ThieleCPUCore.v — Complete Thiele CPU in Kami (26-instruction ISA).

    Implements the full ISA from VMStep.v:
      - Every instruction increments mu by its cost field (μ-monotonicity)
      - PC advances to PC+1 (sequential) or target (branch)
      - HALT latches the halted flag

    Instruction encoding: [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost

    Encoding conventions:
      XFER:      op_a = dst, op_b = src
      LOAD_IMM:  op_a = dst, op_b = immediate value
      LOAD:      op_a = dst, op_b = memory address
      STORE:     op_a = memory address, op_b = src register
      ADD/SUB:   op_a = dst, op_b[7:4] = rs1, op_b[3:0] = rs2
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


    Kami Vector notes: Vector K n stores 2^n elements, indexed by Bit n.
    So "regs" is Vector (Bit 32) 5 = 2^5 = 32 registers, indexed by Bit 5.
    And "mem" is Vector (Bit 32) 8 = 2^8 = 256 memory words, indexed by Bit 8.
    And "imem" is Vector (Bit 32) 8 = 2^8 = 256 instruction words.
    And "mu_tensor" is Vector (Bit 32) 4 = 2^4 = 16 tensor entries. *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
Require Import KamiHW.ThieleTypes.

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

  (** Stack pointer register index (r31) *)
  Definition SP_IDX : word RegIdxSz := WO~1~1~1~1~1.

  Definition thieleCore :=
    MODULE {
      (* Core registers matching VMState *)
      Register "pc"     : Bit WordSz <- Default
      with Register "mu"     : Bit WordSz <- Default
      with Register "err"    : Bool <- false
      with Register "halted" : Bool <- false
      with Register "regs"   : Vector (Bit WordSz) RegIdxSz  <- Default  (* 2^5=32 regs *)
      with Register "mem"    : Vector (Bit WordSz) MemAddrSz <- Default  (* 2^8=256 words *)
      with Register "imem"   : Vector (Bit InstrSz) MemAddrSz <- Default (* 2^8=256 instrs *)

      (* Diagnostic counters — needed for test parity with handwritten RTL *)
      with Register "partition_ops" : Bit WordSz <- Default
      with Register "mdl_ops"       : Bit WordSz <- Default
      with Register "info_gain"     : Bit WordSz <- Default

      (* Error code register — specific error condition identifier *)
      with Register "error_code"    : Bit WordSz <- Default

      (* In-core logic engine accumulator: deterministic certificate/logic state. *)
      with Register "logic_acc"     : Bit WordSz <- Default

      (* Explicit L-coprocessor request/response interface state (in-core ports). *)
      with Register "logic_req_valid"   : Bool <- false
      with Register "logic_req_opcode"  : Bit OpcodeSz <- Default
      with Register "logic_req_payload" : Bit WordSz <- Default
      with Register "logic_resp_valid"  : Bool <- false
      with Register "logic_resp_error"  : Bool <- false
      with Register "logic_resp_value"  : Bit WordSz <- Default

      (* μ-tensor: 4×4 flattened (16 entries) for revelation direction tracking *)
      with Register "mu_tensor"     : Vector (Bit WordSz) MuTensorIdxSz <- Default

      (* Partition table — bounded to PTableSz = 64 slots, matching NUM_MODULES in VMState and RTL.
         pt_sizes[id] = region_size for that module slot (0 = unallocated/invalid).
         pt_next_id is the next free module ID to assign; initialized to 1 to match
         empty_graph.pg_next_id = 1 from VMState.v. *)
      with Register "pt_sizes"      : Vector (Bit WordSz) PTableIdxSz <- Default
      with Register "pt_next_id"    : Bit WordSz <- PT_NEXT_ID_INIT

      (** The single step rule: fetch-decode-execute in one atomic action.
          This matches the Coq vm_step relation which is also atomic. *)
      with Rule "step" :=
        Read halted_v : Bool <- "halted";
        Assert !#halted_v;

        Read err_v : Bool <- "err";
        Assert !#err_v;

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
        Read logic_req_valid_v : Bool <- "logic_req_valid";
        Read logic_req_opcode_v : Bit OpcodeSz <- "logic_req_opcode";
        Read logic_req_payload_v : Bit WordSz <- "logic_req_payload";
        Read logic_resp_valid_v : Bool <- "logic_resp_valid";
        Read logic_resp_error_v : Bool <- "logic_resp_error";
        Read logic_resp_value_v : Bit WordSz <- "logic_resp_value";
        Read mu_tensor_v : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";
        Read pt_sizes_v   : Vector (Bit WordSz) PTableIdxSz <- "pt_sizes";
        Read pt_next_id_v : Bit WordSz <- "pt_next_id";

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

        (* Memory address from op_b *)
        LET mem_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #op_b;
        LET mem_addr_a : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #op_a;
        LET mem_val : Bit WordSz <- #mem_v@[#mem_addr];

        (* Partition-table indexed value probes for in-core PDISCOVER datapath *)
        LET pt_probe_idx : Bit PTableIdxSz <- UniBit (Trunc PTableIdxSz _) #op_b;
        LET pt_probe_size : Bit WordSz <- #pt_sizes_v@[#pt_probe_idx];

        (* JNEZ: target address from op_b zero-extended *)
        LET jnez_target : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;

        (* JUMP/CALL: target from {op_a, op_b} = 16-bit zero-extended *)
        LET jump_target_16 : Bit 16 <- {#op_a, #op_b};
        LET jump_target : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #jump_target_16;

        (* Stack pointer (r31) for CALL/RET *)
        LET sp_val : Bit WordSz <- #regs_v@[$$(SP_IDX)];
        LET sp_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_val;
        LET sp_inc : Bit WordSz <- #sp_val + $1;
        LET sp_dec : Bit WordSz <- #sp_val - $1;
        LET sp_dec_addr : Bit MemAddrSz <- UniBit (Trunc MemAddrSz _) #sp_dec;
        LET ret_pc : Bit WordSz <- #mem_v@[#sp_dec_addr];

        (* Execute: compute all possible results *)
        LET add_result : Bit WordSz <- #rs1_val + #rs2_val;
        LET sub_result : Bit WordSz <- #rs1_val - #rs2_val;
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
        LET chsh_x1 <- #op_a > $$(WO~0~0~0~0~0~0~0~1);
        LET chsh_cert_missing <- (#chsh_x1) && (#tensor_total == $0);
        LET chsh_bits_bad <- #chsh_outcomes_bad || #chsh_cert_missing;

        (* L-coprocessor request/response interface semantics *)
        LET is_logic_op <- (#opcode == $$(OP_LASSERT)) || (#opcode == $$(OP_LJOIN));
        LET lpayload16 : Bit 16 <- {#op_a, #op_b};
        LET lpayload32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #lpayload16;
        LET logic_rsp_pending <- #logic_req_valid_v && !#logic_resp_valid_v;
        LET logic_rsp_fire <- #logic_req_valid_v && #logic_resp_valid_v;
        LET logic_issue <- #is_logic_op && !#logic_req_valid_v;

        (* REVEAL: tensor index from op_a[3:0] *)
        LET tensor_idx : Bit MuTensorIdxSz <- UniBit (Trunc MuTensorIdxSz _) #op_a;
        LET tensor_old : Bit WordSz <- #mu_tensor_v@[#tensor_idx];
        LET tensor_new_val : Bit WordSz <- #tensor_old + #cost32;

        (* ============================================================
           Determine new PC
           ============================================================ *)
        LET new_pc : Bit WordSz <-
          IF (#bianchi_violation || #logic_rsp_pending)
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
                                        else #pc_plus_1)))));

        (* Pre-compute XOR_SWAP result: write both dst<-src and src<-dst *)
        LET swap_regs : Vector (Bit WordSz) RegIdxSz <-
          (#regs_v@[#dst_idx <- #src_val])@[#src_idx <- #dst_val];

        (* ============================================================
           Determine new register file
           ============================================================ *)
        LET new_regs : Vector (Bit WordSz) RegIdxSz <-
          IF #bianchi_violation
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
                then #regs_v@[#dst_idx <- #mem_val]
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
          else #regs_v))))))))))));

        (* ============================================================
           Determine new memory
           ============================================================ *)
        LET new_mem : Vector (Bit WordSz) MemAddrSz <-
          IF #bianchi_violation
          then #mem_v
          else (IF (#opcode == $$(OP_STORE))
          then #mem_v@[#mem_addr_a <- #src_val]
          else (IF (#opcode == $$(OP_CALL))
                then #mem_v@[#sp_addr <- #pc_plus_1]
          else #mem_v));

        (* Determine halted state *)
        LET new_halted <- #bianchi_violation || (#opcode == $$(OP_HALT));

        (* Determine error state: protocol errors set err; logic errors come from coprocessor response. *)
        LET logic_resp_fail <- #logic_rsp_fire && #logic_resp_error_v;
        LET new_err <- ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad) || #logic_resp_fail;

        (* Determine error code *)
        LET new_error_code : Bit WordSz <-
          IF #bianchi_violation
          then $$(ERR_BIANCHI_VAL)
          else (IF #logic_resp_fail
                then $$(ERR_LOGIC_VAL)
                else (IF ((#opcode == $$(OP_CHSH_TRIAL)) && #chsh_bits_bad)
                      then $$(ERR_CHSH_VAL)
                      else #error_code_v));

        (* Determine new mu — only charge if not a bianchi violation.
           ORACLE_HALTS (0x10) always charges 1,000,000 regardless of cost field. *)
        LET final_mu : Bit WordSz <-
          IF #bianchi_violation
          then #mu_v
          else (IF #logic_rsp_pending
                then #mu_v
                else (IF (#opcode == $$(OP_ORACLE_HALTS))
                      then #mu_v + $1000000
                      else (IF ((#opcode == $$(OP_CHSH_TRIAL)) && (#chsh_x1))
                            then #new_mu + $$(CHSH_X1_SURCHARGE)
                            else #new_mu)));

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
        LET next_after_pnew : Bit WordSz <- #pt_next_id_v + $1;

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
        LET next_after_psplit : Bit WordSz <- #pt_next_id_v + $2;

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
        LET next_after_pmerge : Bit WordSz <- #pt_next_id_v + $1;

        (* Select partition table update based on opcode *)
        LET new_pt_sizes : Vector (Bit WordSz) PTableIdxSz <-
          IF #bianchi_violation
          then #pt_sizes_v
          else (IF (#opcode == $$(OP_PNEW))
                then #pt_after_pnew
                else (IF (#opcode == $$(OP_PSPLIT))
                      then #pt_after_psplit
                      else (IF (#opcode == $$(OP_PMERGE))
                            then #pt_after_pmerge
                            else #pt_sizes_v)));

        LET new_pt_next_id : Bit WordSz <-
          IF #bianchi_violation
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

        (* Zero-extend op_b to 32 bits for info_gain increment *)
        LET op_b_32 : Bit WordSz <- UniBit (ZeroExtendTrunc _ _) #op_b;
        LET is_info_gain_op <-
          (#opcode == $$(OP_PDISCOVER)) || (#opcode == $$(OP_EMIT));
        LET new_info_gain : Bit WordSz <-
          IF (#is_info_gain_op && !#bianchi_violation)
          then #info_gain_v + #op_b_32
          else #info_gain_v;

        (* ============================================================
           μ-tensor update (REVEAL charges tensor entry)
           ============================================================ *)
        LET new_mu_tensor : Vector (Bit WordSz) MuTensorIdxSz <-
          IF ((#opcode == $$(OP_REVEAL)) && !#bianchi_violation)
          then #mu_tensor_v@[#tensor_idx <- #tensor_new_val]
          else #mu_tensor_v;

        LET new_logic_acc : Bit WordSz <-
          IF #bianchi_violation
          then #logic_acc_v
          else (IF #logic_rsp_fire
                then #logic_acc_v + #logic_resp_value_v
                else (IF (#opcode == $$(OP_ORACLE_HALTS))
                      then #logic_acc_v + $1
                      else #logic_acc_v));

        LET new_logic_req_valid <-
          IF #bianchi_violation
          then #logic_req_valid_v
          else (IF #logic_rsp_fire
                then $$false
                else (IF #logic_issue then $$true else #logic_req_valid_v));

        LET new_logic_req_opcode : Bit OpcodeSz <-
          IF #logic_issue then #opcode else #logic_req_opcode_v;

        LET new_logic_req_payload : Bit WordSz <-
          IF #logic_issue then #lpayload32 else #logic_req_payload_v;

        LET new_logic_resp_valid <-
          IF #bianchi_violation
          then #logic_resp_valid_v
          else (IF #logic_rsp_fire then $$false else #logic_resp_valid_v);

        (* Write back *)
        Write "pc"             <- #new_pc;
        Write "mu"             <- #final_mu;
        Write "regs"           <- #new_regs;
        Write "mem"            <- #new_mem;
        Write "halted"         <- #new_halted;
        Write "err"            <- #new_err;
        Write "error_code"     <- #new_error_code;
        Write "logic_acc"      <- #new_logic_acc;
        Write "logic_req_valid"   <- #new_logic_req_valid;
        Write "logic_req_opcode"  <- #new_logic_req_opcode;
        Write "logic_req_payload" <- #new_logic_req_payload;
        Write "logic_resp_valid"  <- #new_logic_resp_valid;
        Write "partition_ops"  <- #new_partition_ops;
        Write "mdl_ops"        <- #new_mdl_ops;
        Write "info_gain"      <- #new_info_gain;
        Write "mu_tensor"      <- #new_mu_tensor;
        Write "pt_sizes"       <- #new_pt_sizes;
        Write "pt_next_id"     <- #new_pt_next_id;
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

      with Method "getPartitionOps" () : Bit WordSz :=
        Read v : Bit WordSz <- "partition_ops"; Ret #v

      with Method "getMdlOps" () : Bit WordSz :=
        Read v : Bit WordSz <- "mdl_ops"; Ret #v

      with Method "getInfoGain" () : Bit WordSz :=
        Read v : Bit WordSz <- "info_gain"; Ret #v

      with Method "getErrorCode" () : Bit WordSz :=
        Read v : Bit WordSz <- "error_code"; Ret #v

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
        Read v : Bit WordSz <- "pt_next_id"; Ret #v

      with Method "getPtSize" (idx : Bit PTableIdxSz) : Bit WordSz :=
        Read t : Vector (Bit WordSz) PTableIdxSz <- "pt_sizes";
        Ret #t@[#idx]
    }.

  (** Extraction targets *)
  Definition thieleCoreS := getModuleS thieleCore.
  Definition thieleCoreB := ModulesSToBModules thieleCoreS.

End ThieleCPU.

#[global] Hint Unfold thieleCore : ModuleDefs.
