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

      (* μ-tensor: 4×4 flattened (16 entries) for revelation direction tracking *)
      with Register "mu_tensor"     : Vector (Bit WordSz) MuTensorIdxSz <- Default

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
        Read mu_tensor_v : Vector (Bit WordSz) MuTensorIdxSz <- "mu_tensor";

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

        (* CHSH_TRIAL: validate bits are in {0,1} *)
        LET chsh_x : Bit 8 <- #op_a;
        LET chsh_y : Bit 8 <- #op_b;
        LET chsh_bits_bad <- (#chsh_x > $$(WO~0~0~0~0~0~0~0~1)) || (#chsh_y > $$(WO~0~0~0~0~0~0~0~1));

        (* REVEAL: tensor index from op_a[3:0] *)
        LET tensor_idx : Bit MuTensorIdxSz <- UniBit (Trunc MuTensorIdxSz _) #op_a;
        LET tensor_old : Bit WordSz <- #mu_tensor_v@[#tensor_idx];
        LET tensor_new_val : Bit WordSz <- #tensor_old + #cost32;

        (* ============================================================
           Determine new PC
           ============================================================ *)
        LET new_pc : Bit WordSz <-
          IF #bianchi_violation
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
          else #regs_v)))))))))));

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

        (* Determine error state: latch (once set, stays set) *)
        LET new_err <- #chsh_bits_bad;

        (* Determine error code *)
        LET new_error_code : Bit WordSz <-
          IF #bianchi_violation
          then $$(ERR_BIANCHI_VAL)
          else (IF #chsh_bits_bad
                then $$(ERR_CHSH_VAL)
                else #error_code_v);

        (* Determine new mu — only charge if not a bianchi violation *)
        LET final_mu : Bit WordSz <-
          IF #bianchi_violation then #mu_v else #new_mu;

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

        (* Write back *)
        Write "pc"             <- #new_pc;
        Write "mu"             <- #final_mu;
        Write "regs"           <- #new_regs;
        Write "mem"            <- #new_mem;
        Write "halted"         <- #new_halted;
        Write "err"            <- #new_err;
        Write "error_code"     <- #new_error_code;
        Write "partition_ops"  <- #new_partition_ops;
        Write "mdl_ops"        <- #new_mdl_ops;
        Write "info_gain"      <- #new_info_gain;
        Write "mu_tensor"      <- #new_mu_tensor;
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
    }.

  (** Extraction targets *)
  Definition thieleCoreS := getModuleS thieleCore.
  Definition thieleCoreB := ModulesSToBModules thieleCoreS.

End ThieleCPU.

#[global] Hint Unfold thieleCore : ModuleDefs.
