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

  (** Stack pointer register index (r31) *)
  Definition SP_IDX : word RegIdxSz := WO~1~1~1~1~1.

  (** Physical locality helper: address must stay within active partition size. *)
  Definition check_bounds
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (active_partition_size : Expr ty (SyntaxKind (Bit WordSz)))
    : Expr ty (SyntaxKind Bool) :=
    BinBitBool (Lt WordSz) (UniBit (ZeroExtendTrunc _ _) addr) active_partition_size.


  Fixpoint mem_read_tree_aux
           {ty}
           (depth base : nat)
           (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
           (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Bit WordSz)) :=
    match depth with
    | O => ReadIndex (@Const ty (Bit MemAddrSz) (natToWord MemAddrSz base)) memv
    | S d' =>
        let half := Nat.pow 2 d' in
        let pivot := base + half in
        ITE (BinBitBool (Lt MemAddrSz) addr (@Const ty (Bit MemAddrSz) (natToWord MemAddrSz pivot)))
            (mem_read_tree_aux d' base addr memv)
            (mem_read_tree_aux d' pivot addr memv)
    end.

  Definition read_mem
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Bit WordSz)) :=
    mem_read_tree_aux MemAddrSz 0 addr memv.

  Fixpoint mem_write_tree_aux
           {ty}
           (depth base : nat)
           (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
           (val : Expr ty (SyntaxKind (Bit WordSz)))
           (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)) :=
    match depth with
    | O => UpdateVector memv (@Const ty (Bit MemAddrSz) (natToWord MemAddrSz base)) val
    | S d' =>
        let half := Nat.pow 2 d' in
        let pivot := base + half in
        ITE (BinBitBool (Lt MemAddrSz) addr (@Const ty (Bit MemAddrSz) (natToWord MemAddrSz pivot)))
            (mem_write_tree_aux d' base addr val memv)
            (mem_write_tree_aux d' pivot addr val memv)
    end.

  Definition write_mem
             {ty}
             (addr : Expr ty (SyntaxKind (Bit MemAddrSz)))
             (val : Expr ty (SyntaxKind (Bit WordSz)))
             (memv : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)))
    : Expr ty (SyntaxKind (Vector (Bit WordSz) MemAddrSz)) :=
    mem_write_tree_aux MemAddrSz 0 addr val memv.

  Definition thieleCore :=
    MODULE {
      (* Core registers matching VMState *)
      Register "pc"     : Bit WordSz <- Default
      with Register "mu"     : Bit WordSz <- Default
      with Register "err"    : Bool <- false
      with Register "halted" : Bool <- false
      with Register "reg0"    : Bit WordSz <- Default
      with Register "reg1"    : Bit WordSz <- Default
      with Register "reg2"    : Bit WordSz <- Default
      with Register "reg3"    : Bit WordSz <- Default
      with Register "reg4"    : Bit WordSz <- Default
      with Register "reg5"    : Bit WordSz <- Default
      with Register "reg6"    : Bit WordSz <- Default
      with Register "reg7"    : Bit WordSz <- Default
      with Register "reg8"    : Bit WordSz <- Default
      with Register "reg9"    : Bit WordSz <- Default
      with Register "reg10"    : Bit WordSz <- Default
      with Register "reg11"    : Bit WordSz <- Default
      with Register "reg12"    : Bit WordSz <- Default
      with Register "reg13"    : Bit WordSz <- Default
      with Register "reg14"    : Bit WordSz <- Default
      with Register "reg15"    : Bit WordSz <- Default
      with Register "reg16"    : Bit WordSz <- Default
      with Register "reg17"    : Bit WordSz <- Default
      with Register "reg18"    : Bit WordSz <- Default
      with Register "reg19"    : Bit WordSz <- Default
      with Register "reg20"    : Bit WordSz <- Default
      with Register "reg21"    : Bit WordSz <- Default
      with Register "reg22"    : Bit WordSz <- Default
      with Register "reg23"    : Bit WordSz <- Default
      with Register "reg24"    : Bit WordSz <- Default
      with Register "reg25"    : Bit WordSz <- Default
      with Register "reg26"    : Bit WordSz <- Default
      with Register "reg27"    : Bit WordSz <- Default
      with Register "reg28"    : Bit WordSz <- Default
      with Register "reg29"    : Bit WordSz <- Default
      with Register "reg30"    : Bit WordSz <- Default
      with Register "reg31"    : Bit WordSz <- Default
      with Register "mem0"  : Bit WordSz <- Default
      with Register "mem1"  : Bit WordSz <- Default
      with Register "mem2"  : Bit WordSz <- Default
      with Register "mem3"  : Bit WordSz <- Default
      with Register "mem4"  : Bit WordSz <- Default
      with Register "mem5"  : Bit WordSz <- Default
      with Register "mem6"  : Bit WordSz <- Default
      with Register "mem7"  : Bit WordSz <- Default
      with Register "mem8"  : Bit WordSz <- Default
      with Register "mem9"  : Bit WordSz <- Default
      with Register "mem10"  : Bit WordSz <- Default
      with Register "mem11"  : Bit WordSz <- Default
      with Register "mem12"  : Bit WordSz <- Default
      with Register "mem13"  : Bit WordSz <- Default
      with Register "mem14"  : Bit WordSz <- Default
      with Register "mem15"  : Bit WordSz <- Default
      with Register "mem16"  : Bit WordSz <- Default
      with Register "mem17"  : Bit WordSz <- Default
      with Register "mem18"  : Bit WordSz <- Default
      with Register "mem19"  : Bit WordSz <- Default
      with Register "mem20"  : Bit WordSz <- Default
      with Register "mem21"  : Bit WordSz <- Default
      with Register "mem22"  : Bit WordSz <- Default
      with Register "mem23"  : Bit WordSz <- Default
      with Register "mem24"  : Bit WordSz <- Default
      with Register "mem25"  : Bit WordSz <- Default
      with Register "mem26"  : Bit WordSz <- Default
      with Register "mem27"  : Bit WordSz <- Default
      with Register "mem28"  : Bit WordSz <- Default
      with Register "mem29"  : Bit WordSz <- Default
      with Register "mem30"  : Bit WordSz <- Default
      with Register "mem31"  : Bit WordSz <- Default
      with Register "mem32"  : Bit WordSz <- Default
      with Register "mem33"  : Bit WordSz <- Default
      with Register "mem34"  : Bit WordSz <- Default
      with Register "mem35"  : Bit WordSz <- Default
      with Register "mem36"  : Bit WordSz <- Default
      with Register "mem37"  : Bit WordSz <- Default
      with Register "mem38"  : Bit WordSz <- Default
      with Register "mem39"  : Bit WordSz <- Default
      with Register "mem40"  : Bit WordSz <- Default
      with Register "mem41"  : Bit WordSz <- Default
      with Register "mem42"  : Bit WordSz <- Default
      with Register "mem43"  : Bit WordSz <- Default
      with Register "mem44"  : Bit WordSz <- Default
      with Register "mem45"  : Bit WordSz <- Default
      with Register "mem46"  : Bit WordSz <- Default
      with Register "mem47"  : Bit WordSz <- Default
      with Register "mem48"  : Bit WordSz <- Default
      with Register "mem49"  : Bit WordSz <- Default
      with Register "mem50"  : Bit WordSz <- Default
      with Register "mem51"  : Bit WordSz <- Default
      with Register "mem52"  : Bit WordSz <- Default
      with Register "mem53"  : Bit WordSz <- Default
      with Register "mem54"  : Bit WordSz <- Default
      with Register "mem55"  : Bit WordSz <- Default
      with Register "mem56"  : Bit WordSz <- Default
      with Register "mem57"  : Bit WordSz <- Default
      with Register "mem58"  : Bit WordSz <- Default
      with Register "mem59"  : Bit WordSz <- Default
      with Register "mem60"  : Bit WordSz <- Default
      with Register "mem61"  : Bit WordSz <- Default
      with Register "mem62"  : Bit WordSz <- Default
      with Register "mem63"  : Bit WordSz <- Default
      with Register "mem64"  : Bit WordSz <- Default
      with Register "mem65"  : Bit WordSz <- Default
      with Register "mem66"  : Bit WordSz <- Default
      with Register "mem67"  : Bit WordSz <- Default
      with Register "mem68"  : Bit WordSz <- Default
      with Register "mem69"  : Bit WordSz <- Default
      with Register "mem70"  : Bit WordSz <- Default
      with Register "mem71"  : Bit WordSz <- Default
      with Register "mem72"  : Bit WordSz <- Default
      with Register "mem73"  : Bit WordSz <- Default
      with Register "mem74"  : Bit WordSz <- Default
      with Register "mem75"  : Bit WordSz <- Default
      with Register "mem76"  : Bit WordSz <- Default
      with Register "mem77"  : Bit WordSz <- Default
      with Register "mem78"  : Bit WordSz <- Default
      with Register "mem79"  : Bit WordSz <- Default
      with Register "mem80"  : Bit WordSz <- Default
      with Register "mem81"  : Bit WordSz <- Default
      with Register "mem82"  : Bit WordSz <- Default
      with Register "mem83"  : Bit WordSz <- Default
      with Register "mem84"  : Bit WordSz <- Default
      with Register "mem85"  : Bit WordSz <- Default
      with Register "mem86"  : Bit WordSz <- Default
      with Register "mem87"  : Bit WordSz <- Default
      with Register "mem88"  : Bit WordSz <- Default
      with Register "mem89"  : Bit WordSz <- Default
      with Register "mem90"  : Bit WordSz <- Default
      with Register "mem91"  : Bit WordSz <- Default
      with Register "mem92"  : Bit WordSz <- Default
      with Register "mem93"  : Bit WordSz <- Default
      with Register "mem94"  : Bit WordSz <- Default
      with Register "mem95"  : Bit WordSz <- Default
      with Register "mem96"  : Bit WordSz <- Default
      with Register "mem97"  : Bit WordSz <- Default
      with Register "mem98"  : Bit WordSz <- Default
      with Register "mem99"  : Bit WordSz <- Default
      with Register "mem100"  : Bit WordSz <- Default
      with Register "mem101"  : Bit WordSz <- Default
      with Register "mem102"  : Bit WordSz <- Default
      with Register "mem103"  : Bit WordSz <- Default
      with Register "mem104"  : Bit WordSz <- Default
      with Register "mem105"  : Bit WordSz <- Default
      with Register "mem106"  : Bit WordSz <- Default
      with Register "mem107"  : Bit WordSz <- Default
      with Register "mem108"  : Bit WordSz <- Default
      with Register "mem109"  : Bit WordSz <- Default
      with Register "mem110"  : Bit WordSz <- Default
      with Register "mem111"  : Bit WordSz <- Default
      with Register "mem112"  : Bit WordSz <- Default
      with Register "mem113"  : Bit WordSz <- Default
      with Register "mem114"  : Bit WordSz <- Default
      with Register "mem115"  : Bit WordSz <- Default
      with Register "mem116"  : Bit WordSz <- Default
      with Register "mem117"  : Bit WordSz <- Default
      with Register "mem118"  : Bit WordSz <- Default
      with Register "mem119"  : Bit WordSz <- Default
      with Register "mem120"  : Bit WordSz <- Default
      with Register "mem121"  : Bit WordSz <- Default
      with Register "mem122"  : Bit WordSz <- Default
      with Register "mem123"  : Bit WordSz <- Default
      with Register "mem124"  : Bit WordSz <- Default
      with Register "mem125"  : Bit WordSz <- Default
      with Register "mem126"  : Bit WordSz <- Default
      with Register "mem127"  : Bit WordSz <- Default
      with Register "mem128"  : Bit WordSz <- Default
      with Register "mem129"  : Bit WordSz <- Default
      with Register "mem130"  : Bit WordSz <- Default
      with Register "mem131"  : Bit WordSz <- Default
      with Register "mem132"  : Bit WordSz <- Default
      with Register "mem133"  : Bit WordSz <- Default
      with Register "mem134"  : Bit WordSz <- Default
      with Register "mem135"  : Bit WordSz <- Default
      with Register "mem136"  : Bit WordSz <- Default
      with Register "mem137"  : Bit WordSz <- Default
      with Register "mem138"  : Bit WordSz <- Default
      with Register "mem139"  : Bit WordSz <- Default
      with Register "mem140"  : Bit WordSz <- Default
      with Register "mem141"  : Bit WordSz <- Default
      with Register "mem142"  : Bit WordSz <- Default
      with Register "mem143"  : Bit WordSz <- Default
      with Register "mem144"  : Bit WordSz <- Default
      with Register "mem145"  : Bit WordSz <- Default
      with Register "mem146"  : Bit WordSz <- Default
      with Register "mem147"  : Bit WordSz <- Default
      with Register "mem148"  : Bit WordSz <- Default
      with Register "mem149"  : Bit WordSz <- Default
      with Register "mem150"  : Bit WordSz <- Default
      with Register "mem151"  : Bit WordSz <- Default
      with Register "mem152"  : Bit WordSz <- Default
      with Register "mem153"  : Bit WordSz <- Default
      with Register "mem154"  : Bit WordSz <- Default
      with Register "mem155"  : Bit WordSz <- Default
      with Register "mem156"  : Bit WordSz <- Default
      with Register "mem157"  : Bit WordSz <- Default
      with Register "mem158"  : Bit WordSz <- Default
      with Register "mem159"  : Bit WordSz <- Default
      with Register "mem160"  : Bit WordSz <- Default
      with Register "mem161"  : Bit WordSz <- Default
      with Register "mem162"  : Bit WordSz <- Default
      with Register "mem163"  : Bit WordSz <- Default
      with Register "mem164"  : Bit WordSz <- Default
      with Register "mem165"  : Bit WordSz <- Default
      with Register "mem166"  : Bit WordSz <- Default
      with Register "mem167"  : Bit WordSz <- Default
      with Register "mem168"  : Bit WordSz <- Default
      with Register "mem169"  : Bit WordSz <- Default
      with Register "mem170"  : Bit WordSz <- Default
      with Register "mem171"  : Bit WordSz <- Default
      with Register "mem172"  : Bit WordSz <- Default
      with Register "mem173"  : Bit WordSz <- Default
      with Register "mem174"  : Bit WordSz <- Default
      with Register "mem175"  : Bit WordSz <- Default
      with Register "mem176"  : Bit WordSz <- Default
      with Register "mem177"  : Bit WordSz <- Default
      with Register "mem178"  : Bit WordSz <- Default
      with Register "mem179"  : Bit WordSz <- Default
      with Register "mem180"  : Bit WordSz <- Default
      with Register "mem181"  : Bit WordSz <- Default
      with Register "mem182"  : Bit WordSz <- Default
      with Register "mem183"  : Bit WordSz <- Default
      with Register "mem184"  : Bit WordSz <- Default
      with Register "mem185"  : Bit WordSz <- Default
      with Register "mem186"  : Bit WordSz <- Default
      with Register "mem187"  : Bit WordSz <- Default
      with Register "mem188"  : Bit WordSz <- Default
      with Register "mem189"  : Bit WordSz <- Default
      with Register "mem190"  : Bit WordSz <- Default
      with Register "mem191"  : Bit WordSz <- Default
      with Register "mem192"  : Bit WordSz <- Default
      with Register "mem193"  : Bit WordSz <- Default
      with Register "mem194"  : Bit WordSz <- Default
      with Register "mem195"  : Bit WordSz <- Default
      with Register "mem196"  : Bit WordSz <- Default
      with Register "mem197"  : Bit WordSz <- Default
      with Register "mem198"  : Bit WordSz <- Default
      with Register "mem199"  : Bit WordSz <- Default
      with Register "mem200"  : Bit WordSz <- Default
      with Register "mem201"  : Bit WordSz <- Default
      with Register "mem202"  : Bit WordSz <- Default
      with Register "mem203"  : Bit WordSz <- Default
      with Register "mem204"  : Bit WordSz <- Default
      with Register "mem205"  : Bit WordSz <- Default
      with Register "mem206"  : Bit WordSz <- Default
      with Register "mem207"  : Bit WordSz <- Default
      with Register "mem208"  : Bit WordSz <- Default
      with Register "mem209"  : Bit WordSz <- Default
      with Register "mem210"  : Bit WordSz <- Default
      with Register "mem211"  : Bit WordSz <- Default
      with Register "mem212"  : Bit WordSz <- Default
      with Register "mem213"  : Bit WordSz <- Default
      with Register "mem214"  : Bit WordSz <- Default
      with Register "mem215"  : Bit WordSz <- Default
      with Register "mem216"  : Bit WordSz <- Default
      with Register "mem217"  : Bit WordSz <- Default
      with Register "mem218"  : Bit WordSz <- Default
      with Register "mem219"  : Bit WordSz <- Default
      with Register "mem220"  : Bit WordSz <- Default
      with Register "mem221"  : Bit WordSz <- Default
      with Register "mem222"  : Bit WordSz <- Default
      with Register "mem223"  : Bit WordSz <- Default
      with Register "mem224"  : Bit WordSz <- Default
      with Register "mem225"  : Bit WordSz <- Default
      with Register "mem226"  : Bit WordSz <- Default
      with Register "mem227"  : Bit WordSz <- Default
      with Register "mem228"  : Bit WordSz <- Default
      with Register "mem229"  : Bit WordSz <- Default
      with Register "mem230"  : Bit WordSz <- Default
      with Register "mem231"  : Bit WordSz <- Default
      with Register "mem232"  : Bit WordSz <- Default
      with Register "mem233"  : Bit WordSz <- Default
      with Register "mem234"  : Bit WordSz <- Default
      with Register "mem235"  : Bit WordSz <- Default
      with Register "mem236"  : Bit WordSz <- Default
      with Register "mem237"  : Bit WordSz <- Default
      with Register "mem238"  : Bit WordSz <- Default
      with Register "mem239"  : Bit WordSz <- Default
      with Register "mem240"  : Bit WordSz <- Default
      with Register "mem241"  : Bit WordSz <- Default
      with Register "mem242"  : Bit WordSz <- Default
      with Register "mem243"  : Bit WordSz <- Default
      with Register "mem244"  : Bit WordSz <- Default
      with Register "mem245"  : Bit WordSz <- Default
      with Register "mem246"  : Bit WordSz <- Default
      with Register "mem247"  : Bit WordSz <- Default
      with Register "mem248"  : Bit WordSz <- Default
      with Register "mem249"  : Bit WordSz <- Default
      with Register "mem250"  : Bit WordSz <- Default
      with Register "mem251"  : Bit WordSz <- Default
      with Register "mem252"  : Bit WordSz <- Default
      with Register "mem253"  : Bit WordSz <- Default
      with Register "mem254"  : Bit WordSz <- Default
      with Register "mem255"  : Bit WordSz <- Default
      with Register "imem"   : Vector (Bit InstrSz) MemAddrSz <- Default (* 2^8=256 instrs *)

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

      (* μ-tensor: 4×4 flattened (16 entries) for revelation direction tracking *)
      with Register "mu_tensor"     : Vector (Bit WordSz) MuTensorIdxSz <- Default

      (* Partition table — bounded to PTableSz = 64 slots, matching NUM_MODULES in VMState and RTL.
         pt_sizes[id] = region_size for that module slot (0 = unallocated/invalid).
         pt_next_id is the next free module ID to assign; initialized to 1 to match
         empty_graph.pg_next_id = 1 from VMState.v. *)
      with Register "pt0"      : Bit WordSz <- Default
      with Register "pt1"      : Bit WordSz <- Default
      with Register "pt2"      : Bit WordSz <- Default
      with Register "pt3"      : Bit WordSz <- Default
      with Register "pt4"      : Bit WordSz <- Default
      with Register "pt5"      : Bit WordSz <- Default
      with Register "pt6"      : Bit WordSz <- Default
      with Register "pt7"      : Bit WordSz <- Default
      with Register "pt8"      : Bit WordSz <- Default
      with Register "pt9"      : Bit WordSz <- Default
      with Register "pt10"     : Bit WordSz <- Default
      with Register "pt11"     : Bit WordSz <- Default
      with Register "pt12"     : Bit WordSz <- Default
      with Register "pt13"     : Bit WordSz <- Default
      with Register "pt14"     : Bit WordSz <- Default
      with Register "pt15"     : Bit WordSz <- Default
      with Register "pt_next_id"    : Bit WordSz <- PT_NEXT_ID_INIT

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
        Read reg0_v : Bit WordSz <- "reg0";
        Read reg1_v : Bit WordSz <- "reg1";
        Read reg2_v : Bit WordSz <- "reg2";
        Read reg3_v : Bit WordSz <- "reg3";
        Read reg4_v : Bit WordSz <- "reg4";
        Read reg5_v : Bit WordSz <- "reg5";
        Read reg6_v : Bit WordSz <- "reg6";
        Read reg7_v : Bit WordSz <- "reg7";
        Read reg8_v : Bit WordSz <- "reg8";
        Read reg9_v : Bit WordSz <- "reg9";
        Read reg10_v : Bit WordSz <- "reg10";
        Read reg11_v : Bit WordSz <- "reg11";
        Read reg12_v : Bit WordSz <- "reg12";
        Read reg13_v : Bit WordSz <- "reg13";
        Read reg14_v : Bit WordSz <- "reg14";
        Read reg15_v : Bit WordSz <- "reg15";
        Read reg16_v : Bit WordSz <- "reg16";
        Read reg17_v : Bit WordSz <- "reg17";
        Read reg18_v : Bit WordSz <- "reg18";
        Read reg19_v : Bit WordSz <- "reg19";
        Read reg20_v : Bit WordSz <- "reg20";
        Read reg21_v : Bit WordSz <- "reg21";
        Read reg22_v : Bit WordSz <- "reg22";
        Read reg23_v : Bit WordSz <- "reg23";
        Read reg24_v : Bit WordSz <- "reg24";
        Read reg25_v : Bit WordSz <- "reg25";
        Read reg26_v : Bit WordSz <- "reg26";
        Read reg27_v : Bit WordSz <- "reg27";
        Read reg28_v : Bit WordSz <- "reg28";
        Read reg29_v : Bit WordSz <- "reg29";
        Read reg30_v : Bit WordSz <- "reg30";
        Read reg31_v : Bit WordSz <- "reg31";
        Read mem0_v : Bit WordSz <- "mem0";
        Read mem1_v : Bit WordSz <- "mem1";
        Read mem2_v : Bit WordSz <- "mem2";
        Read mem3_v : Bit WordSz <- "mem3";
        Read mem4_v : Bit WordSz <- "mem4";
        Read mem5_v : Bit WordSz <- "mem5";
        Read mem6_v : Bit WordSz <- "mem6";
        Read mem7_v : Bit WordSz <- "mem7";
        Read mem8_v : Bit WordSz <- "mem8";
        Read mem9_v : Bit WordSz <- "mem9";
        Read mem10_v : Bit WordSz <- "mem10";
        Read mem11_v : Bit WordSz <- "mem11";
        Read mem12_v : Bit WordSz <- "mem12";
        Read mem13_v : Bit WordSz <- "mem13";
        Read mem14_v : Bit WordSz <- "mem14";
        Read mem15_v : Bit WordSz <- "mem15";
        Read mem16_v : Bit WordSz <- "mem16";
        Read mem17_v : Bit WordSz <- "mem17";
        Read mem18_v : Bit WordSz <- "mem18";
        Read mem19_v : Bit WordSz <- "mem19";
        Read mem20_v : Bit WordSz <- "mem20";
        Read mem21_v : Bit WordSz <- "mem21";
        Read mem22_v : Bit WordSz <- "mem22";
        Read mem23_v : Bit WordSz <- "mem23";
        Read mem24_v : Bit WordSz <- "mem24";
        Read mem25_v : Bit WordSz <- "mem25";
        Read mem26_v : Bit WordSz <- "mem26";
        Read mem27_v : Bit WordSz <- "mem27";
        Read mem28_v : Bit WordSz <- "mem28";
        Read mem29_v : Bit WordSz <- "mem29";
        Read mem30_v : Bit WordSz <- "mem30";
        Read mem31_v : Bit WordSz <- "mem31";
        Read mem32_v : Bit WordSz <- "mem32";
        Read mem33_v : Bit WordSz <- "mem33";
        Read mem34_v : Bit WordSz <- "mem34";
        Read mem35_v : Bit WordSz <- "mem35";
        Read mem36_v : Bit WordSz <- "mem36";
        Read mem37_v : Bit WordSz <- "mem37";
        Read mem38_v : Bit WordSz <- "mem38";
        Read mem39_v : Bit WordSz <- "mem39";
        Read mem40_v : Bit WordSz <- "mem40";
        Read mem41_v : Bit WordSz <- "mem41";
        Read mem42_v : Bit WordSz <- "mem42";
        Read mem43_v : Bit WordSz <- "mem43";
        Read mem44_v : Bit WordSz <- "mem44";
        Read mem45_v : Bit WordSz <- "mem45";
        Read mem46_v : Bit WordSz <- "mem46";
        Read mem47_v : Bit WordSz <- "mem47";
        Read mem48_v : Bit WordSz <- "mem48";
        Read mem49_v : Bit WordSz <- "mem49";
        Read mem50_v : Bit WordSz <- "mem50";
        Read mem51_v : Bit WordSz <- "mem51";
        Read mem52_v : Bit WordSz <- "mem52";
        Read mem53_v : Bit WordSz <- "mem53";
        Read mem54_v : Bit WordSz <- "mem54";
        Read mem55_v : Bit WordSz <- "mem55";
        Read mem56_v : Bit WordSz <- "mem56";
        Read mem57_v : Bit WordSz <- "mem57";
        Read mem58_v : Bit WordSz <- "mem58";
        Read mem59_v : Bit WordSz <- "mem59";
        Read mem60_v : Bit WordSz <- "mem60";
        Read mem61_v : Bit WordSz <- "mem61";
        Read mem62_v : Bit WordSz <- "mem62";
        Read mem63_v : Bit WordSz <- "mem63";
        Read mem64_v : Bit WordSz <- "mem64";
        Read mem65_v : Bit WordSz <- "mem65";
        Read mem66_v : Bit WordSz <- "mem66";
        Read mem67_v : Bit WordSz <- "mem67";
        Read mem68_v : Bit WordSz <- "mem68";
        Read mem69_v : Bit WordSz <- "mem69";
        Read mem70_v : Bit WordSz <- "mem70";
        Read mem71_v : Bit WordSz <- "mem71";
        Read mem72_v : Bit WordSz <- "mem72";
        Read mem73_v : Bit WordSz <- "mem73";
        Read mem74_v : Bit WordSz <- "mem74";
        Read mem75_v : Bit WordSz <- "mem75";
        Read mem76_v : Bit WordSz <- "mem76";
        Read mem77_v : Bit WordSz <- "mem77";
        Read mem78_v : Bit WordSz <- "mem78";
        Read mem79_v : Bit WordSz <- "mem79";
        Read mem80_v : Bit WordSz <- "mem80";
        Read mem81_v : Bit WordSz <- "mem81";
        Read mem82_v : Bit WordSz <- "mem82";
        Read mem83_v : Bit WordSz <- "mem83";
        Read mem84_v : Bit WordSz <- "mem84";
        Read mem85_v : Bit WordSz <- "mem85";
        Read mem86_v : Bit WordSz <- "mem86";
        Read mem87_v : Bit WordSz <- "mem87";
        Read mem88_v : Bit WordSz <- "mem88";
        Read mem89_v : Bit WordSz <- "mem89";
        Read mem90_v : Bit WordSz <- "mem90";
        Read mem91_v : Bit WordSz <- "mem91";
        Read mem92_v : Bit WordSz <- "mem92";
        Read mem93_v : Bit WordSz <- "mem93";
        Read mem94_v : Bit WordSz <- "mem94";
        Read mem95_v : Bit WordSz <- "mem95";
        Read mem96_v : Bit WordSz <- "mem96";
        Read mem97_v : Bit WordSz <- "mem97";
        Read mem98_v : Bit WordSz <- "mem98";
        Read mem99_v : Bit WordSz <- "mem99";
        Read mem100_v : Bit WordSz <- "mem100";
        Read mem101_v : Bit WordSz <- "mem101";
        Read mem102_v : Bit WordSz <- "mem102";
        Read mem103_v : Bit WordSz <- "mem103";
        Read mem104_v : Bit WordSz <- "mem104";
        Read mem105_v : Bit WordSz <- "mem105";
        Read mem106_v : Bit WordSz <- "mem106";
        Read mem107_v : Bit WordSz <- "mem107";
        Read mem108_v : Bit WordSz <- "mem108";
        Read mem109_v : Bit WordSz <- "mem109";
        Read mem110_v : Bit WordSz <- "mem110";
        Read mem111_v : Bit WordSz <- "mem111";
        Read mem112_v : Bit WordSz <- "mem112";
        Read mem113_v : Bit WordSz <- "mem113";
        Read mem114_v : Bit WordSz <- "mem114";
        Read mem115_v : Bit WordSz <- "mem115";
        Read mem116_v : Bit WordSz <- "mem116";
        Read mem117_v : Bit WordSz <- "mem117";
        Read mem118_v : Bit WordSz <- "mem118";
        Read mem119_v : Bit WordSz <- "mem119";
        Read mem120_v : Bit WordSz <- "mem120";
        Read mem121_v : Bit WordSz <- "mem121";
        Read mem122_v : Bit WordSz <- "mem122";
        Read mem123_v : Bit WordSz <- "mem123";
        Read mem124_v : Bit WordSz <- "mem124";
        Read mem125_v : Bit WordSz <- "mem125";
        Read mem126_v : Bit WordSz <- "mem126";
        Read mem127_v : Bit WordSz <- "mem127";
        Read mem128_v : Bit WordSz <- "mem128";
        Read mem129_v : Bit WordSz <- "mem129";
        Read mem130_v : Bit WordSz <- "mem130";
        Read mem131_v : Bit WordSz <- "mem131";
        Read mem132_v : Bit WordSz <- "mem132";
        Read mem133_v : Bit WordSz <- "mem133";
        Read mem134_v : Bit WordSz <- "mem134";
        Read mem135_v : Bit WordSz <- "mem135";
        Read mem136_v : Bit WordSz <- "mem136";
        Read mem137_v : Bit WordSz <- "mem137";
        Read mem138_v : Bit WordSz <- "mem138";
        Read mem139_v : Bit WordSz <- "mem139";
        Read mem140_v : Bit WordSz <- "mem140";
        Read mem141_v : Bit WordSz <- "mem141";
        Read mem142_v : Bit WordSz <- "mem142";
        Read mem143_v : Bit WordSz <- "mem143";
        Read mem144_v : Bit WordSz <- "mem144";
        Read mem145_v : Bit WordSz <- "mem145";
        Read mem146_v : Bit WordSz <- "mem146";
        Read mem147_v : Bit WordSz <- "mem147";
        Read mem148_v : Bit WordSz <- "mem148";
        Read mem149_v : Bit WordSz <- "mem149";
        Read mem150_v : Bit WordSz <- "mem150";
        Read mem151_v : Bit WordSz <- "mem151";
        Read mem152_v : Bit WordSz <- "mem152";
        Read mem153_v : Bit WordSz <- "mem153";
        Read mem154_v : Bit WordSz <- "mem154";
        Read mem155_v : Bit WordSz <- "mem155";
        Read mem156_v : Bit WordSz <- "mem156";
        Read mem157_v : Bit WordSz <- "mem157";
        Read mem158_v : Bit WordSz <- "mem158";
        Read mem159_v : Bit WordSz <- "mem159";
        Read mem160_v : Bit WordSz <- "mem160";
        Read mem161_v : Bit WordSz <- "mem161";
        Read mem162_v : Bit WordSz <- "mem162";
        Read mem163_v : Bit WordSz <- "mem163";
        Read mem164_v : Bit WordSz <- "mem164";
        Read mem165_v : Bit WordSz <- "mem165";
        Read mem166_v : Bit WordSz <- "mem166";
        Read mem167_v : Bit WordSz <- "mem167";
        Read mem168_v : Bit WordSz <- "mem168";
        Read mem169_v : Bit WordSz <- "mem169";
        Read mem170_v : Bit WordSz <- "mem170";
        Read mem171_v : Bit WordSz <- "mem171";
        Read mem172_v : Bit WordSz <- "mem172";
        Read mem173_v : Bit WordSz <- "mem173";
        Read mem174_v : Bit WordSz <- "mem174";
        Read mem175_v : Bit WordSz <- "mem175";
        Read mem176_v : Bit WordSz <- "mem176";
        Read mem177_v : Bit WordSz <- "mem177";
        Read mem178_v : Bit WordSz <- "mem178";
        Read mem179_v : Bit WordSz <- "mem179";
        Read mem180_v : Bit WordSz <- "mem180";
        Read mem181_v : Bit WordSz <- "mem181";
        Read mem182_v : Bit WordSz <- "mem182";
        Read mem183_v : Bit WordSz <- "mem183";
        Read mem184_v : Bit WordSz <- "mem184";
        Read mem185_v : Bit WordSz <- "mem185";
        Read mem186_v : Bit WordSz <- "mem186";
        Read mem187_v : Bit WordSz <- "mem187";
        Read mem188_v : Bit WordSz <- "mem188";
        Read mem189_v : Bit WordSz <- "mem189";
        Read mem190_v : Bit WordSz <- "mem190";
        Read mem191_v : Bit WordSz <- "mem191";
        Read mem192_v : Bit WordSz <- "mem192";
        Read mem193_v : Bit WordSz <- "mem193";
        Read mem194_v : Bit WordSz <- "mem194";
        Read mem195_v : Bit WordSz <- "mem195";
        Read mem196_v : Bit WordSz <- "mem196";
        Read mem197_v : Bit WordSz <- "mem197";
        Read mem198_v : Bit WordSz <- "mem198";
        Read mem199_v : Bit WordSz <- "mem199";
        Read mem200_v : Bit WordSz <- "mem200";
        Read mem201_v : Bit WordSz <- "mem201";
        Read mem202_v : Bit WordSz <- "mem202";
        Read mem203_v : Bit WordSz <- "mem203";
        Read mem204_v : Bit WordSz <- "mem204";
        Read mem205_v : Bit WordSz <- "mem205";
        Read mem206_v : Bit WordSz <- "mem206";
        Read mem207_v : Bit WordSz <- "mem207";
        Read mem208_v : Bit WordSz <- "mem208";
        Read mem209_v : Bit WordSz <- "mem209";
        Read mem210_v : Bit WordSz <- "mem210";
        Read mem211_v : Bit WordSz <- "mem211";
        Read mem212_v : Bit WordSz <- "mem212";
        Read mem213_v : Bit WordSz <- "mem213";
        Read mem214_v : Bit WordSz <- "mem214";
        Read mem215_v : Bit WordSz <- "mem215";
        Read mem216_v : Bit WordSz <- "mem216";
        Read mem217_v : Bit WordSz <- "mem217";
        Read mem218_v : Bit WordSz <- "mem218";
        Read mem219_v : Bit WordSz <- "mem219";
        Read mem220_v : Bit WordSz <- "mem220";
        Read mem221_v : Bit WordSz <- "mem221";
        Read mem222_v : Bit WordSz <- "mem222";
        Read mem223_v : Bit WordSz <- "mem223";
        Read mem224_v : Bit WordSz <- "mem224";
        Read mem225_v : Bit WordSz <- "mem225";
        Read mem226_v : Bit WordSz <- "mem226";
        Read mem227_v : Bit WordSz <- "mem227";
        Read mem228_v : Bit WordSz <- "mem228";
        Read mem229_v : Bit WordSz <- "mem229";
        Read mem230_v : Bit WordSz <- "mem230";
        Read mem231_v : Bit WordSz <- "mem231";
        Read mem232_v : Bit WordSz <- "mem232";
        Read mem233_v : Bit WordSz <- "mem233";
        Read mem234_v : Bit WordSz <- "mem234";
        Read mem235_v : Bit WordSz <- "mem235";
        Read mem236_v : Bit WordSz <- "mem236";
        Read mem237_v : Bit WordSz <- "mem237";
        Read mem238_v : Bit WordSz <- "mem238";
        Read mem239_v : Bit WordSz <- "mem239";
        Read mem240_v : Bit WordSz <- "mem240";
        Read mem241_v : Bit WordSz <- "mem241";
        Read mem242_v : Bit WordSz <- "mem242";
        Read mem243_v : Bit WordSz <- "mem243";
        Read mem244_v : Bit WordSz <- "mem244";
        Read mem245_v : Bit WordSz <- "mem245";
        Read mem246_v : Bit WordSz <- "mem246";
        Read mem247_v : Bit WordSz <- "mem247";
        Read mem248_v : Bit WordSz <- "mem248";
        Read mem249_v : Bit WordSz <- "mem249";
        Read mem250_v : Bit WordSz <- "mem250";
        Read mem251_v : Bit WordSz <- "mem251";
        Read mem252_v : Bit WordSz <- "mem252";
        Read mem253_v : Bit WordSz <- "mem253";
        Read mem254_v : Bit WordSz <- "mem254";
        Read mem255_v : Bit WordSz <- "mem255";

        LET mem_v0 : Vector (Bit WordSz) MemAddrSz <- $$Default@[$$(natToWord MemAddrSz 0) <- #mem0_v];
        LET mem_v1 : Vector (Bit WordSz) MemAddrSz <- #mem_v0@[$$(natToWord MemAddrSz 1) <- #mem1_v];
        LET mem_v2 : Vector (Bit WordSz) MemAddrSz <- #mem_v1@[$$(natToWord MemAddrSz 2) <- #mem2_v];
        LET mem_v3 : Vector (Bit WordSz) MemAddrSz <- #mem_v2@[$$(natToWord MemAddrSz 3) <- #mem3_v];
        LET mem_v4 : Vector (Bit WordSz) MemAddrSz <- #mem_v3@[$$(natToWord MemAddrSz 4) <- #mem4_v];
        LET mem_v5 : Vector (Bit WordSz) MemAddrSz <- #mem_v4@[$$(natToWord MemAddrSz 5) <- #mem5_v];
        LET mem_v6 : Vector (Bit WordSz) MemAddrSz <- #mem_v5@[$$(natToWord MemAddrSz 6) <- #mem6_v];
        LET mem_v7 : Vector (Bit WordSz) MemAddrSz <- #mem_v6@[$$(natToWord MemAddrSz 7) <- #mem7_v];
        LET mem_v8 : Vector (Bit WordSz) MemAddrSz <- #mem_v7@[$$(natToWord MemAddrSz 8) <- #mem8_v];
        LET mem_v9 : Vector (Bit WordSz) MemAddrSz <- #mem_v8@[$$(natToWord MemAddrSz 9) <- #mem9_v];
        LET mem_v10 : Vector (Bit WordSz) MemAddrSz <- #mem_v9@[$$(natToWord MemAddrSz 10) <- #mem10_v];
        LET mem_v11 : Vector (Bit WordSz) MemAddrSz <- #mem_v10@[$$(natToWord MemAddrSz 11) <- #mem11_v];
        LET mem_v12 : Vector (Bit WordSz) MemAddrSz <- #mem_v11@[$$(natToWord MemAddrSz 12) <- #mem12_v];
        LET mem_v13 : Vector (Bit WordSz) MemAddrSz <- #mem_v12@[$$(natToWord MemAddrSz 13) <- #mem13_v];
        LET mem_v14 : Vector (Bit WordSz) MemAddrSz <- #mem_v13@[$$(natToWord MemAddrSz 14) <- #mem14_v];
        LET mem_v15 : Vector (Bit WordSz) MemAddrSz <- #mem_v14@[$$(natToWord MemAddrSz 15) <- #mem15_v];
        LET mem_v16 : Vector (Bit WordSz) MemAddrSz <- #mem_v15@[$$(natToWord MemAddrSz 16) <- #mem16_v];
        LET mem_v17 : Vector (Bit WordSz) MemAddrSz <- #mem_v16@[$$(natToWord MemAddrSz 17) <- #mem17_v];
        LET mem_v18 : Vector (Bit WordSz) MemAddrSz <- #mem_v17@[$$(natToWord MemAddrSz 18) <- #mem18_v];
        LET mem_v19 : Vector (Bit WordSz) MemAddrSz <- #mem_v18@[$$(natToWord MemAddrSz 19) <- #mem19_v];
        LET mem_v20 : Vector (Bit WordSz) MemAddrSz <- #mem_v19@[$$(natToWord MemAddrSz 20) <- #mem20_v];
        LET mem_v21 : Vector (Bit WordSz) MemAddrSz <- #mem_v20@[$$(natToWord MemAddrSz 21) <- #mem21_v];
        LET mem_v22 : Vector (Bit WordSz) MemAddrSz <- #mem_v21@[$$(natToWord MemAddrSz 22) <- #mem22_v];
        LET mem_v23 : Vector (Bit WordSz) MemAddrSz <- #mem_v22@[$$(natToWord MemAddrSz 23) <- #mem23_v];
        LET mem_v24 : Vector (Bit WordSz) MemAddrSz <- #mem_v23@[$$(natToWord MemAddrSz 24) <- #mem24_v];
        LET mem_v25 : Vector (Bit WordSz) MemAddrSz <- #mem_v24@[$$(natToWord MemAddrSz 25) <- #mem25_v];
        LET mem_v26 : Vector (Bit WordSz) MemAddrSz <- #mem_v25@[$$(natToWord MemAddrSz 26) <- #mem26_v];
        LET mem_v27 : Vector (Bit WordSz) MemAddrSz <- #mem_v26@[$$(natToWord MemAddrSz 27) <- #mem27_v];
        LET mem_v28 : Vector (Bit WordSz) MemAddrSz <- #mem_v27@[$$(natToWord MemAddrSz 28) <- #mem28_v];
        LET mem_v29 : Vector (Bit WordSz) MemAddrSz <- #mem_v28@[$$(natToWord MemAddrSz 29) <- #mem29_v];
        LET mem_v30 : Vector (Bit WordSz) MemAddrSz <- #mem_v29@[$$(natToWord MemAddrSz 30) <- #mem30_v];
        LET mem_v31 : Vector (Bit WordSz) MemAddrSz <- #mem_v30@[$$(natToWord MemAddrSz 31) <- #mem31_v];
        LET mem_v32 : Vector (Bit WordSz) MemAddrSz <- #mem_v31@[$$(natToWord MemAddrSz 32) <- #mem32_v];
        LET mem_v33 : Vector (Bit WordSz) MemAddrSz <- #mem_v32@[$$(natToWord MemAddrSz 33) <- #mem33_v];
        LET mem_v34 : Vector (Bit WordSz) MemAddrSz <- #mem_v33@[$$(natToWord MemAddrSz 34) <- #mem34_v];
        LET mem_v35 : Vector (Bit WordSz) MemAddrSz <- #mem_v34@[$$(natToWord MemAddrSz 35) <- #mem35_v];
        LET mem_v36 : Vector (Bit WordSz) MemAddrSz <- #mem_v35@[$$(natToWord MemAddrSz 36) <- #mem36_v];
        LET mem_v37 : Vector (Bit WordSz) MemAddrSz <- #mem_v36@[$$(natToWord MemAddrSz 37) <- #mem37_v];
        LET mem_v38 : Vector (Bit WordSz) MemAddrSz <- #mem_v37@[$$(natToWord MemAddrSz 38) <- #mem38_v];
        LET mem_v39 : Vector (Bit WordSz) MemAddrSz <- #mem_v38@[$$(natToWord MemAddrSz 39) <- #mem39_v];
        LET mem_v40 : Vector (Bit WordSz) MemAddrSz <- #mem_v39@[$$(natToWord MemAddrSz 40) <- #mem40_v];
        LET mem_v41 : Vector (Bit WordSz) MemAddrSz <- #mem_v40@[$$(natToWord MemAddrSz 41) <- #mem41_v];
        LET mem_v42 : Vector (Bit WordSz) MemAddrSz <- #mem_v41@[$$(natToWord MemAddrSz 42) <- #mem42_v];
        LET mem_v43 : Vector (Bit WordSz) MemAddrSz <- #mem_v42@[$$(natToWord MemAddrSz 43) <- #mem43_v];
        LET mem_v44 : Vector (Bit WordSz) MemAddrSz <- #mem_v43@[$$(natToWord MemAddrSz 44) <- #mem44_v];
        LET mem_v45 : Vector (Bit WordSz) MemAddrSz <- #mem_v44@[$$(natToWord MemAddrSz 45) <- #mem45_v];
        LET mem_v46 : Vector (Bit WordSz) MemAddrSz <- #mem_v45@[$$(natToWord MemAddrSz 46) <- #mem46_v];
        LET mem_v47 : Vector (Bit WordSz) MemAddrSz <- #mem_v46@[$$(natToWord MemAddrSz 47) <- #mem47_v];
        LET mem_v48 : Vector (Bit WordSz) MemAddrSz <- #mem_v47@[$$(natToWord MemAddrSz 48) <- #mem48_v];
        LET mem_v49 : Vector (Bit WordSz) MemAddrSz <- #mem_v48@[$$(natToWord MemAddrSz 49) <- #mem49_v];
        LET mem_v50 : Vector (Bit WordSz) MemAddrSz <- #mem_v49@[$$(natToWord MemAddrSz 50) <- #mem50_v];
        LET mem_v51 : Vector (Bit WordSz) MemAddrSz <- #mem_v50@[$$(natToWord MemAddrSz 51) <- #mem51_v];
        LET mem_v52 : Vector (Bit WordSz) MemAddrSz <- #mem_v51@[$$(natToWord MemAddrSz 52) <- #mem52_v];
        LET mem_v53 : Vector (Bit WordSz) MemAddrSz <- #mem_v52@[$$(natToWord MemAddrSz 53) <- #mem53_v];
        LET mem_v54 : Vector (Bit WordSz) MemAddrSz <- #mem_v53@[$$(natToWord MemAddrSz 54) <- #mem54_v];
        LET mem_v55 : Vector (Bit WordSz) MemAddrSz <- #mem_v54@[$$(natToWord MemAddrSz 55) <- #mem55_v];
        LET mem_v56 : Vector (Bit WordSz) MemAddrSz <- #mem_v55@[$$(natToWord MemAddrSz 56) <- #mem56_v];
        LET mem_v57 : Vector (Bit WordSz) MemAddrSz <- #mem_v56@[$$(natToWord MemAddrSz 57) <- #mem57_v];
        LET mem_v58 : Vector (Bit WordSz) MemAddrSz <- #mem_v57@[$$(natToWord MemAddrSz 58) <- #mem58_v];
        LET mem_v59 : Vector (Bit WordSz) MemAddrSz <- #mem_v58@[$$(natToWord MemAddrSz 59) <- #mem59_v];
        LET mem_v60 : Vector (Bit WordSz) MemAddrSz <- #mem_v59@[$$(natToWord MemAddrSz 60) <- #mem60_v];
        LET mem_v61 : Vector (Bit WordSz) MemAddrSz <- #mem_v60@[$$(natToWord MemAddrSz 61) <- #mem61_v];
        LET mem_v62 : Vector (Bit WordSz) MemAddrSz <- #mem_v61@[$$(natToWord MemAddrSz 62) <- #mem62_v];
        LET mem_v63 : Vector (Bit WordSz) MemAddrSz <- #mem_v62@[$$(natToWord MemAddrSz 63) <- #mem63_v];
        LET mem_v64 : Vector (Bit WordSz) MemAddrSz <- #mem_v63@[$$(natToWord MemAddrSz 64) <- #mem64_v];
        LET mem_v65 : Vector (Bit WordSz) MemAddrSz <- #mem_v64@[$$(natToWord MemAddrSz 65) <- #mem65_v];
        LET mem_v66 : Vector (Bit WordSz) MemAddrSz <- #mem_v65@[$$(natToWord MemAddrSz 66) <- #mem66_v];
        LET mem_v67 : Vector (Bit WordSz) MemAddrSz <- #mem_v66@[$$(natToWord MemAddrSz 67) <- #mem67_v];
        LET mem_v68 : Vector (Bit WordSz) MemAddrSz <- #mem_v67@[$$(natToWord MemAddrSz 68) <- #mem68_v];
        LET mem_v69 : Vector (Bit WordSz) MemAddrSz <- #mem_v68@[$$(natToWord MemAddrSz 69) <- #mem69_v];
        LET mem_v70 : Vector (Bit WordSz) MemAddrSz <- #mem_v69@[$$(natToWord MemAddrSz 70) <- #mem70_v];
        LET mem_v71 : Vector (Bit WordSz) MemAddrSz <- #mem_v70@[$$(natToWord MemAddrSz 71) <- #mem71_v];
        LET mem_v72 : Vector (Bit WordSz) MemAddrSz <- #mem_v71@[$$(natToWord MemAddrSz 72) <- #mem72_v];
        LET mem_v73 : Vector (Bit WordSz) MemAddrSz <- #mem_v72@[$$(natToWord MemAddrSz 73) <- #mem73_v];
        LET mem_v74 : Vector (Bit WordSz) MemAddrSz <- #mem_v73@[$$(natToWord MemAddrSz 74) <- #mem74_v];
        LET mem_v75 : Vector (Bit WordSz) MemAddrSz <- #mem_v74@[$$(natToWord MemAddrSz 75) <- #mem75_v];
        LET mem_v76 : Vector (Bit WordSz) MemAddrSz <- #mem_v75@[$$(natToWord MemAddrSz 76) <- #mem76_v];
        LET mem_v77 : Vector (Bit WordSz) MemAddrSz <- #mem_v76@[$$(natToWord MemAddrSz 77) <- #mem77_v];
        LET mem_v78 : Vector (Bit WordSz) MemAddrSz <- #mem_v77@[$$(natToWord MemAddrSz 78) <- #mem78_v];
        LET mem_v79 : Vector (Bit WordSz) MemAddrSz <- #mem_v78@[$$(natToWord MemAddrSz 79) <- #mem79_v];
        LET mem_v80 : Vector (Bit WordSz) MemAddrSz <- #mem_v79@[$$(natToWord MemAddrSz 80) <- #mem80_v];
        LET mem_v81 : Vector (Bit WordSz) MemAddrSz <- #mem_v80@[$$(natToWord MemAddrSz 81) <- #mem81_v];
        LET mem_v82 : Vector (Bit WordSz) MemAddrSz <- #mem_v81@[$$(natToWord MemAddrSz 82) <- #mem82_v];
        LET mem_v83 : Vector (Bit WordSz) MemAddrSz <- #mem_v82@[$$(natToWord MemAddrSz 83) <- #mem83_v];
        LET mem_v84 : Vector (Bit WordSz) MemAddrSz <- #mem_v83@[$$(natToWord MemAddrSz 84) <- #mem84_v];
        LET mem_v85 : Vector (Bit WordSz) MemAddrSz <- #mem_v84@[$$(natToWord MemAddrSz 85) <- #mem85_v];
        LET mem_v86 : Vector (Bit WordSz) MemAddrSz <- #mem_v85@[$$(natToWord MemAddrSz 86) <- #mem86_v];
        LET mem_v87 : Vector (Bit WordSz) MemAddrSz <- #mem_v86@[$$(natToWord MemAddrSz 87) <- #mem87_v];
        LET mem_v88 : Vector (Bit WordSz) MemAddrSz <- #mem_v87@[$$(natToWord MemAddrSz 88) <- #mem88_v];
        LET mem_v89 : Vector (Bit WordSz) MemAddrSz <- #mem_v88@[$$(natToWord MemAddrSz 89) <- #mem89_v];
        LET mem_v90 : Vector (Bit WordSz) MemAddrSz <- #mem_v89@[$$(natToWord MemAddrSz 90) <- #mem90_v];
        LET mem_v91 : Vector (Bit WordSz) MemAddrSz <- #mem_v90@[$$(natToWord MemAddrSz 91) <- #mem91_v];
        LET mem_v92 : Vector (Bit WordSz) MemAddrSz <- #mem_v91@[$$(natToWord MemAddrSz 92) <- #mem92_v];
        LET mem_v93 : Vector (Bit WordSz) MemAddrSz <- #mem_v92@[$$(natToWord MemAddrSz 93) <- #mem93_v];
        LET mem_v94 : Vector (Bit WordSz) MemAddrSz <- #mem_v93@[$$(natToWord MemAddrSz 94) <- #mem94_v];
        LET mem_v95 : Vector (Bit WordSz) MemAddrSz <- #mem_v94@[$$(natToWord MemAddrSz 95) <- #mem95_v];
        LET mem_v96 : Vector (Bit WordSz) MemAddrSz <- #mem_v95@[$$(natToWord MemAddrSz 96) <- #mem96_v];
        LET mem_v97 : Vector (Bit WordSz) MemAddrSz <- #mem_v96@[$$(natToWord MemAddrSz 97) <- #mem97_v];
        LET mem_v98 : Vector (Bit WordSz) MemAddrSz <- #mem_v97@[$$(natToWord MemAddrSz 98) <- #mem98_v];
        LET mem_v99 : Vector (Bit WordSz) MemAddrSz <- #mem_v98@[$$(natToWord MemAddrSz 99) <- #mem99_v];
        LET mem_v100 : Vector (Bit WordSz) MemAddrSz <- #mem_v99@[$$(natToWord MemAddrSz 100) <- #mem100_v];
        LET mem_v101 : Vector (Bit WordSz) MemAddrSz <- #mem_v100@[$$(natToWord MemAddrSz 101) <- #mem101_v];
        LET mem_v102 : Vector (Bit WordSz) MemAddrSz <- #mem_v101@[$$(natToWord MemAddrSz 102) <- #mem102_v];
        LET mem_v103 : Vector (Bit WordSz) MemAddrSz <- #mem_v102@[$$(natToWord MemAddrSz 103) <- #mem103_v];
        LET mem_v104 : Vector (Bit WordSz) MemAddrSz <- #mem_v103@[$$(natToWord MemAddrSz 104) <- #mem104_v];
        LET mem_v105 : Vector (Bit WordSz) MemAddrSz <- #mem_v104@[$$(natToWord MemAddrSz 105) <- #mem105_v];
        LET mem_v106 : Vector (Bit WordSz) MemAddrSz <- #mem_v105@[$$(natToWord MemAddrSz 106) <- #mem106_v];
        LET mem_v107 : Vector (Bit WordSz) MemAddrSz <- #mem_v106@[$$(natToWord MemAddrSz 107) <- #mem107_v];
        LET mem_v108 : Vector (Bit WordSz) MemAddrSz <- #mem_v107@[$$(natToWord MemAddrSz 108) <- #mem108_v];
        LET mem_v109 : Vector (Bit WordSz) MemAddrSz <- #mem_v108@[$$(natToWord MemAddrSz 109) <- #mem109_v];
        LET mem_v110 : Vector (Bit WordSz) MemAddrSz <- #mem_v109@[$$(natToWord MemAddrSz 110) <- #mem110_v];
        LET mem_v111 : Vector (Bit WordSz) MemAddrSz <- #mem_v110@[$$(natToWord MemAddrSz 111) <- #mem111_v];
        LET mem_v112 : Vector (Bit WordSz) MemAddrSz <- #mem_v111@[$$(natToWord MemAddrSz 112) <- #mem112_v];
        LET mem_v113 : Vector (Bit WordSz) MemAddrSz <- #mem_v112@[$$(natToWord MemAddrSz 113) <- #mem113_v];
        LET mem_v114 : Vector (Bit WordSz) MemAddrSz <- #mem_v113@[$$(natToWord MemAddrSz 114) <- #mem114_v];
        LET mem_v115 : Vector (Bit WordSz) MemAddrSz <- #mem_v114@[$$(natToWord MemAddrSz 115) <- #mem115_v];
        LET mem_v116 : Vector (Bit WordSz) MemAddrSz <- #mem_v115@[$$(natToWord MemAddrSz 116) <- #mem116_v];
        LET mem_v117 : Vector (Bit WordSz) MemAddrSz <- #mem_v116@[$$(natToWord MemAddrSz 117) <- #mem117_v];
        LET mem_v118 : Vector (Bit WordSz) MemAddrSz <- #mem_v117@[$$(natToWord MemAddrSz 118) <- #mem118_v];
        LET mem_v119 : Vector (Bit WordSz) MemAddrSz <- #mem_v118@[$$(natToWord MemAddrSz 119) <- #mem119_v];
        LET mem_v120 : Vector (Bit WordSz) MemAddrSz <- #mem_v119@[$$(natToWord MemAddrSz 120) <- #mem120_v];
        LET mem_v121 : Vector (Bit WordSz) MemAddrSz <- #mem_v120@[$$(natToWord MemAddrSz 121) <- #mem121_v];
        LET mem_v122 : Vector (Bit WordSz) MemAddrSz <- #mem_v121@[$$(natToWord MemAddrSz 122) <- #mem122_v];
        LET mem_v123 : Vector (Bit WordSz) MemAddrSz <- #mem_v122@[$$(natToWord MemAddrSz 123) <- #mem123_v];
        LET mem_v124 : Vector (Bit WordSz) MemAddrSz <- #mem_v123@[$$(natToWord MemAddrSz 124) <- #mem124_v];
        LET mem_v125 : Vector (Bit WordSz) MemAddrSz <- #mem_v124@[$$(natToWord MemAddrSz 125) <- #mem125_v];
        LET mem_v126 : Vector (Bit WordSz) MemAddrSz <- #mem_v125@[$$(natToWord MemAddrSz 126) <- #mem126_v];
        LET mem_v127 : Vector (Bit WordSz) MemAddrSz <- #mem_v126@[$$(natToWord MemAddrSz 127) <- #mem127_v];
        LET mem_v128 : Vector (Bit WordSz) MemAddrSz <- #mem_v127@[$$(natToWord MemAddrSz 128) <- #mem128_v];
        LET mem_v129 : Vector (Bit WordSz) MemAddrSz <- #mem_v128@[$$(natToWord MemAddrSz 129) <- #mem129_v];
        LET mem_v130 : Vector (Bit WordSz) MemAddrSz <- #mem_v129@[$$(natToWord MemAddrSz 130) <- #mem130_v];
        LET mem_v131 : Vector (Bit WordSz) MemAddrSz <- #mem_v130@[$$(natToWord MemAddrSz 131) <- #mem131_v];
        LET mem_v132 : Vector (Bit WordSz) MemAddrSz <- #mem_v131@[$$(natToWord MemAddrSz 132) <- #mem132_v];
        LET mem_v133 : Vector (Bit WordSz) MemAddrSz <- #mem_v132@[$$(natToWord MemAddrSz 133) <- #mem133_v];
        LET mem_v134 : Vector (Bit WordSz) MemAddrSz <- #mem_v133@[$$(natToWord MemAddrSz 134) <- #mem134_v];
        LET mem_v135 : Vector (Bit WordSz) MemAddrSz <- #mem_v134@[$$(natToWord MemAddrSz 135) <- #mem135_v];
        LET mem_v136 : Vector (Bit WordSz) MemAddrSz <- #mem_v135@[$$(natToWord MemAddrSz 136) <- #mem136_v];
        LET mem_v137 : Vector (Bit WordSz) MemAddrSz <- #mem_v136@[$$(natToWord MemAddrSz 137) <- #mem137_v];
        LET mem_v138 : Vector (Bit WordSz) MemAddrSz <- #mem_v137@[$$(natToWord MemAddrSz 138) <- #mem138_v];
        LET mem_v139 : Vector (Bit WordSz) MemAddrSz <- #mem_v138@[$$(natToWord MemAddrSz 139) <- #mem139_v];
        LET mem_v140 : Vector (Bit WordSz) MemAddrSz <- #mem_v139@[$$(natToWord MemAddrSz 140) <- #mem140_v];
        LET mem_v141 : Vector (Bit WordSz) MemAddrSz <- #mem_v140@[$$(natToWord MemAddrSz 141) <- #mem141_v];
        LET mem_v142 : Vector (Bit WordSz) MemAddrSz <- #mem_v141@[$$(natToWord MemAddrSz 142) <- #mem142_v];
        LET mem_v143 : Vector (Bit WordSz) MemAddrSz <- #mem_v142@[$$(natToWord MemAddrSz 143) <- #mem143_v];
        LET mem_v144 : Vector (Bit WordSz) MemAddrSz <- #mem_v143@[$$(natToWord MemAddrSz 144) <- #mem144_v];
        LET mem_v145 : Vector (Bit WordSz) MemAddrSz <- #mem_v144@[$$(natToWord MemAddrSz 145) <- #mem145_v];
        LET mem_v146 : Vector (Bit WordSz) MemAddrSz <- #mem_v145@[$$(natToWord MemAddrSz 146) <- #mem146_v];
        LET mem_v147 : Vector (Bit WordSz) MemAddrSz <- #mem_v146@[$$(natToWord MemAddrSz 147) <- #mem147_v];
        LET mem_v148 : Vector (Bit WordSz) MemAddrSz <- #mem_v147@[$$(natToWord MemAddrSz 148) <- #mem148_v];
        LET mem_v149 : Vector (Bit WordSz) MemAddrSz <- #mem_v148@[$$(natToWord MemAddrSz 149) <- #mem149_v];
        LET mem_v150 : Vector (Bit WordSz) MemAddrSz <- #mem_v149@[$$(natToWord MemAddrSz 150) <- #mem150_v];
        LET mem_v151 : Vector (Bit WordSz) MemAddrSz <- #mem_v150@[$$(natToWord MemAddrSz 151) <- #mem151_v];
        LET mem_v152 : Vector (Bit WordSz) MemAddrSz <- #mem_v151@[$$(natToWord MemAddrSz 152) <- #mem152_v];
        LET mem_v153 : Vector (Bit WordSz) MemAddrSz <- #mem_v152@[$$(natToWord MemAddrSz 153) <- #mem153_v];
        LET mem_v154 : Vector (Bit WordSz) MemAddrSz <- #mem_v153@[$$(natToWord MemAddrSz 154) <- #mem154_v];
        LET mem_v155 : Vector (Bit WordSz) MemAddrSz <- #mem_v154@[$$(natToWord MemAddrSz 155) <- #mem155_v];
        LET mem_v156 : Vector (Bit WordSz) MemAddrSz <- #mem_v155@[$$(natToWord MemAddrSz 156) <- #mem156_v];
        LET mem_v157 : Vector (Bit WordSz) MemAddrSz <- #mem_v156@[$$(natToWord MemAddrSz 157) <- #mem157_v];
        LET mem_v158 : Vector (Bit WordSz) MemAddrSz <- #mem_v157@[$$(natToWord MemAddrSz 158) <- #mem158_v];
        LET mem_v159 : Vector (Bit WordSz) MemAddrSz <- #mem_v158@[$$(natToWord MemAddrSz 159) <- #mem159_v];
        LET mem_v160 : Vector (Bit WordSz) MemAddrSz <- #mem_v159@[$$(natToWord MemAddrSz 160) <- #mem160_v];
        LET mem_v161 : Vector (Bit WordSz) MemAddrSz <- #mem_v160@[$$(natToWord MemAddrSz 161) <- #mem161_v];
        LET mem_v162 : Vector (Bit WordSz) MemAddrSz <- #mem_v161@[$$(natToWord MemAddrSz 162) <- #mem162_v];
        LET mem_v163 : Vector (Bit WordSz) MemAddrSz <- #mem_v162@[$$(natToWord MemAddrSz 163) <- #mem163_v];
        LET mem_v164 : Vector (Bit WordSz) MemAddrSz <- #mem_v163@[$$(natToWord MemAddrSz 164) <- #mem164_v];
        LET mem_v165 : Vector (Bit WordSz) MemAddrSz <- #mem_v164@[$$(natToWord MemAddrSz 165) <- #mem165_v];
        LET mem_v166 : Vector (Bit WordSz) MemAddrSz <- #mem_v165@[$$(natToWord MemAddrSz 166) <- #mem166_v];
        LET mem_v167 : Vector (Bit WordSz) MemAddrSz <- #mem_v166@[$$(natToWord MemAddrSz 167) <- #mem167_v];
        LET mem_v168 : Vector (Bit WordSz) MemAddrSz <- #mem_v167@[$$(natToWord MemAddrSz 168) <- #mem168_v];
        LET mem_v169 : Vector (Bit WordSz) MemAddrSz <- #mem_v168@[$$(natToWord MemAddrSz 169) <- #mem169_v];
        LET mem_v170 : Vector (Bit WordSz) MemAddrSz <- #mem_v169@[$$(natToWord MemAddrSz 170) <- #mem170_v];
        LET mem_v171 : Vector (Bit WordSz) MemAddrSz <- #mem_v170@[$$(natToWord MemAddrSz 171) <- #mem171_v];
        LET mem_v172 : Vector (Bit WordSz) MemAddrSz <- #mem_v171@[$$(natToWord MemAddrSz 172) <- #mem172_v];
        LET mem_v173 : Vector (Bit WordSz) MemAddrSz <- #mem_v172@[$$(natToWord MemAddrSz 173) <- #mem173_v];
        LET mem_v174 : Vector (Bit WordSz) MemAddrSz <- #mem_v173@[$$(natToWord MemAddrSz 174) <- #mem174_v];
        LET mem_v175 : Vector (Bit WordSz) MemAddrSz <- #mem_v174@[$$(natToWord MemAddrSz 175) <- #mem175_v];
        LET mem_v176 : Vector (Bit WordSz) MemAddrSz <- #mem_v175@[$$(natToWord MemAddrSz 176) <- #mem176_v];
        LET mem_v177 : Vector (Bit WordSz) MemAddrSz <- #mem_v176@[$$(natToWord MemAddrSz 177) <- #mem177_v];
        LET mem_v178 : Vector (Bit WordSz) MemAddrSz <- #mem_v177@[$$(natToWord MemAddrSz 178) <- #mem178_v];
        LET mem_v179 : Vector (Bit WordSz) MemAddrSz <- #mem_v178@[$$(natToWord MemAddrSz 179) <- #mem179_v];
        LET mem_v180 : Vector (Bit WordSz) MemAddrSz <- #mem_v179@[$$(natToWord MemAddrSz 180) <- #mem180_v];
        LET mem_v181 : Vector (Bit WordSz) MemAddrSz <- #mem_v180@[$$(natToWord MemAddrSz 181) <- #mem181_v];
        LET mem_v182 : Vector (Bit WordSz) MemAddrSz <- #mem_v181@[$$(natToWord MemAddrSz 182) <- #mem182_v];
        LET mem_v183 : Vector (Bit WordSz) MemAddrSz <- #mem_v182@[$$(natToWord MemAddrSz 183) <- #mem183_v];
        LET mem_v184 : Vector (Bit WordSz) MemAddrSz <- #mem_v183@[$$(natToWord MemAddrSz 184) <- #mem184_v];
        LET mem_v185 : Vector (Bit WordSz) MemAddrSz <- #mem_v184@[$$(natToWord MemAddrSz 185) <- #mem185_v];
        LET mem_v186 : Vector (Bit WordSz) MemAddrSz <- #mem_v185@[$$(natToWord MemAddrSz 186) <- #mem186_v];
        LET mem_v187 : Vector (Bit WordSz) MemAddrSz <- #mem_v186@[$$(natToWord MemAddrSz 187) <- #mem187_v];
        LET mem_v188 : Vector (Bit WordSz) MemAddrSz <- #mem_v187@[$$(natToWord MemAddrSz 188) <- #mem188_v];
        LET mem_v189 : Vector (Bit WordSz) MemAddrSz <- #mem_v188@[$$(natToWord MemAddrSz 189) <- #mem189_v];
        LET mem_v190 : Vector (Bit WordSz) MemAddrSz <- #mem_v189@[$$(natToWord MemAddrSz 190) <- #mem190_v];
        LET mem_v191 : Vector (Bit WordSz) MemAddrSz <- #mem_v190@[$$(natToWord MemAddrSz 191) <- #mem191_v];
        LET mem_v192 : Vector (Bit WordSz) MemAddrSz <- #mem_v191@[$$(natToWord MemAddrSz 192) <- #mem192_v];
        LET mem_v193 : Vector (Bit WordSz) MemAddrSz <- #mem_v192@[$$(natToWord MemAddrSz 193) <- #mem193_v];
        LET mem_v194 : Vector (Bit WordSz) MemAddrSz <- #mem_v193@[$$(natToWord MemAddrSz 194) <- #mem194_v];
        LET mem_v195 : Vector (Bit WordSz) MemAddrSz <- #mem_v194@[$$(natToWord MemAddrSz 195) <- #mem195_v];
        LET mem_v196 : Vector (Bit WordSz) MemAddrSz <- #mem_v195@[$$(natToWord MemAddrSz 196) <- #mem196_v];
        LET mem_v197 : Vector (Bit WordSz) MemAddrSz <- #mem_v196@[$$(natToWord MemAddrSz 197) <- #mem197_v];
        LET mem_v198 : Vector (Bit WordSz) MemAddrSz <- #mem_v197@[$$(natToWord MemAddrSz 198) <- #mem198_v];
        LET mem_v199 : Vector (Bit WordSz) MemAddrSz <- #mem_v198@[$$(natToWord MemAddrSz 199) <- #mem199_v];
        LET mem_v200 : Vector (Bit WordSz) MemAddrSz <- #mem_v199@[$$(natToWord MemAddrSz 200) <- #mem200_v];
        LET mem_v201 : Vector (Bit WordSz) MemAddrSz <- #mem_v200@[$$(natToWord MemAddrSz 201) <- #mem201_v];
        LET mem_v202 : Vector (Bit WordSz) MemAddrSz <- #mem_v201@[$$(natToWord MemAddrSz 202) <- #mem202_v];
        LET mem_v203 : Vector (Bit WordSz) MemAddrSz <- #mem_v202@[$$(natToWord MemAddrSz 203) <- #mem203_v];
        LET mem_v204 : Vector (Bit WordSz) MemAddrSz <- #mem_v203@[$$(natToWord MemAddrSz 204) <- #mem204_v];
        LET mem_v205 : Vector (Bit WordSz) MemAddrSz <- #mem_v204@[$$(natToWord MemAddrSz 205) <- #mem205_v];
        LET mem_v206 : Vector (Bit WordSz) MemAddrSz <- #mem_v205@[$$(natToWord MemAddrSz 206) <- #mem206_v];
        LET mem_v207 : Vector (Bit WordSz) MemAddrSz <- #mem_v206@[$$(natToWord MemAddrSz 207) <- #mem207_v];
        LET mem_v208 : Vector (Bit WordSz) MemAddrSz <- #mem_v207@[$$(natToWord MemAddrSz 208) <- #mem208_v];
        LET mem_v209 : Vector (Bit WordSz) MemAddrSz <- #mem_v208@[$$(natToWord MemAddrSz 209) <- #mem209_v];
        LET mem_v210 : Vector (Bit WordSz) MemAddrSz <- #mem_v209@[$$(natToWord MemAddrSz 210) <- #mem210_v];
        LET mem_v211 : Vector (Bit WordSz) MemAddrSz <- #mem_v210@[$$(natToWord MemAddrSz 211) <- #mem211_v];
        LET mem_v212 : Vector (Bit WordSz) MemAddrSz <- #mem_v211@[$$(natToWord MemAddrSz 212) <- #mem212_v];
        LET mem_v213 : Vector (Bit WordSz) MemAddrSz <- #mem_v212@[$$(natToWord MemAddrSz 213) <- #mem213_v];
        LET mem_v214 : Vector (Bit WordSz) MemAddrSz <- #mem_v213@[$$(natToWord MemAddrSz 214) <- #mem214_v];
        LET mem_v215 : Vector (Bit WordSz) MemAddrSz <- #mem_v214@[$$(natToWord MemAddrSz 215) <- #mem215_v];
        LET mem_v216 : Vector (Bit WordSz) MemAddrSz <- #mem_v215@[$$(natToWord MemAddrSz 216) <- #mem216_v];
        LET mem_v217 : Vector (Bit WordSz) MemAddrSz <- #mem_v216@[$$(natToWord MemAddrSz 217) <- #mem217_v];
        LET mem_v218 : Vector (Bit WordSz) MemAddrSz <- #mem_v217@[$$(natToWord MemAddrSz 218) <- #mem218_v];
        LET mem_v219 : Vector (Bit WordSz) MemAddrSz <- #mem_v218@[$$(natToWord MemAddrSz 219) <- #mem219_v];
        LET mem_v220 : Vector (Bit WordSz) MemAddrSz <- #mem_v219@[$$(natToWord MemAddrSz 220) <- #mem220_v];
        LET mem_v221 : Vector (Bit WordSz) MemAddrSz <- #mem_v220@[$$(natToWord MemAddrSz 221) <- #mem221_v];
        LET mem_v222 : Vector (Bit WordSz) MemAddrSz <- #mem_v221@[$$(natToWord MemAddrSz 222) <- #mem222_v];
        LET mem_v223 : Vector (Bit WordSz) MemAddrSz <- #mem_v222@[$$(natToWord MemAddrSz 223) <- #mem223_v];
        LET mem_v224 : Vector (Bit WordSz) MemAddrSz <- #mem_v223@[$$(natToWord MemAddrSz 224) <- #mem224_v];
        LET mem_v225 : Vector (Bit WordSz) MemAddrSz <- #mem_v224@[$$(natToWord MemAddrSz 225) <- #mem225_v];
        LET mem_v226 : Vector (Bit WordSz) MemAddrSz <- #mem_v225@[$$(natToWord MemAddrSz 226) <- #mem226_v];
        LET mem_v227 : Vector (Bit WordSz) MemAddrSz <- #mem_v226@[$$(natToWord MemAddrSz 227) <- #mem227_v];
        LET mem_v228 : Vector (Bit WordSz) MemAddrSz <- #mem_v227@[$$(natToWord MemAddrSz 228) <- #mem228_v];
        LET mem_v229 : Vector (Bit WordSz) MemAddrSz <- #mem_v228@[$$(natToWord MemAddrSz 229) <- #mem229_v];
        LET mem_v230 : Vector (Bit WordSz) MemAddrSz <- #mem_v229@[$$(natToWord MemAddrSz 230) <- #mem230_v];
        LET mem_v231 : Vector (Bit WordSz) MemAddrSz <- #mem_v230@[$$(natToWord MemAddrSz 231) <- #mem231_v];
        LET mem_v232 : Vector (Bit WordSz) MemAddrSz <- #mem_v231@[$$(natToWord MemAddrSz 232) <- #mem232_v];
        LET mem_v233 : Vector (Bit WordSz) MemAddrSz <- #mem_v232@[$$(natToWord MemAddrSz 233) <- #mem233_v];
        LET mem_v234 : Vector (Bit WordSz) MemAddrSz <- #mem_v233@[$$(natToWord MemAddrSz 234) <- #mem234_v];
        LET mem_v235 : Vector (Bit WordSz) MemAddrSz <- #mem_v234@[$$(natToWord MemAddrSz 235) <- #mem235_v];
        LET mem_v236 : Vector (Bit WordSz) MemAddrSz <- #mem_v235@[$$(natToWord MemAddrSz 236) <- #mem236_v];
        LET mem_v237 : Vector (Bit WordSz) MemAddrSz <- #mem_v236@[$$(natToWord MemAddrSz 237) <- #mem237_v];
        LET mem_v238 : Vector (Bit WordSz) MemAddrSz <- #mem_v237@[$$(natToWord MemAddrSz 238) <- #mem238_v];
        LET mem_v239 : Vector (Bit WordSz) MemAddrSz <- #mem_v238@[$$(natToWord MemAddrSz 239) <- #mem239_v];
        LET mem_v240 : Vector (Bit WordSz) MemAddrSz <- #mem_v239@[$$(natToWord MemAddrSz 240) <- #mem240_v];
        LET mem_v241 : Vector (Bit WordSz) MemAddrSz <- #mem_v240@[$$(natToWord MemAddrSz 241) <- #mem241_v];
        LET mem_v242 : Vector (Bit WordSz) MemAddrSz <- #mem_v241@[$$(natToWord MemAddrSz 242) <- #mem242_v];
        LET mem_v243 : Vector (Bit WordSz) MemAddrSz <- #mem_v242@[$$(natToWord MemAddrSz 243) <- #mem243_v];
        LET mem_v244 : Vector (Bit WordSz) MemAddrSz <- #mem_v243@[$$(natToWord MemAddrSz 244) <- #mem244_v];
        LET mem_v245 : Vector (Bit WordSz) MemAddrSz <- #mem_v244@[$$(natToWord MemAddrSz 245) <- #mem245_v];
        LET mem_v246 : Vector (Bit WordSz) MemAddrSz <- #mem_v245@[$$(natToWord MemAddrSz 246) <- #mem246_v];
        LET mem_v247 : Vector (Bit WordSz) MemAddrSz <- #mem_v246@[$$(natToWord MemAddrSz 247) <- #mem247_v];
        LET mem_v248 : Vector (Bit WordSz) MemAddrSz <- #mem_v247@[$$(natToWord MemAddrSz 248) <- #mem248_v];
        LET mem_v249 : Vector (Bit WordSz) MemAddrSz <- #mem_v248@[$$(natToWord MemAddrSz 249) <- #mem249_v];
        LET mem_v250 : Vector (Bit WordSz) MemAddrSz <- #mem_v249@[$$(natToWord MemAddrSz 250) <- #mem250_v];
        LET mem_v251 : Vector (Bit WordSz) MemAddrSz <- #mem_v250@[$$(natToWord MemAddrSz 251) <- #mem251_v];
        LET mem_v252 : Vector (Bit WordSz) MemAddrSz <- #mem_v251@[$$(natToWord MemAddrSz 252) <- #mem252_v];
        LET mem_v253 : Vector (Bit WordSz) MemAddrSz <- #mem_v252@[$$(natToWord MemAddrSz 253) <- #mem253_v];
        LET mem_v254 : Vector (Bit WordSz) MemAddrSz <- #mem_v253@[$$(natToWord MemAddrSz 254) <- #mem254_v];
        LET mem_v255 : Vector (Bit WordSz) MemAddrSz <- #mem_v254@[$$(natToWord MemAddrSz 255) <- #mem255_v];
        LET mem_v : Vector (Bit WordSz) MemAddrSz <- #mem_v255;
        Read imem_v : Vector (Bit InstrSz) MemAddrSz <- "imem";

        LET regs_v0 : Vector (Bit WordSz) RegIdxSz <- $$Default@[$$(natToWord RegIdxSz 0) <- #reg0_v];
        LET regs_v1 : Vector (Bit WordSz) RegIdxSz <- #regs_v0@[$$(natToWord RegIdxSz 1) <- #reg1_v];
        LET regs_v2 : Vector (Bit WordSz) RegIdxSz <- #regs_v1@[$$(natToWord RegIdxSz 2) <- #reg2_v];
        LET regs_v3 : Vector (Bit WordSz) RegIdxSz <- #regs_v2@[$$(natToWord RegIdxSz 3) <- #reg3_v];
        LET regs_v4 : Vector (Bit WordSz) RegIdxSz <- #regs_v3@[$$(natToWord RegIdxSz 4) <- #reg4_v];
        LET regs_v5 : Vector (Bit WordSz) RegIdxSz <- #regs_v4@[$$(natToWord RegIdxSz 5) <- #reg5_v];
        LET regs_v6 : Vector (Bit WordSz) RegIdxSz <- #regs_v5@[$$(natToWord RegIdxSz 6) <- #reg6_v];
        LET regs_v7 : Vector (Bit WordSz) RegIdxSz <- #regs_v6@[$$(natToWord RegIdxSz 7) <- #reg7_v];
        LET regs_v8 : Vector (Bit WordSz) RegIdxSz <- #regs_v7@[$$(natToWord RegIdxSz 8) <- #reg8_v];
        LET regs_v9 : Vector (Bit WordSz) RegIdxSz <- #regs_v8@[$$(natToWord RegIdxSz 9) <- #reg9_v];
        LET regs_v10 : Vector (Bit WordSz) RegIdxSz <- #regs_v9@[$$(natToWord RegIdxSz 10) <- #reg10_v];
        LET regs_v11 : Vector (Bit WordSz) RegIdxSz <- #regs_v10@[$$(natToWord RegIdxSz 11) <- #reg11_v];
        LET regs_v12 : Vector (Bit WordSz) RegIdxSz <- #regs_v11@[$$(natToWord RegIdxSz 12) <- #reg12_v];
        LET regs_v13 : Vector (Bit WordSz) RegIdxSz <- #regs_v12@[$$(natToWord RegIdxSz 13) <- #reg13_v];
        LET regs_v14 : Vector (Bit WordSz) RegIdxSz <- #regs_v13@[$$(natToWord RegIdxSz 14) <- #reg14_v];
        LET regs_v15 : Vector (Bit WordSz) RegIdxSz <- #regs_v14@[$$(natToWord RegIdxSz 15) <- #reg15_v];
        LET regs_v16 : Vector (Bit WordSz) RegIdxSz <- #regs_v15@[$$(natToWord RegIdxSz 16) <- #reg16_v];
        LET regs_v17 : Vector (Bit WordSz) RegIdxSz <- #regs_v16@[$$(natToWord RegIdxSz 17) <- #reg17_v];
        LET regs_v18 : Vector (Bit WordSz) RegIdxSz <- #regs_v17@[$$(natToWord RegIdxSz 18) <- #reg18_v];
        LET regs_v19 : Vector (Bit WordSz) RegIdxSz <- #regs_v18@[$$(natToWord RegIdxSz 19) <- #reg19_v];
        LET regs_v20 : Vector (Bit WordSz) RegIdxSz <- #regs_v19@[$$(natToWord RegIdxSz 20) <- #reg20_v];
        LET regs_v21 : Vector (Bit WordSz) RegIdxSz <- #regs_v20@[$$(natToWord RegIdxSz 21) <- #reg21_v];
        LET regs_v22 : Vector (Bit WordSz) RegIdxSz <- #regs_v21@[$$(natToWord RegIdxSz 22) <- #reg22_v];
        LET regs_v23 : Vector (Bit WordSz) RegIdxSz <- #regs_v22@[$$(natToWord RegIdxSz 23) <- #reg23_v];
        LET regs_v24 : Vector (Bit WordSz) RegIdxSz <- #regs_v23@[$$(natToWord RegIdxSz 24) <- #reg24_v];
        LET regs_v25 : Vector (Bit WordSz) RegIdxSz <- #regs_v24@[$$(natToWord RegIdxSz 25) <- #reg25_v];
        LET regs_v26 : Vector (Bit WordSz) RegIdxSz <- #regs_v25@[$$(natToWord RegIdxSz 26) <- #reg26_v];
        LET regs_v27 : Vector (Bit WordSz) RegIdxSz <- #regs_v26@[$$(natToWord RegIdxSz 27) <- #reg27_v];
        LET regs_v28 : Vector (Bit WordSz) RegIdxSz <- #regs_v27@[$$(natToWord RegIdxSz 28) <- #reg28_v];
        LET regs_v29 : Vector (Bit WordSz) RegIdxSz <- #regs_v28@[$$(natToWord RegIdxSz 29) <- #reg29_v];
        LET regs_v30 : Vector (Bit WordSz) RegIdxSz <- #regs_v29@[$$(natToWord RegIdxSz 30) <- #reg30_v];
        LET regs_v31 : Vector (Bit WordSz) RegIdxSz <- #regs_v30@[$$(natToWord RegIdxSz 31) <- #reg31_v];
        LET regs_v : Vector (Bit WordSz) RegIdxSz <- #regs_v31;
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
        Read pt0_v : Bit WordSz <- "pt0";
        Read pt1_v : Bit WordSz <- "pt1";
        Read pt2_v : Bit WordSz <- "pt2";
        Read pt3_v : Bit WordSz <- "pt3";
        Read pt4_v : Bit WordSz <- "pt4";
        Read pt5_v : Bit WordSz <- "pt5";
        Read pt6_v : Bit WordSz <- "pt6";
        Read pt7_v : Bit WordSz <- "pt7";
        Read pt8_v : Bit WordSz <- "pt8";
        Read pt9_v : Bit WordSz <- "pt9";
        Read pt10_v : Bit WordSz <- "pt10";
        Read pt11_v : Bit WordSz <- "pt11";
        Read pt12_v : Bit WordSz <- "pt12";
        Read pt13_v : Bit WordSz <- "pt13";
        Read pt14_v : Bit WordSz <- "pt14";
        Read pt15_v : Bit WordSz <- "pt15";
        Read pt_next_id_v : Bit WordSz <- "pt_next_id";

        LET pt_sizes_v0 : Vector (Bit WordSz) PTableIdxSz <- $$Default@[$$(natToWord PTableIdxSz 0) <- #pt0_v];
        LET pt_sizes_v1 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v0@[$$(natToWord PTableIdxSz 1) <- #pt1_v];
        LET pt_sizes_v2 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v1@[$$(natToWord PTableIdxSz 2) <- #pt2_v];
        LET pt_sizes_v3 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v2@[$$(natToWord PTableIdxSz 3) <- #pt3_v];
        LET pt_sizes_v4 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v3@[$$(natToWord PTableIdxSz 4) <- #pt4_v];
        LET pt_sizes_v5 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v4@[$$(natToWord PTableIdxSz 5) <- #pt5_v];
        LET pt_sizes_v6 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v5@[$$(natToWord PTableIdxSz 6) <- #pt6_v];
        LET pt_sizes_v7 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v6@[$$(natToWord PTableIdxSz 7) <- #pt7_v];
        LET pt_sizes_v8 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v7@[$$(natToWord PTableIdxSz 8) <- #pt8_v];
        LET pt_sizes_v9 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v8@[$$(natToWord PTableIdxSz 9) <- #pt9_v];
        LET pt_sizes_v10 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v9@[$$(natToWord PTableIdxSz 10) <- #pt10_v];
        LET pt_sizes_v11 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v10@[$$(natToWord PTableIdxSz 11) <- #pt11_v];
        LET pt_sizes_v12 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v11@[$$(natToWord PTableIdxSz 12) <- #pt12_v];
        LET pt_sizes_v13 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v12@[$$(natToWord PTableIdxSz 13) <- #pt13_v];
        LET pt_sizes_v14 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v13@[$$(natToWord PTableIdxSz 14) <- #pt14_v];
        LET pt_sizes_v15 : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v14@[$$(natToWord PTableIdxSz 15) <- #pt15_v];
        LET pt_sizes_v : Vector (Bit WordSz) PTableIdxSz <- #pt_sizes_v15;

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
        LET mem_val : Bit WordSz <- read_mem #mem_addr #mem_v;

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
        LET is_load_op <- (#opcode == $$(OP_LOAD)) || (#opcode == $$(OP_XOR_LOAD));
        LET is_store_op <- #opcode == $$(OP_STORE);
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
        LET ptable_room_one <- #pt_next_id_v < $64;
        LET ptable_room_two <- (#pt_next_id_v + $1) < $64;
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
          IF (#bianchi_violation || #locality_violation || #ptable_overflow_violation || #high_value_locked || #nfi_violation)
          then #mem_v
          else (IF (#opcode == $$(OP_STORE))
          then write_mem #mem_addr_a #src_val #mem_v
          else (IF (#opcode == $$(OP_CALL))
                then write_mem #sp_addr #pc_plus_1 #mem_v
          else #mem_v));

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
          IF (#bianchi_violation || #ptable_overflow_violation)
          then #pt_sizes_v
          else (IF (#opcode == $$(OP_PNEW))
                then #pt_after_pnew
                else (IF (#opcode == $$(OP_PSPLIT))
                      then #pt_after_psplit
                      else (IF (#opcode == $$(OP_PMERGE))
                            then #pt_after_pmerge
                            else #pt_sizes_v)));

        LET new_pt_next_id : Bit WordSz <-
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
          then #logic_stall_v
          else (IF #logic_rsp_fire then $$false else (IF #logic_issue then $$true else #logic_stall_v));
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
        Write "reg0"           <- #new_regs@[$$(natToWord RegIdxSz 0)];
        Write "reg1"           <- #new_regs@[$$(natToWord RegIdxSz 1)];
        Write "reg2"           <- #new_regs@[$$(natToWord RegIdxSz 2)];
        Write "reg3"           <- #new_regs@[$$(natToWord RegIdxSz 3)];
        Write "reg4"           <- #new_regs@[$$(natToWord RegIdxSz 4)];
        Write "reg5"           <- #new_regs@[$$(natToWord RegIdxSz 5)];
        Write "reg6"           <- #new_regs@[$$(natToWord RegIdxSz 6)];
        Write "reg7"           <- #new_regs@[$$(natToWord RegIdxSz 7)];
        Write "reg8"           <- #new_regs@[$$(natToWord RegIdxSz 8)];
        Write "reg9"           <- #new_regs@[$$(natToWord RegIdxSz 9)];
        Write "reg10"           <- #new_regs@[$$(natToWord RegIdxSz 10)];
        Write "reg11"           <- #new_regs@[$$(natToWord RegIdxSz 11)];
        Write "reg12"           <- #new_regs@[$$(natToWord RegIdxSz 12)];
        Write "reg13"           <- #new_regs@[$$(natToWord RegIdxSz 13)];
        Write "reg14"           <- #new_regs@[$$(natToWord RegIdxSz 14)];
        Write "reg15"           <- #new_regs@[$$(natToWord RegIdxSz 15)];
        Write "reg16"           <- #new_regs@[$$(natToWord RegIdxSz 16)];
        Write "reg17"           <- #new_regs@[$$(natToWord RegIdxSz 17)];
        Write "reg18"           <- #new_regs@[$$(natToWord RegIdxSz 18)];
        Write "reg19"           <- #new_regs@[$$(natToWord RegIdxSz 19)];
        Write "reg20"           <- #new_regs@[$$(natToWord RegIdxSz 20)];
        Write "reg21"           <- #new_regs@[$$(natToWord RegIdxSz 21)];
        Write "reg22"           <- #new_regs@[$$(natToWord RegIdxSz 22)];
        Write "reg23"           <- #new_regs@[$$(natToWord RegIdxSz 23)];
        Write "reg24"           <- #new_regs@[$$(natToWord RegIdxSz 24)];
        Write "reg25"           <- #new_regs@[$$(natToWord RegIdxSz 25)];
        Write "reg26"           <- #new_regs@[$$(natToWord RegIdxSz 26)];
        Write "reg27"           <- #new_regs@[$$(natToWord RegIdxSz 27)];
        Write "reg28"           <- #new_regs@[$$(natToWord RegIdxSz 28)];
        Write "reg29"           <- #new_regs@[$$(natToWord RegIdxSz 29)];
        Write "reg30"           <- #new_regs@[$$(natToWord RegIdxSz 30)];
        Write "reg31"           <- #new_regs@[$$(natToWord RegIdxSz 31)];
        Write "mem0"          <- #new_mem@[$$(natToWord MemAddrSz 0)];
        Write "mem1"          <- #new_mem@[$$(natToWord MemAddrSz 1)];
        Write "mem2"          <- #new_mem@[$$(natToWord MemAddrSz 2)];
        Write "mem3"          <- #new_mem@[$$(natToWord MemAddrSz 3)];
        Write "mem4"          <- #new_mem@[$$(natToWord MemAddrSz 4)];
        Write "mem5"          <- #new_mem@[$$(natToWord MemAddrSz 5)];
        Write "mem6"          <- #new_mem@[$$(natToWord MemAddrSz 6)];
        Write "mem7"          <- #new_mem@[$$(natToWord MemAddrSz 7)];
        Write "mem8"          <- #new_mem@[$$(natToWord MemAddrSz 8)];
        Write "mem9"          <- #new_mem@[$$(natToWord MemAddrSz 9)];
        Write "mem10"          <- #new_mem@[$$(natToWord MemAddrSz 10)];
        Write "mem11"          <- #new_mem@[$$(natToWord MemAddrSz 11)];
        Write "mem12"          <- #new_mem@[$$(natToWord MemAddrSz 12)];
        Write "mem13"          <- #new_mem@[$$(natToWord MemAddrSz 13)];
        Write "mem14"          <- #new_mem@[$$(natToWord MemAddrSz 14)];
        Write "mem15"          <- #new_mem@[$$(natToWord MemAddrSz 15)];
        Write "mem16"          <- #new_mem@[$$(natToWord MemAddrSz 16)];
        Write "mem17"          <- #new_mem@[$$(natToWord MemAddrSz 17)];
        Write "mem18"          <- #new_mem@[$$(natToWord MemAddrSz 18)];
        Write "mem19"          <- #new_mem@[$$(natToWord MemAddrSz 19)];
        Write "mem20"          <- #new_mem@[$$(natToWord MemAddrSz 20)];
        Write "mem21"          <- #new_mem@[$$(natToWord MemAddrSz 21)];
        Write "mem22"          <- #new_mem@[$$(natToWord MemAddrSz 22)];
        Write "mem23"          <- #new_mem@[$$(natToWord MemAddrSz 23)];
        Write "mem24"          <- #new_mem@[$$(natToWord MemAddrSz 24)];
        Write "mem25"          <- #new_mem@[$$(natToWord MemAddrSz 25)];
        Write "mem26"          <- #new_mem@[$$(natToWord MemAddrSz 26)];
        Write "mem27"          <- #new_mem@[$$(natToWord MemAddrSz 27)];
        Write "mem28"          <- #new_mem@[$$(natToWord MemAddrSz 28)];
        Write "mem29"          <- #new_mem@[$$(natToWord MemAddrSz 29)];
        Write "mem30"          <- #new_mem@[$$(natToWord MemAddrSz 30)];
        Write "mem31"          <- #new_mem@[$$(natToWord MemAddrSz 31)];
        Write "mem32"          <- #new_mem@[$$(natToWord MemAddrSz 32)];
        Write "mem33"          <- #new_mem@[$$(natToWord MemAddrSz 33)];
        Write "mem34"          <- #new_mem@[$$(natToWord MemAddrSz 34)];
        Write "mem35"          <- #new_mem@[$$(natToWord MemAddrSz 35)];
        Write "mem36"          <- #new_mem@[$$(natToWord MemAddrSz 36)];
        Write "mem37"          <- #new_mem@[$$(natToWord MemAddrSz 37)];
        Write "mem38"          <- #new_mem@[$$(natToWord MemAddrSz 38)];
        Write "mem39"          <- #new_mem@[$$(natToWord MemAddrSz 39)];
        Write "mem40"          <- #new_mem@[$$(natToWord MemAddrSz 40)];
        Write "mem41"          <- #new_mem@[$$(natToWord MemAddrSz 41)];
        Write "mem42"          <- #new_mem@[$$(natToWord MemAddrSz 42)];
        Write "mem43"          <- #new_mem@[$$(natToWord MemAddrSz 43)];
        Write "mem44"          <- #new_mem@[$$(natToWord MemAddrSz 44)];
        Write "mem45"          <- #new_mem@[$$(natToWord MemAddrSz 45)];
        Write "mem46"          <- #new_mem@[$$(natToWord MemAddrSz 46)];
        Write "mem47"          <- #new_mem@[$$(natToWord MemAddrSz 47)];
        Write "mem48"          <- #new_mem@[$$(natToWord MemAddrSz 48)];
        Write "mem49"          <- #new_mem@[$$(natToWord MemAddrSz 49)];
        Write "mem50"          <- #new_mem@[$$(natToWord MemAddrSz 50)];
        Write "mem51"          <- #new_mem@[$$(natToWord MemAddrSz 51)];
        Write "mem52"          <- #new_mem@[$$(natToWord MemAddrSz 52)];
        Write "mem53"          <- #new_mem@[$$(natToWord MemAddrSz 53)];
        Write "mem54"          <- #new_mem@[$$(natToWord MemAddrSz 54)];
        Write "mem55"          <- #new_mem@[$$(natToWord MemAddrSz 55)];
        Write "mem56"          <- #new_mem@[$$(natToWord MemAddrSz 56)];
        Write "mem57"          <- #new_mem@[$$(natToWord MemAddrSz 57)];
        Write "mem58"          <- #new_mem@[$$(natToWord MemAddrSz 58)];
        Write "mem59"          <- #new_mem@[$$(natToWord MemAddrSz 59)];
        Write "mem60"          <- #new_mem@[$$(natToWord MemAddrSz 60)];
        Write "mem61"          <- #new_mem@[$$(natToWord MemAddrSz 61)];
        Write "mem62"          <- #new_mem@[$$(natToWord MemAddrSz 62)];
        Write "mem63"          <- #new_mem@[$$(natToWord MemAddrSz 63)];
        Write "mem64"          <- #new_mem@[$$(natToWord MemAddrSz 64)];
        Write "mem65"          <- #new_mem@[$$(natToWord MemAddrSz 65)];
        Write "mem66"          <- #new_mem@[$$(natToWord MemAddrSz 66)];
        Write "mem67"          <- #new_mem@[$$(natToWord MemAddrSz 67)];
        Write "mem68"          <- #new_mem@[$$(natToWord MemAddrSz 68)];
        Write "mem69"          <- #new_mem@[$$(natToWord MemAddrSz 69)];
        Write "mem70"          <- #new_mem@[$$(natToWord MemAddrSz 70)];
        Write "mem71"          <- #new_mem@[$$(natToWord MemAddrSz 71)];
        Write "mem72"          <- #new_mem@[$$(natToWord MemAddrSz 72)];
        Write "mem73"          <- #new_mem@[$$(natToWord MemAddrSz 73)];
        Write "mem74"          <- #new_mem@[$$(natToWord MemAddrSz 74)];
        Write "mem75"          <- #new_mem@[$$(natToWord MemAddrSz 75)];
        Write "mem76"          <- #new_mem@[$$(natToWord MemAddrSz 76)];
        Write "mem77"          <- #new_mem@[$$(natToWord MemAddrSz 77)];
        Write "mem78"          <- #new_mem@[$$(natToWord MemAddrSz 78)];
        Write "mem79"          <- #new_mem@[$$(natToWord MemAddrSz 79)];
        Write "mem80"          <- #new_mem@[$$(natToWord MemAddrSz 80)];
        Write "mem81"          <- #new_mem@[$$(natToWord MemAddrSz 81)];
        Write "mem82"          <- #new_mem@[$$(natToWord MemAddrSz 82)];
        Write "mem83"          <- #new_mem@[$$(natToWord MemAddrSz 83)];
        Write "mem84"          <- #new_mem@[$$(natToWord MemAddrSz 84)];
        Write "mem85"          <- #new_mem@[$$(natToWord MemAddrSz 85)];
        Write "mem86"          <- #new_mem@[$$(natToWord MemAddrSz 86)];
        Write "mem87"          <- #new_mem@[$$(natToWord MemAddrSz 87)];
        Write "mem88"          <- #new_mem@[$$(natToWord MemAddrSz 88)];
        Write "mem89"          <- #new_mem@[$$(natToWord MemAddrSz 89)];
        Write "mem90"          <- #new_mem@[$$(natToWord MemAddrSz 90)];
        Write "mem91"          <- #new_mem@[$$(natToWord MemAddrSz 91)];
        Write "mem92"          <- #new_mem@[$$(natToWord MemAddrSz 92)];
        Write "mem93"          <- #new_mem@[$$(natToWord MemAddrSz 93)];
        Write "mem94"          <- #new_mem@[$$(natToWord MemAddrSz 94)];
        Write "mem95"          <- #new_mem@[$$(natToWord MemAddrSz 95)];
        Write "mem96"          <- #new_mem@[$$(natToWord MemAddrSz 96)];
        Write "mem97"          <- #new_mem@[$$(natToWord MemAddrSz 97)];
        Write "mem98"          <- #new_mem@[$$(natToWord MemAddrSz 98)];
        Write "mem99"          <- #new_mem@[$$(natToWord MemAddrSz 99)];
        Write "mem100"          <- #new_mem@[$$(natToWord MemAddrSz 100)];
        Write "mem101"          <- #new_mem@[$$(natToWord MemAddrSz 101)];
        Write "mem102"          <- #new_mem@[$$(natToWord MemAddrSz 102)];
        Write "mem103"          <- #new_mem@[$$(natToWord MemAddrSz 103)];
        Write "mem104"          <- #new_mem@[$$(natToWord MemAddrSz 104)];
        Write "mem105"          <- #new_mem@[$$(natToWord MemAddrSz 105)];
        Write "mem106"          <- #new_mem@[$$(natToWord MemAddrSz 106)];
        Write "mem107"          <- #new_mem@[$$(natToWord MemAddrSz 107)];
        Write "mem108"          <- #new_mem@[$$(natToWord MemAddrSz 108)];
        Write "mem109"          <- #new_mem@[$$(natToWord MemAddrSz 109)];
        Write "mem110"          <- #new_mem@[$$(natToWord MemAddrSz 110)];
        Write "mem111"          <- #new_mem@[$$(natToWord MemAddrSz 111)];
        Write "mem112"          <- #new_mem@[$$(natToWord MemAddrSz 112)];
        Write "mem113"          <- #new_mem@[$$(natToWord MemAddrSz 113)];
        Write "mem114"          <- #new_mem@[$$(natToWord MemAddrSz 114)];
        Write "mem115"          <- #new_mem@[$$(natToWord MemAddrSz 115)];
        Write "mem116"          <- #new_mem@[$$(natToWord MemAddrSz 116)];
        Write "mem117"          <- #new_mem@[$$(natToWord MemAddrSz 117)];
        Write "mem118"          <- #new_mem@[$$(natToWord MemAddrSz 118)];
        Write "mem119"          <- #new_mem@[$$(natToWord MemAddrSz 119)];
        Write "mem120"          <- #new_mem@[$$(natToWord MemAddrSz 120)];
        Write "mem121"          <- #new_mem@[$$(natToWord MemAddrSz 121)];
        Write "mem122"          <- #new_mem@[$$(natToWord MemAddrSz 122)];
        Write "mem123"          <- #new_mem@[$$(natToWord MemAddrSz 123)];
        Write "mem124"          <- #new_mem@[$$(natToWord MemAddrSz 124)];
        Write "mem125"          <- #new_mem@[$$(natToWord MemAddrSz 125)];
        Write "mem126"          <- #new_mem@[$$(natToWord MemAddrSz 126)];
        Write "mem127"          <- #new_mem@[$$(natToWord MemAddrSz 127)];
        Write "mem128"          <- #new_mem@[$$(natToWord MemAddrSz 128)];
        Write "mem129"          <- #new_mem@[$$(natToWord MemAddrSz 129)];
        Write "mem130"          <- #new_mem@[$$(natToWord MemAddrSz 130)];
        Write "mem131"          <- #new_mem@[$$(natToWord MemAddrSz 131)];
        Write "mem132"          <- #new_mem@[$$(natToWord MemAddrSz 132)];
        Write "mem133"          <- #new_mem@[$$(natToWord MemAddrSz 133)];
        Write "mem134"          <- #new_mem@[$$(natToWord MemAddrSz 134)];
        Write "mem135"          <- #new_mem@[$$(natToWord MemAddrSz 135)];
        Write "mem136"          <- #new_mem@[$$(natToWord MemAddrSz 136)];
        Write "mem137"          <- #new_mem@[$$(natToWord MemAddrSz 137)];
        Write "mem138"          <- #new_mem@[$$(natToWord MemAddrSz 138)];
        Write "mem139"          <- #new_mem@[$$(natToWord MemAddrSz 139)];
        Write "mem140"          <- #new_mem@[$$(natToWord MemAddrSz 140)];
        Write "mem141"          <- #new_mem@[$$(natToWord MemAddrSz 141)];
        Write "mem142"          <- #new_mem@[$$(natToWord MemAddrSz 142)];
        Write "mem143"          <- #new_mem@[$$(natToWord MemAddrSz 143)];
        Write "mem144"          <- #new_mem@[$$(natToWord MemAddrSz 144)];
        Write "mem145"          <- #new_mem@[$$(natToWord MemAddrSz 145)];
        Write "mem146"          <- #new_mem@[$$(natToWord MemAddrSz 146)];
        Write "mem147"          <- #new_mem@[$$(natToWord MemAddrSz 147)];
        Write "mem148"          <- #new_mem@[$$(natToWord MemAddrSz 148)];
        Write "mem149"          <- #new_mem@[$$(natToWord MemAddrSz 149)];
        Write "mem150"          <- #new_mem@[$$(natToWord MemAddrSz 150)];
        Write "mem151"          <- #new_mem@[$$(natToWord MemAddrSz 151)];
        Write "mem152"          <- #new_mem@[$$(natToWord MemAddrSz 152)];
        Write "mem153"          <- #new_mem@[$$(natToWord MemAddrSz 153)];
        Write "mem154"          <- #new_mem@[$$(natToWord MemAddrSz 154)];
        Write "mem155"          <- #new_mem@[$$(natToWord MemAddrSz 155)];
        Write "mem156"          <- #new_mem@[$$(natToWord MemAddrSz 156)];
        Write "mem157"          <- #new_mem@[$$(natToWord MemAddrSz 157)];
        Write "mem158"          <- #new_mem@[$$(natToWord MemAddrSz 158)];
        Write "mem159"          <- #new_mem@[$$(natToWord MemAddrSz 159)];
        Write "mem160"          <- #new_mem@[$$(natToWord MemAddrSz 160)];
        Write "mem161"          <- #new_mem@[$$(natToWord MemAddrSz 161)];
        Write "mem162"          <- #new_mem@[$$(natToWord MemAddrSz 162)];
        Write "mem163"          <- #new_mem@[$$(natToWord MemAddrSz 163)];
        Write "mem164"          <- #new_mem@[$$(natToWord MemAddrSz 164)];
        Write "mem165"          <- #new_mem@[$$(natToWord MemAddrSz 165)];
        Write "mem166"          <- #new_mem@[$$(natToWord MemAddrSz 166)];
        Write "mem167"          <- #new_mem@[$$(natToWord MemAddrSz 167)];
        Write "mem168"          <- #new_mem@[$$(natToWord MemAddrSz 168)];
        Write "mem169"          <- #new_mem@[$$(natToWord MemAddrSz 169)];
        Write "mem170"          <- #new_mem@[$$(natToWord MemAddrSz 170)];
        Write "mem171"          <- #new_mem@[$$(natToWord MemAddrSz 171)];
        Write "mem172"          <- #new_mem@[$$(natToWord MemAddrSz 172)];
        Write "mem173"          <- #new_mem@[$$(natToWord MemAddrSz 173)];
        Write "mem174"          <- #new_mem@[$$(natToWord MemAddrSz 174)];
        Write "mem175"          <- #new_mem@[$$(natToWord MemAddrSz 175)];
        Write "mem176"          <- #new_mem@[$$(natToWord MemAddrSz 176)];
        Write "mem177"          <- #new_mem@[$$(natToWord MemAddrSz 177)];
        Write "mem178"          <- #new_mem@[$$(natToWord MemAddrSz 178)];
        Write "mem179"          <- #new_mem@[$$(natToWord MemAddrSz 179)];
        Write "mem180"          <- #new_mem@[$$(natToWord MemAddrSz 180)];
        Write "mem181"          <- #new_mem@[$$(natToWord MemAddrSz 181)];
        Write "mem182"          <- #new_mem@[$$(natToWord MemAddrSz 182)];
        Write "mem183"          <- #new_mem@[$$(natToWord MemAddrSz 183)];
        Write "mem184"          <- #new_mem@[$$(natToWord MemAddrSz 184)];
        Write "mem185"          <- #new_mem@[$$(natToWord MemAddrSz 185)];
        Write "mem186"          <- #new_mem@[$$(natToWord MemAddrSz 186)];
        Write "mem187"          <- #new_mem@[$$(natToWord MemAddrSz 187)];
        Write "mem188"          <- #new_mem@[$$(natToWord MemAddrSz 188)];
        Write "mem189"          <- #new_mem@[$$(natToWord MemAddrSz 189)];
        Write "mem190"          <- #new_mem@[$$(natToWord MemAddrSz 190)];
        Write "mem191"          <- #new_mem@[$$(natToWord MemAddrSz 191)];
        Write "mem192"          <- #new_mem@[$$(natToWord MemAddrSz 192)];
        Write "mem193"          <- #new_mem@[$$(natToWord MemAddrSz 193)];
        Write "mem194"          <- #new_mem@[$$(natToWord MemAddrSz 194)];
        Write "mem195"          <- #new_mem@[$$(natToWord MemAddrSz 195)];
        Write "mem196"          <- #new_mem@[$$(natToWord MemAddrSz 196)];
        Write "mem197"          <- #new_mem@[$$(natToWord MemAddrSz 197)];
        Write "mem198"          <- #new_mem@[$$(natToWord MemAddrSz 198)];
        Write "mem199"          <- #new_mem@[$$(natToWord MemAddrSz 199)];
        Write "mem200"          <- #new_mem@[$$(natToWord MemAddrSz 200)];
        Write "mem201"          <- #new_mem@[$$(natToWord MemAddrSz 201)];
        Write "mem202"          <- #new_mem@[$$(natToWord MemAddrSz 202)];
        Write "mem203"          <- #new_mem@[$$(natToWord MemAddrSz 203)];
        Write "mem204"          <- #new_mem@[$$(natToWord MemAddrSz 204)];
        Write "mem205"          <- #new_mem@[$$(natToWord MemAddrSz 205)];
        Write "mem206"          <- #new_mem@[$$(natToWord MemAddrSz 206)];
        Write "mem207"          <- #new_mem@[$$(natToWord MemAddrSz 207)];
        Write "mem208"          <- #new_mem@[$$(natToWord MemAddrSz 208)];
        Write "mem209"          <- #new_mem@[$$(natToWord MemAddrSz 209)];
        Write "mem210"          <- #new_mem@[$$(natToWord MemAddrSz 210)];
        Write "mem211"          <- #new_mem@[$$(natToWord MemAddrSz 211)];
        Write "mem212"          <- #new_mem@[$$(natToWord MemAddrSz 212)];
        Write "mem213"          <- #new_mem@[$$(natToWord MemAddrSz 213)];
        Write "mem214"          <- #new_mem@[$$(natToWord MemAddrSz 214)];
        Write "mem215"          <- #new_mem@[$$(natToWord MemAddrSz 215)];
        Write "mem216"          <- #new_mem@[$$(natToWord MemAddrSz 216)];
        Write "mem217"          <- #new_mem@[$$(natToWord MemAddrSz 217)];
        Write "mem218"          <- #new_mem@[$$(natToWord MemAddrSz 218)];
        Write "mem219"          <- #new_mem@[$$(natToWord MemAddrSz 219)];
        Write "mem220"          <- #new_mem@[$$(natToWord MemAddrSz 220)];
        Write "mem221"          <- #new_mem@[$$(natToWord MemAddrSz 221)];
        Write "mem222"          <- #new_mem@[$$(natToWord MemAddrSz 222)];
        Write "mem223"          <- #new_mem@[$$(natToWord MemAddrSz 223)];
        Write "mem224"          <- #new_mem@[$$(natToWord MemAddrSz 224)];
        Write "mem225"          <- #new_mem@[$$(natToWord MemAddrSz 225)];
        Write "mem226"          <- #new_mem@[$$(natToWord MemAddrSz 226)];
        Write "mem227"          <- #new_mem@[$$(natToWord MemAddrSz 227)];
        Write "mem228"          <- #new_mem@[$$(natToWord MemAddrSz 228)];
        Write "mem229"          <- #new_mem@[$$(natToWord MemAddrSz 229)];
        Write "mem230"          <- #new_mem@[$$(natToWord MemAddrSz 230)];
        Write "mem231"          <- #new_mem@[$$(natToWord MemAddrSz 231)];
        Write "mem232"          <- #new_mem@[$$(natToWord MemAddrSz 232)];
        Write "mem233"          <- #new_mem@[$$(natToWord MemAddrSz 233)];
        Write "mem234"          <- #new_mem@[$$(natToWord MemAddrSz 234)];
        Write "mem235"          <- #new_mem@[$$(natToWord MemAddrSz 235)];
        Write "mem236"          <- #new_mem@[$$(natToWord MemAddrSz 236)];
        Write "mem237"          <- #new_mem@[$$(natToWord MemAddrSz 237)];
        Write "mem238"          <- #new_mem@[$$(natToWord MemAddrSz 238)];
        Write "mem239"          <- #new_mem@[$$(natToWord MemAddrSz 239)];
        Write "mem240"          <- #new_mem@[$$(natToWord MemAddrSz 240)];
        Write "mem241"          <- #new_mem@[$$(natToWord MemAddrSz 241)];
        Write "mem242"          <- #new_mem@[$$(natToWord MemAddrSz 242)];
        Write "mem243"          <- #new_mem@[$$(natToWord MemAddrSz 243)];
        Write "mem244"          <- #new_mem@[$$(natToWord MemAddrSz 244)];
        Write "mem245"          <- #new_mem@[$$(natToWord MemAddrSz 245)];
        Write "mem246"          <- #new_mem@[$$(natToWord MemAddrSz 246)];
        Write "mem247"          <- #new_mem@[$$(natToWord MemAddrSz 247)];
        Write "mem248"          <- #new_mem@[$$(natToWord MemAddrSz 248)];
        Write "mem249"          <- #new_mem@[$$(natToWord MemAddrSz 249)];
        Write "mem250"          <- #new_mem@[$$(natToWord MemAddrSz 250)];
        Write "mem251"          <- #new_mem@[$$(natToWord MemAddrSz 251)];
        Write "mem252"          <- #new_mem@[$$(natToWord MemAddrSz 252)];
        Write "mem253"          <- #new_mem@[$$(natToWord MemAddrSz 253)];
        Write "mem254"          <- #new_mem@[$$(natToWord MemAddrSz 254)];
        Write "mem255"          <- #new_mem@[$$(natToWord MemAddrSz 255)];
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
        Write "pt0"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 0)];
        Write "pt1"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 1)];
        Write "pt2"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 2)];
        Write "pt3"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 3)];
        Write "pt4"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 4)];
        Write "pt5"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 5)];
        Write "pt6"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 6)];
        Write "pt7"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 7)];
        Write "pt8"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 8)];
        Write "pt9"            <- #new_pt_sizes@[$$(natToWord PTableIdxSz 9)];
        Write "pt10"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 10)];
        Write "pt11"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 11)];
        Write "pt12"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 12)];
        Write "pt13"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 13)];
        Write "pt14"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 14)];
        Write "pt15"           <- #new_pt_sizes@[$$(natToWord PTableIdxSz 15)];
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
        Read pt0_v : Bit WordSz <- "pt0";
        Read pt1_v : Bit WordSz <- "pt1";
        Read pt2_v : Bit WordSz <- "pt2";
        Read pt3_v : Bit WordSz <- "pt3";
        Read pt4_v : Bit WordSz <- "pt4";
        Read pt5_v : Bit WordSz <- "pt5";
        Read pt6_v : Bit WordSz <- "pt6";
        Read pt7_v : Bit WordSz <- "pt7";
        Read pt8_v : Bit WordSz <- "pt8";
        Read pt9_v : Bit WordSz <- "pt9";
        Read pt10_v : Bit WordSz <- "pt10";
        Read pt11_v : Bit WordSz <- "pt11";
        Read pt12_v : Bit WordSz <- "pt12";
        Read pt13_v : Bit WordSz <- "pt13";
        Read pt14_v : Bit WordSz <- "pt14";
        Read pt15_v : Bit WordSz <- "pt15";
        LET lo_idx : Bit 4 <- UniBit (Trunc 4 _) #idx;
        LET v : Bit WordSz <-
          IF (#lo_idx == $$(natToWord 4 0)) then #pt0_v else
          IF (#lo_idx == $$(natToWord 4 1)) then #pt1_v else
          IF (#lo_idx == $$(natToWord 4 2)) then #pt2_v else
          IF (#lo_idx == $$(natToWord 4 3)) then #pt3_v else
          IF (#lo_idx == $$(natToWord 4 4)) then #pt4_v else
          IF (#lo_idx == $$(natToWord 4 5)) then #pt5_v else
          IF (#lo_idx == $$(natToWord 4 6)) then #pt6_v else
          IF (#lo_idx == $$(natToWord 4 7)) then #pt7_v else
          IF (#lo_idx == $$(natToWord 4 8)) then #pt8_v else
          IF (#lo_idx == $$(natToWord 4 9)) then #pt9_v else
          IF (#lo_idx == $$(natToWord 4 10)) then #pt10_v else
          IF (#lo_idx == $$(natToWord 4 11)) then #pt11_v else
          IF (#lo_idx == $$(natToWord 4 12)) then #pt12_v else
          IF (#lo_idx == $$(natToWord 4 13)) then #pt13_v else
          IF (#lo_idx == $$(natToWord 4 14)) then #pt14_v else #pt15_v;
        Ret #v
    }.

  (** Extraction targets *)
  Definition thieleCoreS := getModuleS thieleCore.
  Definition thieleCoreB := ModulesSToBModules thieleCoreS.

End ThieleCPU.

#[global] Hint Unfold thieleCore : ModuleDefs.
