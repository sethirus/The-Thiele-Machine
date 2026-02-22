(** ThieleTypes.v — Hardware type definitions for the Kami Thiele CPU.
    Maps the Coq VMState types to fixed-size hardware representations. *)

Require Import Kami.Kami.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** Register and memory dimensions — must match VMState.v *)
Definition RegCount := 32.
Definition MemSize := 256.
Definition RegIdxSz := 5.   (* log2(32) *)
Definition MemAddrSz := 8.  (* log2(256) *)
Definition WordSz := 32.
Definition OpcodeSz := 8.
Definition CostSz := 8.
Definition MuTensorIdxSz := 4.  (* log2(16) — 4×4 flattened μ-tensor *)

(** Error code constants — must match handwritten RTL *)
Definition ERR_CHSH_VAL    : word WordSz :=
  WO~0~0~0~0~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~1~0~0~0~1~0~1~1~1~0~0. (* 0x0BADC45C *)
Definition ERR_BIANCHI_VAL : word WordSz :=
  WO~0~0~0~0~1~0~1~1~0~0~0~1~1~0~1~0~0~1~0~0~1~1~0~0~1~0~0~0~0~0~0~1. (* 0x0B1A4C81 *)

(** Opcode encoding — must match generated_opcodes.vh *)
Definition OP_PNEW         : word OpcodeSz := WO~0~0~0~0~0~0~0~0.
Definition OP_PSPLIT        : word OpcodeSz := WO~0~0~0~0~0~0~0~1.
Definition OP_PMERGE        : word OpcodeSz := WO~0~0~0~0~0~0~1~0.
Definition OP_LASSERT       : word OpcodeSz := WO~0~0~0~0~0~0~1~1.
Definition OP_LJOIN         : word OpcodeSz := WO~0~0~0~0~0~1~0~0.
Definition OP_MDLACC        : word OpcodeSz := WO~0~0~0~0~0~1~0~1.
Definition OP_PDISCOVER     : word OpcodeSz := WO~0~0~0~0~0~1~1~0.
Definition OP_XFER          : word OpcodeSz := WO~0~0~0~0~0~1~1~1.
Definition OP_LOAD_IMM      : word OpcodeSz := WO~0~0~0~0~1~0~0~0. (* 0x08 *)
Definition OP_CHSH_TRIAL    : word OpcodeSz := WO~0~0~0~0~1~0~0~1. (* 0x09 *)
Definition OP_XOR_LOAD      : word OpcodeSz := WO~0~0~0~0~1~0~1~0. (* 0x0A *)
Definition OP_XOR_ADD       : word OpcodeSz := WO~0~0~0~0~1~0~1~1. (* 0x0B *)
Definition OP_XOR_SWAP      : word OpcodeSz := WO~0~0~0~0~1~1~0~0. (* 0x0C *)
Definition OP_XOR_RANK      : word OpcodeSz := WO~0~0~0~0~1~1~0~1. (* 0x0D *)
Definition OP_EMIT          : word OpcodeSz := WO~0~0~0~0~1~1~1~0. (* 0x0E *)
Definition OP_REVEAL        : word OpcodeSz := WO~0~0~0~0~1~1~1~1. (* 0x0F *)
Definition OP_ORACLE_HALTS  : word OpcodeSz := WO~0~0~0~1~0~0~0~0. (* 0x10 *)
Definition OP_LOAD          : word OpcodeSz := WO~0~0~0~1~0~0~0~1. (* 0x11 *)
Definition OP_STORE         : word OpcodeSz := WO~0~0~0~1~0~0~1~0. (* 0x12 *)
Definition OP_ADD           : word OpcodeSz := WO~0~0~0~1~0~0~1~1. (* 0x13 *)
Definition OP_SUB           : word OpcodeSz := WO~0~0~0~1~0~1~0~0. (* 0x14 *)
Definition OP_JUMP          : word OpcodeSz := WO~0~0~0~1~0~1~0~1. (* 0x15 *)
Definition OP_JNEZ          : word OpcodeSz := WO~0~0~0~1~0~1~1~0. (* 0x16 *)
Definition OP_CALL          : word OpcodeSz := WO~0~0~0~1~0~1~1~1. (* 0x17 *)
Definition OP_RET           : word OpcodeSz := WO~0~0~0~1~1~0~0~0. (* 0x18 *)
Definition OP_HALT          : word OpcodeSz := WO~1~1~1~1~1~1~1~1. (* 0xFF *)

(** Instruction encoding: [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost *)
Definition InstrSz := 32.
