(** ThieleTypes.v — Hardware type definitions for the Kami Thiele CPU.
    Maps the Coq VMState types to fixed-size hardware representations. *)

Require Import Kami.Kami.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** Register and memory dimensions — must match VMState.v.

    The kernel proofs are parametric in these constants. The values below
    are the silicon-side bounds of the synthesized RTL (chosen to fit the
    Xilinx Artix-7 xc7a35tcsg324-1 / Arty A7-35T target through the
    open-source yosys + openXC7 toolchain); the same Coq development scales
    up linearly when bound to larger values for a different device or for
    pure simulation. *)
Definition RegCount := 16.
Definition MemSize := 128.
Definition RegIdxSz := 4.    (* log2(RegCount) *)
Definition MemAddrSz := 7.   (* log2(MemSize)  *)
Definition WordSz := 32.
Definition LegacyInstrSz := 32.
Definition InstrUpperSz := 96.
Definition InstrSz := 128.
Definition FormatIdSz := 8.
Definition FormatSubtypeSz := 4.
Definition DescKindFieldSz := 4.
Definition InlineLenSz := 8.
Definition OpcodeSz := 8.
Definition CostSz := 8.
Definition MuTensorIdxSz := 4.  (* log2(16) — 4×4 flattened μ-tensor *)

(** ISA-v2 format identifiers. *)
Definition FMT_LEGACY : word FormatIdSz :=
  WO~0~0~0~0~0~0~0~0.
Definition FMT_BRANCH_EXT : word FormatIdSz :=
  WO~0~0~0~0~0~0~0~1.
Definition FMT_TENSOR_EXT : word FormatIdSz :=
  WO~0~0~0~0~0~0~1~0.
Definition FMT_MORPH_INLINE : word FormatIdSz :=
  WO~0~0~0~0~0~0~1~1.
Definition FMT_DESC : word FormatIdSz :=
  WO~0~0~0~0~0~1~0~0.
Definition FMT_CERT_INLINE : word FormatIdSz :=
  WO~0~0~0~0~0~1~0~1.

(** Partition table sizing. Proofs reference PTableSz symbolically, so the
    constant can be retargeted by editing this one place (and adjusting
    any tactics that compute on the literal width). *)
Definition PTableIdxSz := 6.   (* log2(PTableSz) *)
Definition PTableSz := 64.     (* physically implemented partition slots *)
Definition PTableNextIdSz := 7.  (* enough to represent 0..PTableSz for trap *)

(** Rich-state table dimensions for the ISA-v2 bounded hardware model.
    Each auxiliary descriptor table holds at most $16$ live entries; the
    ISA semantics are parametric in the table sizes, and programs that
    overflow a particular table trap with the standard descriptor-range
    error code. *)
Definition DescIdxSz := 4.            (* generic descriptor identifier width *)
Definition DescTableSz := 16.
Definition DescTableNextIdSz := 5.    (* enough to represent 0..16 descriptor allocations *)
Definition MorphTableIdxSz := 4.      (* log2(16) — 16 morphism descriptors *)
Definition MorphTableSz := 16.
Definition MorphTableNextIdSz := 5.   (* enough to represent 0..16 for trap/overflow checks *)
Definition CouplingDescIdxSz := 4.    (* log2(16) — 16 coupling descriptors *)
Definition CouplingDescSz := 16.
Definition FormulaDescIdxSz := 4.     (* log2(16) — 16 formula descriptors *)
Definition FormulaDescSz := 16.
Definition CertDescIdxSz := 4.        (* log2(16) — 16 certification descriptors *)
Definition CertDescSz := 16.
Definition DescMetaIdxSz := 4.        (* log2(16) — 16 descriptor metadata records *)
Definition DescMetaSz := 16.
Definition CouplingPairIdxSz := 4.    (* bounded on-chip storage for 16 coupling pairs *)
Definition CouplingPairSz := 16.
Definition CouplingPairCountSz := 5.  (* enough to represent 0..16 pairs *)
Definition LassertFbufIdxSz := 6.     (* Vector exponent: 2^6 backing words (64) *)
Definition LassertCbufIdxSz := 6.     (* Vector exponent: 2^6 backing words (64) *)

(** Initial active module id (module slot 1). *)
Definition ACTIVE_MODULE_INIT : word PTableIdxSz :=
  WO~0~0~0~0~0~1.

(** Initial value for pt_next_id: starts at 1 to match empty_graph.pg_next_id = 1 *)
Definition PT_NEXT_ID_INIT : word PTableNextIdSz :=
  WO~0~0~0~0~0~0~1. (* value 1 *)

(** Initial value for morph_next_id: starts at 1 to match empty_graph.pg_next_morph_id = 1 *)
Definition MORPH_NEXT_ID_INIT : word MorphTableNextIdSz :=
  WO~0~0~0~0~1. (* value 1 — 5-bit *)

(** Descriptor / pair tables start empty, so their next-id counters begin at 0. *)
Definition DESC_NEXT_ID_INIT : word DescTableNextIdSz :=
  WO~0~0~0~0~0. (* 5-bit *)

(** Error code constants — must match handwritten RTL.
    Using binary literals to avoid pathological Peano extraction.
    All values are 32-bit. *)
(* ERR_CHSH_VAL = 0x0BADC45C - simplified for fast extraction *)
Definition ERR_CHSH_VAL    : word WordSz :=
  WO~0~0~0~0~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~1~0~0~0~1~0~1~1~1~0~0.
(* ERR_BIANCHI_VAL = 0x0B1A4C81 - simplified for fast extraction *)
Definition ERR_BIANCHI_VAL : word WordSz :=
  WO~0~0~0~0~1~0~1~1~0~0~0~1~1~0~1~0~0~1~0~0~1~1~0~0~1~0~0~0~0~0~0~1.
(* ERR_LOGIC_VAL = 0xC43471A1 - needs 32-bit binary literal *)
Definition ERR_LOGIC_VAL   : word WordSz :=
  WO~1~1~0~0~0~1~0~0~0~0~1~1~0~1~0~0~0~1~1~1~0~0~0~1~1~0~1~0~0~0~0~1.
(* ERR_LOCALITY_VAL = 0x0BADC0DE *)
Definition ERR_LOCALITY_VAL : word WordSz :=
  WO~0~0~0~0~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~1~1~0~1~1~1~1~0.
(* ERR_PARTITION_VAL = 0xBADF001D *)
Definition ERR_PARTITION_VAL : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~1~1~0~0~0~0~0~0~0~0~0~0~0~1~1~1~0~1.
(* ERR_COUPLING_INVALID = 0xBADC0000 — morphism coupling failed well-formedness check *)
Definition ERR_COUPLING_INVALID : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
(* ERR_COMPOSE_TYPE = 0xBADC0001 — compose type mismatch (target ≠ source) *)
Definition ERR_COMPOSE_TYPE : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1.
(* ERR_TENSOR_INVALID = 0xBADC0002 — tensor morphism precondition failed *)
Definition ERR_TENSOR_INVALID : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0.
(* ERR_MORPH_NOT_FOUND = 0xBADC0003 — morphism ID not in graph *)
Definition ERR_MORPH_NOT_FOUND : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1.
(* ERR_ISA_VERSION = 0xBADC0010 — ISA-v2 instruction version field is invalid *)
Definition ERR_ISA_VERSION : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0.
(* ERR_FORMAT_INVALID = 0xBADC0011 — reserved/unknown format_id *)
Definition ERR_FORMAT_INVALID : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~1.
(* ERR_DESC_RANGE = 0xBADC0012 — descriptor id outside bounded table range *)
Definition ERR_DESC_RANGE : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1~0.
(* ERR_INLINE_MALFORMED = 0xBADC0013 — malformed inline payload/flag layout *)
Definition ERR_INLINE_MALFORMED : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~1~1.
(* ERR_TABLE_OVERFLOW = 0xBADC0014 — bounded rich-state table allocation overflow *)
Definition ERR_TABLE_OVERFLOW : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0~0.
(* ERR_CERT_DESC_INVALID = 0xBADC0015 — formula/cert descriptor invalid or mismatched *)
Definition ERR_CERT_DESC_INVALID : word WordSz :=
  WO~1~0~1~1~1~0~1~0~1~1~0~1~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1~0~1.

(** Logic-gated physics key required for REVEAL/CHSH_TRIAL unlock.
    LOGIC_GATE_KEY = 0xCAFEEACE = 3405703886 - binary literal for fast extraction *)
Definition LOGIC_GATE_KEY : word WordSz :=
  WO~1~1~0~0~1~0~1~0~1~1~1~1~1~1~1~0~1~1~1~0~1~0~1~0~1~1~0~0~1~1~1~0.

(** Trap vector defaults (PC target for fault recovery code).
    TRAP_VEC_INIT = 0x00000F00 = 3840 - binary literal for fast extraction *)
Definition TRAP_VEC_INIT : word WordSz :=
  WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~0~0~0~0~0~0~0~0.

(** mstatus mode bits - simple values, binary literals *)
Definition MSTATUS_TURING : word WordSz :=
  WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
Definition MSTATUS_THIELE : word WordSz :=
  WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1.

(** ORACLE_HALTS_HW_COST: legacy cost ceiling constant. No opcode uses it now;
    kept for conservative cost-cap lemmas in Abstraction.v. *)
Definition ORACLE_HALTS_HW_COST : nat := 1000000.

(** CHSH x=1 surcharge constant (μ-bits).
    CHSH_X1_SURCHARGE = 0x100 = 256 - binary literal for fast extraction *)
Definition CHSH_X1_SURCHARGE : word WordSz :=
  WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0.

(** Opcode encoding — canonical source; RTL is generated via the Kami extraction chain *)
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
(* 0x10 reserved (formerly ORACLE_HALTS) *)
Definition OP_LOAD          : word OpcodeSz := WO~0~0~0~1~0~0~0~1. (* 0x11 *)
Definition OP_STORE         : word OpcodeSz := WO~0~0~0~1~0~0~1~0. (* 0x12 *)
Definition OP_ADD           : word OpcodeSz := WO~0~0~0~1~0~0~1~1. (* 0x13 *)
Definition OP_SUB           : word OpcodeSz := WO~0~0~0~1~0~1~0~0. (* 0x14 *)
Definition OP_JUMP          : word OpcodeSz := WO~0~0~0~1~0~1~0~1. (* 0x15 *)
Definition OP_JNEZ          : word OpcodeSz := WO~0~0~0~1~0~1~1~0. (* 0x16 *)
Definition OP_CALL          : word OpcodeSz := WO~0~0~0~1~0~1~1~1. (* 0x17 *)
Definition OP_RET           : word OpcodeSz := WO~0~0~0~1~1~0~0~0. (* 0x18 *)
Definition OP_CHECKPOINT    : word OpcodeSz := WO~0~0~0~1~1~0~0~1. (* 0x19 *)
Definition OP_READ_PORT     : word OpcodeSz := WO~0~0~0~1~1~0~1~0. (* 0x1A *)
Definition OP_WRITE_PORT    : word OpcodeSz := WO~0~0~0~1~1~0~1~1. (* 0x1B *)
Definition OP_HEAP_LOAD     : word OpcodeSz := WO~0~0~0~1~1~1~0~0. (* 0x1C *)
Definition OP_HEAP_STORE    : word OpcodeSz := WO~0~0~0~1~1~1~0~1. (* 0x1D *)
Definition OP_CERTIFY       : word OpcodeSz := WO~0~0~0~1~1~1~1~0. (* 0x1E *)
Definition OP_AND           : word OpcodeSz := WO~0~0~0~1~1~1~1~1. (* 0x1F *)
Definition OP_OR            : word OpcodeSz := WO~0~0~1~0~0~0~0~0. (* 0x20 *)
Definition OP_SHL           : word OpcodeSz := WO~0~0~1~0~0~0~0~1. (* 0x21 *)
Definition OP_SHR           : word OpcodeSz := WO~0~0~1~0~0~0~1~0. (* 0x22 *)
Definition OP_MUL           : word OpcodeSz := WO~0~0~1~0~0~0~1~1. (* 0x23 *)
Definition OP_LUI           : word OpcodeSz := WO~0~0~1~0~0~1~0~0. (* 0x24 *)
Definition OP_TENSOR_SET    : word OpcodeSz := WO~0~0~1~0~0~1~0~1. (* 0x25 *)
Definition OP_TENSOR_GET    : word OpcodeSz := WO~0~0~1~0~0~1~1~0. (* 0x26 *)
(** Categorical morphism opcodes (Phase 6 / M3-M4):
    bounded on-chip morph/coupling tables now exist; M4 completes the step
    semantics that actively mutate them. *)
Definition OP_MORPH         : word OpcodeSz := WO~0~0~1~0~0~1~1~1. (* 0x27 *)
Definition OP_COMPOSE       : word OpcodeSz := WO~0~0~1~0~1~0~0~0. (* 0x28 *)
Definition OP_MORPH_ID      : word OpcodeSz := WO~0~0~1~0~1~0~0~1. (* 0x29 *)
Definition OP_MORPH_DELETE  : word OpcodeSz := WO~0~0~1~0~1~0~1~0. (* 0x2A *)
Definition OP_MORPH_ASSERT  : word OpcodeSz := WO~0~0~1~0~1~0~1~1. (* 0x2B cert-setter *)
Definition OP_MORPH_TENSOR  : word OpcodeSz := WO~0~0~1~0~1~1~0~0. (* 0x2C *)
Definition OP_MORPH_GET     : word OpcodeSz := WO~0~0~1~0~1~1~0~1. (* 0x2D *)
Definition OP_HALT          : word OpcodeSz := WO~1~1~1~1~1~1~1~1. (* 0xFF *)

(** ISA v2 instruction transport is 128 bits wide.
    The low 32 bits preserve the legacy bridge encoding:
    [31:24] opcode | [23:16] op_a | [15:8] op_b | [7:0] cost *)

(* INQUISITOR NOTE: connectivity anchor. *)
Definition hardware_dimensions := (RegCount, MemSize, CostSz).
