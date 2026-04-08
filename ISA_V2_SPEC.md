# ISA v2 Specification

Binding freeze for the ISA v2 transport and rich-payload contract.

Status:
- This document freezes the ISA v2 instruction shape and bounded rich-state model.
- Opcode byte assignments remain the canonical values already defined in [coq/kami_hw/ThieleTypes.v](/workspaces/The-Thiele-Machine/coq/kami_hw/ThieleTypes.v).
- Current assembler / RTL transport is still `32-bit`; this spec is the contract M1+ must implement.

## 1. Instruction Word

Every ISA v2 instruction is exactly `128` bits wide.

| Bits | Name | Width | Meaning |
|------|------|-------|---------|
| `127:120` | `isa_version` | `8` | Must equal `0x02` |
| `119:112` | `format_id` | `8` | Upper-lane interpretation class |
| `111:96` | `flags` | `16` | Format subtype / descriptor kind / inline length |
| `95:64` | `ext1` | `32` | Extended payload lane 1 |
| `63:32` | `ext0` | `32` | Extended payload lane 0 |
| `31:24` | `opcode` | `8` | Legacy opcode byte |
| `23:16` | `op_a` | `8` | Legacy operand A |
| `15:8` | `op_b` | `8` | Legacy operand B |
| `7:0` | `cost` | `8` | Legacy cost lane |

Low-lane compatibility rule:
- The low `32` bits preserve the current legacy bridge encoding exactly.
- Legacy instructions must continue to decode their existing low-lane semantics unchanged.

Version rule:
- `isa_version != 0x02` is an instruction-format fault.

## 2. Format IDs

These numeric `format_id` values are fixed:

| Value | Name | Meaning |
|------|------|---------|
| `0x00` | `FMT_LEGACY` | Upper lanes ignored; low `32` bits fully define semantics |
| `0x01` | `FMT_BRANCH_EXT` | `ext0/ext1` extend branch / call / jump targets or immediates |
| `0x02` | `FMT_TENSOR_EXT` | `ext0/ext1` carry extended tensor / module / index payload |
| `0x03` | `FMT_MORPH_INLINE` | `ext0/ext1` carry inline morph / coupling payload |
| `0x04` | `FMT_DESC` | `ext0/ext1` carry descriptor references into bounded hardware tables |
| `0x05` | `FMT_CERT_INLINE` | `ext0/ext1` carry short inline certification payload |

All other `format_id` values are reserved and fault.

Current live execution subcases (`2026-04-07`):
- `REVEAL` with `FMT_TENSOR_EXT` reads the tensor flat index from `ext0[3:0]`.
- `MORPH_EXT`, `COMPOSE_EXT`, `MORPH_ID_EXT`, `MORPH_DELETE_EXT`, and `MORPH_GET_EXT` use `FMT_MORPH_INLINE` to carry the missing morph operands and now drive real hardware morph-table mutation / lookup.
- `MORPH_ASSERT_EXT` uses `FMT_CERT_INLINE` with `inline_len = 4`; `ext0[31:0]` is the inline property checksum that the live hardware path commits into the hardware-visible cert-address witness on successful morph validation.
- The low-lane legacy fields still carry the opcode, primary operand, and cost.

## 3. Flag Layout

`flags[15:12]`:
- `subtype`

`flags[11:8]`:
- `desc_kind`

`flags[7:0]`:
- `inline_len`

Interpretation rules:
- `subtype` is opcode-local and may refine meaning within a format class.
- `desc_kind` is used only by `FMT_DESC`.
- `inline_len` is used only by inline formats and gives payload length in bytes.

Reserved rule:
- Any format/opcode combination that does not define one of these flag fields must require it to be zero.

## 4. Bounded Hardware Capacities

These capacities are fixed for ISA v2:

| Resource | Capacity | Index Width |
|------|------|------------|
| Register file | `32` | `5` bits |
| Data memory | `65536` words | `16` bits |
| Instruction memory | `65536` words | `16` bits |
| Module / partition table | `64` slots | `6` bits |
| μ-tensor entries | `16` | `4` bits |
| Morph table | `64` entries | `6` bits |
| Coupling descriptor store | `64` entries | `6` bits |
| Formula descriptor store | `64` entries | `6` bits |
| Certification descriptor store | `64` entries | `6` bits |
| Descriptor metadata table | `64` entries | `6` bits |

Capacity rationale:
- `64` rich-state entries align with the existing `PTableSz = 64` hardware module bound in [ThieleTypes.v](/workspaces/The-Thiele-Machine/coq/kami_hw/ThieleTypes.v).
- Descriptor IDs are therefore architecturally `6` bits even when transported inside `32`-bit `ext` lanes.

## 5. Descriptor Model

Descriptor IDs:
- `0..63` are valid.
- `64+` fault.

`desc_kind` values:

| Value | Meaning |
|------|---------|
| `0x0` | morph descriptor |
| `0x1` | coupling descriptor |
| `0x2` | formula descriptor |
| `0x3` | certification descriptor |
| `0x4` | descriptor metadata record |

`FMT_DESC` lane contract:
- `ext0[5:0]` = primary descriptor id
- `ext0[11:6]` = secondary descriptor id
- `ext0[15:12]` = descriptor count or small subtype-local arity
- `ext0[31:16]` = opcode-local immediate / selector
- `ext1[31:0]` = opcode-local auxiliary payload

Mixed payload policy:
- Morph payloads: mixed
  - `FMT_MORPH_INLINE` for short inline metadata
  - `FMT_DESC` for table-backed morph / coupling references
- Certification payloads: mixed
  - `FMT_CERT_INLINE` for short inline certificate / property metadata
  - `FMT_DESC` for formula / certification descriptors
- Tensor payloads: mixed
  - `FMT_LEGACY` for current low-lane behavior
  - `FMT_TENSOR_EXT` when richer module / index / value payload is required

## 6. Trap / Error Behavior

Architectural rich-state fault rule:
- Set `err := 1`
- Write `error_code := fault_code`
- Set `pc := trap_vector`
- Do not partially mutate descriptor tables, morph table, certification state, or destination register
- Charge the encoded `cost` field unless the opcode already has a stricter existing charge rule

Existing charge-rule exceptions preserved:
- `CERTIFY` keeps its existing `S(cost)` charge rule.
- `LASSERT` keeps its existing verified hardware charge behavior.

New ISA v2 fault classes:

| Fault | Trigger |
|------|---------|
| `ERR_ISA_VERSION` | `isa_version != 0x02` on ISA-v2 decode path |
| `ERR_FORMAT_INVALID` | unknown / reserved `format_id` |
| `ERR_DESC_RANGE` | descriptor id outside `0..63` |
| `ERR_INLINE_MALFORMED` | inline payload length or flag structure invalid |
| `ERR_TABLE_OVERFLOW` | descriptor or morph table allocation past capacity |
| `ERR_MORPH_LOOKUP` | morph id missing |
| `ERR_TENSOR_INDEX` | tensor index outside supported bounds |
| `ERR_CERT_DESC_INVALID` | formula / certification descriptor invalid or type-mismatched |

Mapping requirement for implementation:
- `ERR_MORPH_LOOKUP` must map to current `ERR_MORPH_NOT_FOUND`.
- `ERR_TENSOR_INDEX` must map to current `ERR_TENSOR_INVALID`.
- Coupling / malformed rich-payload failures must map to a dedicated error code or the current `ERR_COUPLING_INVALID` until split further in hardware.

## 7. Opcode Policy

Opcode byte assignments are unchanged from the current `47`-opcode table in
[ThieleTypes.v](/workspaces/The-Thiele-Machine/coq/kami_hw/ThieleTypes.v).

Purely legacy under ISA v2:
- `XFER`
- `LOAD_IMM`
- `LOAD`
- `STORE`
- `ADD`
- `SUB`
- `JUMP`
- `JNEZ`
- `CALL`
- `RET`
- `CHECKPOINT`
- `READ_PORT`
- `WRITE_PORT`
- `HEAP_LOAD`
- `HEAP_STORE`
- `AND`
- `OR`
- `SHL`
- `SHR`
- `MUL`
- `LUI`
- `XOR_LOAD`
- `XOR_ADD`
- `XOR_SWAP`
- `XOR_RANK`
- `ORACLE_HALTS`
- `HALT`

Rich-capable under ISA v2:
- `PNEW`
- `PSPLIT`
- `PMERGE`
- `LASSERT`
- `LJOIN`
- `MDLACC`
- `PDISCOVER`
- `CHSH_TRIAL`
- `EMIT`
- `REVEAL`
- `CERTIFY`
- `TENSOR_SET`
- `TENSOR_GET`
- `MORPH`
- `COMPOSE`
- `MORPH_ID`
- `MORPH_DELETE`
- `MORPH_ASSERT`
- `MORPH_TENSOR`
- `MORPH_GET`

Default format expectations:
- Purely legacy opcodes default to `FMT_LEGACY`.
- `JUMP`, `JNEZ`, and `CALL` may additionally use `FMT_BRANCH_EXT`.
- `TENSOR_SET` and `TENSOR_GET` may additionally use `FMT_TENSOR_EXT`.
- Morph opcodes may use `FMT_MORPH_INLINE` or `FMT_DESC`.
- Assertion / certification opcodes may use `FMT_CERT_INLINE` or `FMT_DESC`.

## 8. Canonical Opcode Bytes

Grouped canonical opcode map:

- `0x00` `PNEW`
- `0x01` `PSPLIT`
- `0x02` `PMERGE`
- `0x03` `LASSERT`
- `0x04` `LJOIN`
- `0x05` `MDLACC`
- `0x06` `PDISCOVER`
- `0x07` `XFER`
- `0x08` `LOAD_IMM`
- `0x09` `CHSH_TRIAL`
- `0x0A` `XOR_LOAD`
- `0x0B` `XOR_ADD`
- `0x0C` `XOR_SWAP`
- `0x0D` `XOR_RANK`
- `0x0E` `EMIT`
- `0x0F` `REVEAL`
- `0x10` `ORACLE_HALTS`
- `0x11` `LOAD`
- `0x12` `STORE`
- `0x13` `ADD`
- `0x14` `SUB`
- `0x15` `JUMP`
- `0x16` `JNEZ`
- `0x17` `CALL`
- `0x18` `RET`
- `0x19` `CHECKPOINT`
- `0x1A` `READ_PORT`
- `0x1B` `WRITE_PORT`
- `0x1C` `HEAP_LOAD`
- `0x1D` `HEAP_STORE`
- `0x1E` `CERTIFY`
- `0x1F` `AND`
- `0x20` `OR`
- `0x21` `SHL`
- `0x22` `SHR`
- `0x23` `MUL`
- `0x24` `LUI`
- `0x25` `TENSOR_SET`
- `0x26` `TENSOR_GET`
- `0x27` `MORPH`
- `0x28` `COMPOSE`
- `0x29` `MORPH_ID`
- `0x2A` `MORPH_DELETE`
- `0x2B` `MORPH_ASSERT`
- `0x2C` `MORPH_TENSOR`
- `0x2D` `MORPH_GET`
- `0xFF` `HALT`

## 9. Implementation Targets

M1 must make all of the following true:
- `InstrSz = 128`
- assembler emits `16` bytes / `32` hex chars per instruction
- Kami `imem` stores `128`-bit words
- testbench instruction memory stores `128`-bit words
- decode continues reading legacy fields from low bits while formats are introduced

Until M1 lands, this document is the binding contract and the playbook remains the execution tracker.
