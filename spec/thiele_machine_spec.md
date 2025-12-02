# Thiele Machine Canonical Specification v2.0

> **Status:** Normative canonical specification for isomorphism verification.
> This specification defines the exact state representation, instruction set,
> and μ-ledger semantics that MUST be implemented identically across:
> - Python VM (`thielecpu/`)
> - Verilog RTL (`hardware/`)
> - Coq Proofs (`coq/thielemachine/`)

## 1. State Representation

### 1.1 Partition Representation

All implementations MUST use **bitmask-based partitions**:

```
MASK_WIDTH = 64  # Fixed width for hardware compatibility
PartitionMask = uint64  # 0..(1<<MASK_WIDTH)-1
```

A partition is represented as an unsigned 64-bit integer where:
- Bit `i` is set iff element `i` is in the partition
- Empty partition: `0x0000000000000000`
- Full partition: `0xFFFFFFFFFFFFFFFF`

### 1.2 Module Table

```
MAX_MODULES = 8  # Maximum number of active modules
REGION_WIDTH = 64  # Same as MASK_WIDTH

ModuleEntry = {
    id: uint8,           # Unique module identifier
    region: PartitionMask,  # Bitmask of elements in this module
    axioms: list[str],   # Axioms associated with module (optional)
}
```

### 1.3 μ-Ledger

The μ-ledger tracks information-theoretic costs:

```
MuLedger = {
    mu_discovery: uint32,   # Cost of partition discovery operations
    mu_execution: uint32,   # Cost of instruction execution
}

mu_total = mu_discovery + mu_execution
```

**Invariant:** μ-values are monotonically non-decreasing.

### 1.4 Machine State

```
State = {
    pc: uint32,              # Program counter
    modules: ModuleEntry[MAX_MODULES],
    num_modules: uint8,
    mu_ledger: MuLedger,
    csr: {                   # Control/Status Registers
        CERT_ADDR: uint32,
        STATUS: uint32,
        ERR: uint32,
    }
}
```

## 2. Instruction Set Architecture (ISA)

### 2.1 Opcode Encoding

All opcodes are 8-bit values encoded in the first byte of a 32-bit instruction word:

| Mnemonic | Encoding | Description |
|----------|----------|-------------|
| PNEW     | 0x00     | Create new module from region |
| PSPLIT   | 0x01     | Split module using predicate |
| PMERGE   | 0x02     | Merge two modules |
| LASSERT  | 0x03     | Assert logical formula |
| LJOIN    | 0x04     | Join two certificates |
| MDLACC   | 0x05     | Accumulate MDL cost |
| XFER     | 0x07     | Transfer register value |
| PYEXEC   | 0x08     | Execute Python code |
| XOR_LOAD | 0x0A     | Load value with XOR |
| XOR_ADD  | 0x0B     | XOR addition |
| XOR_SWAP | 0x0C     | XOR swap |
| XOR_RANK | 0x0D     | Compute popcount |
| EMIT     | 0x0E     | Emit output value |
| HALT     | 0xFF     | Halt execution |

### 2.2 Instruction Format

```
Instruction Word (32 bits):
  [7:0]   - Opcode
  [15:8]  - Operand A (8 bits)
  [23:16] - Operand B (8 bits)
  [31:24] - Reserved (must be 0)
```

### 2.3 Instruction Semantics

#### PNEW (0x00)
- **Input:** region mask (PartitionMask)
- **Before:** `S = {modules, num_modules, mu_ledger}`
- **After:** `S' = {modules ∪ {new_module}, num_modules + 1, mu_ledger'}`
- **μ-update:** `mu_discovery += popcount(region)`

#### PSPLIT (0x01)
- **Input:** module_id, split_mask
- **Before:** `modules[module_id].region = R`
- **After:** 
  - `modules[module_id].region = R & ~split_mask`
  - `modules[num_modules].region = R & split_mask`
  - `num_modules += 1`
- **μ-update:** `mu_execution += REGION_WIDTH`

#### PMERGE (0x02)
- **Input:** module_id1, module_id2
- **Before:** `modules[m1].region = R1, modules[m2].region = R2`
- **After:** `modules[m1].region = R1 | R2`, `modules[m2].region = 0`
- **μ-update:** `mu_execution += 4`

#### LASSERT (0x03)
- **Input:** config_path
- **Before:** `S`
- **After:** `S'` with updated `csr.CERT_ADDR`
- **μ-update:** Depends on formula complexity

#### MDLACC (0x05)
- **Input:** module_id
- **μ-update:** `mu_execution += mdl_cost(modules[module_id])`

#### EMIT (0x0E)
- **Input:** value or info_bits
- **μ-update:** `mu_execution += info_bits` (if applicable)

#### HALT (0xFF)
- **Effect:** Stop execution
- **μ-update:** None

## 3. Invariants

### 3.1 Partition Invariants

1. **Disjointness:** For all modules i ≠ j:
   `modules[i].region & modules[j].region == 0`

2. **Non-empty:** Active modules have non-zero regions:
   `modules[i].id < num_modules ⟹ modules[i].region ≠ 0`

### 3.2 μ-Ledger Invariants

1. **Monotonicity:** For any state transition `S → S'`:
   `S'.mu_ledger.mu_discovery >= S.mu_ledger.mu_discovery`
   `S'.mu_ledger.mu_execution >= S.mu_ledger.mu_execution`

2. **Finite (non-paradox):** Under normal execution:
   `mu_total < ∞`

3. **Paradox detection:** If contradiction detected:
   `mu_total = ∞`

### 3.3 Hardware Constraints

1. `num_modules <= MAX_MODULES` (8)
2. `MASK_WIDTH = REGION_WIDTH = 64`
3. All masks fit in 64 bits

## 4. Isomorphism Requirements

### 4.1 Python ↔ Verilog

The following MUST be identical:
- Opcode numeric values
- State representation layout
- μ-update rules for each instruction
- Partition invariant enforcement

### 4.2 Python ↔ Coq

The Coq specification MUST:
- Mirror the state type exactly
- Implement the same small-step transition rules
- Prove μ-monotonicity for all instructions

### 4.3 Verification Procedure

1. Run same program on Python VM → `vm_trace.json`
2. Run same program on Verilog → `hw_trace.log`
3. Run same program on Coq → `coq_trace.json`
4. Compare traces step-by-step for equality

## 5. Trace Format

### 5.1 JSON Trace Entry

```json
{
  "step": 0,
  "pc": 0,
  "opcode": "PNEW",
  "operands": {"region": 7},
  "state_before": {
    "num_modules": 0,
    "partition_masks": [],
    "mu": {"mu_discovery": 0, "mu_execution": 0}
  },
  "state_after": {
    "num_modules": 1,
    "partition_masks": [7],
    "mu": {"mu_discovery": 3, "mu_execution": 0}
  }
}
```

## 6. Version History

- v2.0 (2025-12): Canonical specification for isomorphism verification
- v1.0 (2025-10): Archived, see `spec/THIELE-SPEC-v1.0.md`
