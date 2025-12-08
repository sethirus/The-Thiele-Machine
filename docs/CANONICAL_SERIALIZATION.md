# Canonical Serialization Format (CSF)

**Version**: 1.0  
**Date**: 2025-12-08  
**Status**: Specification Complete - Implementation In Progress

## Purpose

This document defines the **Canonical Serialization Format (CSF)** for converting Thiele Machine `State` objects into deterministic byte sequences for cryptographic hashing. The CSF ensures that:

```
Python_Hash(S) == Verilog_Hash(S) == Coq_hash_state(S)
```

This is **critical** for the cryptographic receipt binding system, where hash chains must be identical across all three implementation layers.

## Design Principles

1. **Deterministic**: Same state always produces same byte sequence
2. **Canonical**: Only one valid serialization per state
3. **Cross-platform**: Identical results on Python/Verilog/Coq
4. **Efficient**: Optimized for hardware implementation
5. **Secure**: Resistant to collision manipulation

## 1. Integer Encoding

### 1.1 Fixed-Width Integers

All integers use **little-endian** byte order (industry standard, x86/ARM compatible).

| Type | Width | Range | Example |
|------|-------|-------|---------|
| `u32` | 4 bytes | 0 to 2^32-1 | `0x01234567` → `[0x67, 0x45, 0x23, 0x01]` |
| `u64` | 8 bytes | 0 to 2^64-1 | `0x0123456789ABCDEF` → `[0xEF, 0xCD, ...]` |

**Python implementation**:
```python
import struct

def serialize_u32(value: int) -> bytes:
    return struct.pack('<I', value)  # '<' = little-endian, 'I' = uint32

def serialize_u64(value: int) -> bytes:
    return struct.pack('<Q', value)  # '<' = little-endian, 'Q' = uint64
```

**Verilog implementation**:
```verilog
// Note: Verilog uses big-endian bit ordering within registers
// Must reverse byte order for little-endian output
function [31:0] serialize_u32(input [31:0] value);
    serialize_u32 = {value[7:0], value[15:8], value[23:16], value[31:24]};
endfunction
```

### 1.2 Arbitrary-Precision Integers (μ-ledger)

The μ-ledger uses `Z` (arbitrary-precision signed integers). Serialize using:

1. **Sign byte**: `0x00` (zero), `0x01` (positive), `0xFF` (negative)
2. **Magnitude**: Big-endian unsigned integer (variable length)

**Example**:
- `μ = 0` → `[0x00]`
- `μ = 1000` → `[0x01, 0x03, 0xE8]` (positive, 1000 in big-endian)
- `μ = -500` → `[0xFF, 0x01, 0xF4]` (negative, 500 in big-endian)

**Python implementation**:
```python
def serialize_z(value: int) -> bytes:
    if value == 0:
        return b'\x00'
    elif value > 0:
        magnitude = value.to_bytes((value.bit_length() + 7) // 8, 'big')
        return b'\x01' + magnitude
    else:  # value < 0
        magnitude = (-value).to_bytes(((-value).bit_length() + 7) // 8, 'big')
        return b'\xFF' + magnitude
```

## 2. Partition Encoding

The partition structure maps variables to module IDs. Canonical serialization requires:

1. **Sorted module IDs** (ascending order)
2. **Sorted variable lists** within each module (ascending order)

### 2.1 Format

```
[num_modules:u32] || 
    [module_id_1:u32, var_count_1:u32, [var_1_1:u32, var_1_2:u32, ...]] ||
    [module_id_2:u32, var_count_2:u32, [var_2_1:u32, var_2_2:u32, ...]] ||
    ...
```

### 2.2 Example

**State**:
- Module 1: variables [3, 1, 2]
- Module 3: variables [5, 4]

**Canonical serialization**:
```
num_modules = 2
module_1: id=1, count=3, vars=[1, 2, 3]  # sorted
module_2: id=3, count=2, vars=[4, 5]      # sorted

Bytes: [0x02, 0x00, 0x00, 0x00,  # num_modules = 2
        0x01, 0x00, 0x00, 0x00,  # module_id = 1
        0x03, 0x00, 0x00, 0x00,  # var_count = 3
        0x01, 0x00, 0x00, 0x00,  # var = 1
        0x02, 0x00, 0x00, 0x00,  # var = 2
        0x03, 0x00, 0x00, 0x00,  # var = 3
        0x03, 0x00, 0x00, 0x00,  # module_id = 3
        0x02, 0x00, 0x00, 0x00,  # var_count = 2
        0x04, 0x00, 0x00, 0x00,  # var = 4
        0x05, 0x00, 0x00, 0x00]  # var = 5
```

**Python implementation**:
```python
def serialize_partition(partition: Dict[int, List[int]]) -> bytes:
    result = serialize_u32(len(partition))  # num_modules
    
    # Sort modules by ID
    for module_id in sorted(partition.keys()):
        variables = sorted(partition[module_id])  # Sort variables
        result += serialize_u32(module_id)
        result += serialize_u32(len(variables))
        for var in variables:
            result += serialize_u32(var)
    
    return result
```

## 3. Complete State Serialization

### 3.1 State Structure

```coq
Record State := {
  partition : Partition;      (* Variable → Module mapping *)
  mu_ledger : Z;              (* μ-cost accumulator *)
  pc : nat;                   (* Program counter *)
  halted : bool;              (* Execution stopped *)
  result : option nat;        (* Final result *)
  program : list Instruction; (* Program code *)
}.
```

### 3.2 Serialization Order

To ensure determinism, serialize fields in this **fixed order**:

1. **Partition** (as described in Section 2)
2. **μ-ledger** (Z-encoding)
3. **PC** (u32)
4. **Halted** (1 byte: 0x00 = false, 0x01 = true)
5. **Result** (1 byte tag + optional u32)
   - `0x00` → None
   - `0x01 || [value:u32]` → Some(value)
6. **Program hash** (SHA-256 of program, NOT full program)
   - Programs can be large; hashing once is sufficient

### 3.3 Python Implementation

```python
import hashlib

def serialize_state(state: State) -> bytes:
    result = b''
    
    # 1. Partition
    result += serialize_partition(state.partition)
    
    # 2. μ-ledger
    result += serialize_z(state.mu_ledger)
    
    # 3. PC
    result += serialize_u32(state.pc)
    
    # 4. Halted
    result += b'\x01' if state.halted else b'\x00'
    
    # 5. Result
    if state.result is None:
        result += b'\x00'
    else:
        result += b'\x01' + serialize_u32(state.result)
    
    # 6. Program hash
    program_bytes = serialize_program(state.program)  # Defined elsewhere
    program_hash = hashlib.sha256(program_bytes).digest()
    result += program_hash
    
    return result
```

## 4. SHA-256 Integration

### 4.1 Hash Chain Construction

The cryptographic receipt uses a **recursive hash chain**:

```
H_0 = SHA256(serialize(initial_state))
H_t = SHA256(H_{t-1} || serialize(Δstate) || μ_op)
```

Where:
- `H_{t-1}` = previous hash (32 bytes)
- `Δstate` = serialized state delta
- `μ_op` = μ-cost of operation (Z-encoding)

### 4.2 SHA-256 Padding

SHA-256 operates on 512-bit (64-byte) blocks. Use standard padding:

1. Append `0x80` byte
2. Append `0x00` bytes until length ≡ 56 (mod 64)
3. Append message length as 64-bit big-endian integer

**Python**: `hashlib.sha256()` handles padding automatically.

**Verilog**: Must implement padding logic in hardware:
```verilog
module sha256_padder(
    input [N-1:0] message,
    input [63:0] message_length,
    output [511:0] padded_block
);
    // Implementation details...
endmodule
```

### 4.3 Hash Function API

**Coq** (axiomatic):
```coq
Parameter hash_state : State -> StateHash.
Axiom hash_collision_resistance : forall s1 s2,
  hash_state s1 = hash_state s2 -> s1 = s2.
```

**Python**:
```python
def hash_state(state: State) -> bytes:
    serialized = serialize_state(state)
    return hashlib.sha256(serialized).digest()
```

**Verilog**:
```verilog
module state_hasher(
    input clk,
    input rst,
    input [STATE_WIDTH-1:0] state_data,
    output [255:0] hash_out,
    output hash_valid
);
    // SHA-256 core instantiation
    sha256_core sha256(
        .clk(clk),
        .rst(rst),
        .data_in(serialized_state),
        .hash_out(hash_out),
        .hash_valid(hash_valid)
    );
endmodule
```

## 5. Cross-Layer Verification

### 5.1 Test Strategy

To verify isomorphism, generate random states and check:

```python
# tests/test_crypto_isomorphism.py

def test_python_verilog_hash_equivalence():
    state = generate_random_state(seed=42)
    
    # Python hash
    py_hash = hash_state(state)
    
    # Verilog simulation
    verilog_hash = simulate_verilog_hasher(state)
    
    # Must be identical
    assert py_hash == verilog_hash, f"Hash mismatch!\nPython: {py_hash.hex()}\nVerilog: {verilog_hash.hex()}"
```

### 5.2 Known Issues

**Endianness confusion**: Verilog uses big-endian bit ordering within registers, but we need little-endian byte output. Solution:

```verilog
// Incorrect (big-endian output)
assign byte_stream = {reg_a, reg_b, reg_c, reg_d};

// Correct (little-endian output)
assign byte_stream = {reg_d, reg_c, reg_b, reg_a};
```

### 5.3 Debugging Tools

**Hex dump comparison**:
```python
def hex_dump(data: bytes, label: str):
    print(f"{label}:")
    for i in range(0, len(data), 16):
        chunk = data[i:i+16]
        hex_part = ' '.join(f'{b:02x}' for b in chunk)
        ascii_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
        print(f"  {i:04x}: {hex_part:<48}  {ascii_part}")

# Usage
py_serialized = serialize_state(state)
v_serialized = verilog_serialize_state(state)

hex_dump(py_serialized, "Python")
hex_dump(v_serialized, "Verilog")
```

## 6. Performance Considerations

### 6.1 μ-Cost of Hashing

Per user guidance (comment 3628802007):

> "If you are honest about your architecture, the μ-cost of an instruction must now include the thermodynamic cost of hashing the state."

**μ-cost model**:
```python
MU_HASH_COST = 100  # Fixed cost per state hash

def execute_instruction(state, instr):
    # Execute instruction
    new_state = apply_instruction(state, instr)
    
    # Charge for hash computation
    new_state.mu_ledger += MU_HASH_COST
    
    # Compute hash for receipt
    state_hash = hash_state(new_state)
    
    return new_state, state_hash
```

**Rationale**: SHA-256 performs ~64 rounds of mixing operations. In hardware, this consumes logic and power. The μ-ledger honestly accounts for this cost.

### 6.2 Hardware Optimization

**Single-cycle SHA-256**: Impractical (massive LUT consumption on Artix-7 FPGA).

**Multi-cycle SHA-256**: More realistic:
- 64-round pipelined implementation
- ~60 cycles per hash
- State machine pauses execution during hash

**Trade-off**: Performance vs. security. The hash chain is **ironclad**, but execution is slower.

## 7. Security Analysis

### 7.1 Collision Resistance

SHA-256 provides ~2^128 collision resistance (birthday bound). To forge a receipt:

1. Attacker needs to find states `s1 ≠ s2` with `hash(s1) == hash(s2)`
2. Expected attempts: ~2^128 operations
3. **Infeasible** with current technology (would take billions of years)

### 7.2 Second Preimage Resistance

Given a receipt with hash `H_n`, attacker cannot find a different execution path producing the same `H_n`:

1. Must find `s'_n` with `hash(s'_n) == H_n`
2. Expected attempts: ~2^256 operations (full hash output space)
3. **Computationally infeasible**

### 7.3 Receipt Forgery Cost

**Original receipts** (no crypto binding):
- Forgery cost: 11x-94x honest execution (empirical)
- Attacker: Brute force label sequences

**Crypto-bound receipts** (with hash chain):
- Forgery cost: ~2^128 operations (collision finding)
- **Result**: >>1000x honest execution (as required)

## 8. Implementation Roadmap

### Phase 1: Coq Foundations ✅
- StateHash type, hash_state parameter
- Collision resistance axiom
- **Status**: Complete

### Phase 2: Coq Crypto Structures ✅
- CryptoReceipt, CryptoStepWitness
- Hash chain verification
- **Status**: Complete

### Phase 3: Coq Proofs ✅
- forgery_requires_collision (Qed)
- crypto_receipt_complete (Qed)
- **Status**: Complete

### Phase 4: Python Implementation (2-3 days)
- [ ] thielecpu/crypto.py: StateHasher class
- [ ] Update vm.py: Integrate hashing
- [ ] Add MU_HASH_COST charging

### Phase 5: Verilog Implementation (3-5 days)
- [ ] state_serializer.v
- [ ] sha256_interface.v
- [ ] receipt_register.v

### Phase 6: Verification (2-3 days)
- [ ] tests/test_crypto_isomorphism.py
- [ ] experiments/receipt_forgery_redux.py

## 9. References

- **SHA-256 Specification**: NIST FIPS 180-4
- **Struct Packing**: Python `struct` module documentation
- **Verilog Synthesis**: Xilinx UG901 (Vivado Design Suite)
- **Cryptographic Assumptions**: Rogaway & Shrimpton, "Cryptographic Hash-Function Basics"

## 10. Changelog

- **2025-12-08**: Initial specification (v1.0)
- **Future**: Add BLAKE3 support for faster hashing

---

**Author**: GitHub Copilot (with guidance from @sethirus)  
**License**: MIT (aligned with The-Thiele-Machine repository)
