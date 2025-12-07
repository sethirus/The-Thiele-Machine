# μ-ALU Specification v1.0

## Purpose

This specification defines the bit-exact mathematical operations for μ-bit calculations in the Thiele Machine. All implementations (Python VM, Verilog hardware, and Coq proofs) MUST produce identical results for all μ-ALU operations.

## Numeric Representation: Q16.16 Fixed Point

All μ-calculations use **Q16.16 fixed-point** representation:
- **Total bits**: 32 bits
- **Integer part**: 16 bits (signed, two's complement)
- **Fractional part**: 16 bits (unsigned)
- **Range**: [-32768.0, 32767.99998474121] 
- **Resolution**: 1/65536 ≈ 0.0000152587890625

### Q16.16 Encoding

For a real number `x`:
```
Q16.16(x) = floor(x × 2^16)
```

To decode a Q16.16 value `q`:
```
x = q / 2^16
```

### Examples
- `1.0` → `0x00010000` (65536)
- `0.5` → `0x00008000` (32768)
- `3.14159` → `0x0003243F` (205887)
- `-1.0` → `0xFFFF0000` (-65536)
- `0.0` → `0x00000000` (0)

## Arithmetic Operations

### Addition
```
result = a + b
```
Simple 32-bit signed addition. Overflow behavior: **saturate** at `0x7FFFFFFF` (max) or `0x80000000` (min).

### Subtraction
```
result = a - b
```
Simple 32-bit signed subtraction. Overflow behavior: **saturate** at bounds.

### Multiplication
For Q16.16 × Q16.16 → Q16.16:
```
temp = (int64_t)a × (int64_t)b
result = (temp >> 16) & 0xFFFFFFFF
```
The 64-bit intermediate prevents overflow. The result is shifted right by 16 to maintain Q16.16 format.

### Division
For Q16.16 ÷ Q16.16 → Q16.16:
```
temp = ((int64_t)a << 16) / (int64_t)b
result = temp & 0xFFFFFFFF
```
Shift left before division to maintain precision.

## Logarithm (log₂) Look-Up Table

The hardware log₂ implementation uses a 256-entry look-up table (LUT) for values in the range [1.0, 2.0).

### LUT Specification

**Input range**: Q16.16 values representing [1.0, 2.0)
**Output range**: Q16.16 values representing [0.0, 1.0)

The LUT is indexed by the top 8 bits of the fractional part:
```
index = (x - 0x00010000) >> 8  // Extract bits [15:8] of fractional part
```

### LUT Generation Algorithm

For `i` from 0 to 255:
```python
x = 1.0 + (i / 256.0)
log2_x = log₂(x)
lut[i] = Q16.16(log2_x)
```

### LUT Values (First 16 entries as reference)

```
LUT[0x00] = 0x00000000  // log₂(1.00000000) = 0.00000000
LUT[0x01] = 0x000005C5  // log₂(1.00390625) ≈ 0.00562891
LUT[0x02] = 0x00000B8A  // log₂(1.00781250) ≈ 0.01122742
LUT[0x03] = 0x0000114E  // log₂(1.01171875) ≈ 0.01679688
LUT[0x04] = 0x00001711  // log₂(1.01562500) ≈ 0.02233765
LUT[0x05] = 0x00001CD3  // log₂(1.01953125) ≈ 0.02785015
LUT[0x06] = 0x00002294  // log₂(1.02343750) ≈ 0.03333473
LUT[0x07] = 0x00002854  // log₂(1.02734375) ≈ 0.03879166
LUT[0x08] = 0x00002E13  // log₂(1.03125000) ≈ 0.04422119
LUT[0x09] = 0x000033D1  // log₂(1.03515625) ≈ 0.04962372
LUT[0x0A] = 0x0000398E  // log₂(1.03906250) ≈ 0.05499949
LUT[0x0B] = 0x00003F4A  // log₂(1.04296875) ≈ 0.06034851
LUT[0x0C] = 0x00004504  // log₂(1.04687500) ≈ 0.06567097
LUT[0x0D] = 0x00004ABD  // log₂(1.05078125) ≈ 0.07096708
LUT[0x0E] = 0x00005075  // log₂(1.05468750) ≈ 0.07623672
LUT[0x0F] = 0x0000562C  // log₂(1.05859375) ≈ 0.08148003
```

*Note*: Full 256-entry LUT MUST be generated using the algorithm above to ensure consistency across all implementations.

### log₂ Implementation for Arbitrary Values

For computing `log₂(x)` where `x > 0`:

1. **Extract exponent**: Count leading zeros and normalize to [1.0, 2.0)
```
if x == 0: return -∞ (or saturate to minimum)
exponent = count_leading_zeros(x) - 16  // Adjust for Q16.16
normalized = x << (exponent + 16)       // Shift to [1.0, 2.0)
```

2. **Look up fractional part**:
```
index = (normalized - 0x00010000) >> 8
frac_log = LUT[index]
```

3. **Combine**:
```
result = Q16.16(-exponent) + frac_log
```

### Special Cases
- `log₂(0)` → saturate to `0x80000000` (minimum representable value)
- `log₂(1.0)` → `0x00000000` (exactly 0)
- `log₂(2.0)` → `0x00010000` (exactly 1)
- `log₂(x)` where `x < 0` → undefined (error/assertion)

## Information Gain Calculation

The μ-ALU computes information gain as:
```
info_gain = log₂(before / after)
           = log₂(before) - log₂(after)
```

Using Q16.16 fixed-point:
```
log_before = log2_q16(before)
log_after = log2_q16(after)
info_gain = log_before - log_after
```

### Accumulation

The μ-accumulator is a 32-bit Q16.16 register that accumulates μ-costs:
```
mu_accumulator += mu_cost
```

**Overflow behavior**: Saturate at `0xFFFFFFFF`. When saturation occurs, set an overflow flag but continue execution.

## Conformance Requirements

1. **Bit-exact reproduction**: All implementations MUST produce identical bit patterns for all operations.

2. **LUT consistency**: The log₂ LUT MUST be generated using the specified algorithm. Hardcoded values are acceptable only if they match byte-for-byte.

3. **Test vectors**: Implementations MUST pass all test vectors in `spec/golden/mu_alu_test_vectors.json`.

4. **No hidden precision**: Implementations MUST NOT use higher precision internally and then truncate. All intermediate values MUST be Q16.16.

## Test Vectors

### Addition
```
0x00010000 + 0x00010000 = 0x00020000  // 1.0 + 1.0 = 2.0
0x00008000 + 0x00004000 = 0x0000C000  // 0.5 + 0.25 = 0.75
0x7FFFFFFF + 0x00000001 = 0x7FFFFFFF  // Saturation at max
```

### Subtraction
```
0x00020000 - 0x00010000 = 0x00010000  // 2.0 - 1.0 = 1.0
0x00000000 - 0x00010000 = 0xFFFF0000  // 0.0 - 1.0 = -1.0
```

### Multiplication
```
0x00010000 × 0x00020000 = 0x00020000  // 1.0 × 2.0 = 2.0
0x00008000 × 0x00008000 = 0x00004000  // 0.5 × 0.5 = 0.25
```

### Division
```
0x00020000 ÷ 0x00010000 = 0x00020000  // 2.0 ÷ 1.0 = 2.0
0x00010000 ÷ 0x00020000 = 0x00008000  // 1.0 ÷ 2.0 = 0.5
```

### log₂
```
log₂(0x00010000) = 0x00000000         // log₂(1.0) = 0.0
log₂(0x00020000) = 0x00010000         // log₂(2.0) = 1.0
log₂(0x00040000) = 0x00020000         // log₂(4.0) = 2.0
log₂(0x00018000) = 0x000095C0         // log₂(1.5) ≈ 0.585 (from LUT)
```

*Note*: The exact value for `log₂(1.5)` depends on LUT precision and must be verified across implementations.

## Reference Implementation

The Python reference implementation SHALL be located at:
```
thielecpu/mu_fixed.py
```

This implementation SHALL serve as the canonical behavior specification for edge cases not explicitly covered in this document.

## Version History

- **v1.0** (2025-12-03): Initial specification for Phase 1 implementation
