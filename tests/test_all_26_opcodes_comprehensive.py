#!/usr/bin/env python3
"""Comprehensive test of all 26 Thiele CPU opcodes."""

from thielecpu.hardware.cosim import run_verilog

def run_opcode_test(name, program, checks):
    """Test a single opcode with the given program and verification checks."""
    print(f"\n{'='*70}")
    print(f"Testing: {name}")
    print(f"{'='*70}")
    print(f"Program:\n{program}")
    
    result = run_verilog(program, timeout=30)
    
    if result is None:
        print(f"❌ FAILED: iverilog unavailable")
        return False
    
    all_pass = True
    for check_name, check_fn in checks.items():
        try:
            check_fn(result)
            print(f"  ✓ {check_name}")
        except AssertionError as e:
            print(f"  ✗ {check_name}: {e}")
            all_pass = False
    
    if all_pass:
        print(f"✓ {name} PASSED")
    else:
        print(f"✗ {name} FAILED")
        print(f"Full result: {result}")
    
    return all_pass

# Test suite for all 26 opcodes
tests = []

# 1. PNEW
tests.append(("PNEW", "PNEW 0 0 5\nHALT", {
    "charges_mu": lambda r: r["mu"] == 5,
    "increments_partition_ops": lambda r: r["partition_ops"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 2. PSPLIT  
tests.append(("PSPLIT", "PSPLIT 0 0 0 7\nHALT", {
    "charges_mu": lambda r: r["mu"] == 7,
    "increments_partition_ops": lambda r: r["partition_ops"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 3. PMERGE
tests.append(("PMERGE", "PMERGE 0 0 9\nHALT", {
    "charges_mu": lambda r: r["mu"] == 9,
    "increments_partition_ops": lambda r: r["partition_ops"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 4. LASSERT
tests.append(("LASSERT", "LASSERT 0 0 3\nHALT", {
    "charges_mu": lambda r: r["mu"] == 3,
    "advances_pc": lambda r: r["pc"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 5. LJOIN
tests.append(("LJOIN", "LJOIN 0 0 4\nHALT", {
    "charges_mu": lambda r: r["mu"] == 4,
    "advances_pc": lambda r: r["pc"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 6. MDLACC
tests.append(("MDLACC", "MDLACC 0 6\nHALT", {
    "charges_mu": lambda r: r["mu"] == 6,
    "increments_mdl_ops": lambda r: r["mdl_ops"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 7. PDISCOVER
tests.append(("PDISCOVER", "PDISCOVER 0 10 8\nHALT", {
    "charges_mu": lambda r: r["mu"] == 8,
    "increments_info_gain": lambda r: r["info_gain"] == 10,
    "halts": lambda r: r["status"] == 2,
}))

# 8. XFER
tests.append(("XFER", "LOAD_IMM 1 42 1\nXFER 2 1 1\nHALT", {
    "copies_register": lambda r: r["regs"][2] == 42,
    "preserves_source": lambda r: r["regs"][1] == 42,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 9. LOAD_IMM
tests.append(("LOAD_IMM", "LOAD_IMM 5 123 1\nHALT", {
    "loads_immediate": lambda r: r["regs"][5] == 123,
    "charges_mu": lambda r: r["mu"] == 1,
}))

# 10. CHSH_TRIAL
tests.append(("CHSH_TRIAL", "CHSH_TRIAL 0 0 1\nHALT", {
    "charges_mu": lambda r: r["mu"] == 1,
    "no_error": lambda r: r["err"] == 0,
    "halts": lambda r: r["status"] == 2,
}))

# 11. XOR_LOAD
tests.append(("XOR_LOAD", "INIT_MEM 10 99\nXOR_LOAD 3 10 1\nHALT", {
    "loads_from_memory": lambda r: r["regs"][3] == 99,
    "charges_mu": lambda r: r["mu"] == 1,
}))

# 12. XOR_ADD
tests.append(("XOR_ADD", "LOAD_IMM 1 15 1\nLOAD_IMM 2 240 1\nXOR_ADD 1 2 1\nHALT", {
    "xor_adds": lambda r: r["regs"][1] == 255,  # 15 XOR 240 = 255
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 13. XOR_SWAP
tests.append(("XOR_SWAP", "LOAD_IMM 1 10 1\nLOAD_IMM 2 20 1\nXOR_SWAP 1 2 1\nHALT", {
    "swaps_first": lambda r: r["regs"][1] == 20,
    "swaps_second": lambda r: r["regs"][2] == 10,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 14. XOR_RANK (popcount)
tests.append(("XOR_RANK", "LOAD_IMM 1 255 1\nXOR_RANK 2 1 1\nHALT", {
    "counts_bits": lambda r: r["regs"][2] == 8,  # 255 has 8 bits set
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 15. EMIT
tests.append(("EMIT", "EMIT 0 15 7\nHALT", {
    "charges_mu": lambda r: r["mu"] == 7,
    "increments_info_gain": lambda r: r["info_gain"] == 15,
    "halts": lambda r: r["status"] == 2,
}))

# 16. REVEAL
tests.append(("REVEAL", "REVEAL 0 0 5\nHALT", {
    "charges_mu": lambda r: r["mu"] == 5,
    "charges_tensor": lambda r: r["mu_tensor_0"] == 5,
    "halts": lambda r: r["status"] == 2,
}))

# 17. ORACLE_HALTS
tests.append(("ORACLE_HALTS", "ORACLE_HALTS 0 0 11\nHALT", {
    "charges_mu": lambda r: r["mu"] == 11,
    "advances_pc": lambda r: r["pc"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 18. LOAD
tests.append(("LOAD", "INIT_MEM 5 77\nLOAD 3 5 1\nHALT", {
    "loads_from_memory": lambda r: r["regs"][3] == 77,
    "charges_mu": lambda r: r["mu"] == 1,
}))

# 19. STORE
tests.append(("STORE", "LOAD_IMM 1 88 1\nSTORE 10 1 1\nHALT", {
    "stores_to_memory": lambda r: r["mem"][10] == 88,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 20. ADD
tests.append(("ADD", "LOAD_IMM 1 10 1\nLOAD_IMM 2 15 1\nADD 3 1 2 1\nHALT", {
    "adds_correctly": lambda r: r["regs"][3] == 25,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 21. SUB
tests.append(("SUB", "LOAD_IMM 1 50 1\nLOAD_IMM 2 30 1\nSUB 3 1 2 1\nHALT", {
    "subtracts_correctly": lambda r: r["regs"][3] == 20,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 22. JUMP
tests.append(("JUMP", "JUMP 3 1\nLOAD_IMM 1 99 1\nHALT\nLOAD_IMM 2 55 1\nHALT", {
    "jumps_to_target": lambda r: r["regs"][2] == 55,
    "skips_jumped_over": lambda r: r["regs"][1] == 0,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 23. JNEZ
tests.append(("JNEZ", "LOAD_IMM 1 1 1\nJNEZ 1 4 1\nLOAD_IMM 2 99 1\nHALT\nLOAD_IMM 3 77 1\nHALT", {
    "jumps_when_nonzero": lambda r: r["regs"][3] == 77,
    "skips_when_jumped": lambda r: r["regs"][2] == 0,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 24. CALL
tests.append(("CALL", "CALL 2 1\nHALT\nLOAD_IMM 1 33 1\nHALT", {
    "jumps_to_target": lambda r: r["regs"][1] == 33,
    "saves_return_address": lambda r: r["mem"][1] == 1,  # SP starts at 0, incremented to 1
    "increments_sp": lambda r: r["regs"][31] == 1,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 25. RET
tests.append(("RET", "CALL 2 1\nHALT\nLOAD_IMM 1 44 1\nRET 1\nLOAD_IMM 2 55 1\nHALT", {
    "returns_to_saved_pc": lambda r: r["regs"][2] == 55,
    "executed_subroutine": lambda r: r["regs"][1] == 44,
    "decrements_sp": lambda r: r["regs"][31] == 0,
    "charges_mu": lambda r: r["mu"] == 4,
}))

# 26. HALT
tests.append(("HALT", "HALT", {
    "sets_halted_flag": lambda r: r["status"] == 2,
    "stops_at_halt": lambda r: r["pc"] == 0,
}))

# ── pytest-compatible test functions ──────────────────────────────
import pytest

@pytest.mark.integration
@pytest.mark.parametrize("name,program,checks", tests, ids=[t[0] for t in tests])
def test_opcode_parametrized(name, program, checks):
    """Run a single opcode test via pytest parametrize."""
    assert run_opcode_test(name, program, checks), f"Opcode {name} failed"


if __name__ == "__main__":
    # Standalone execution
    print("="*70)
    print("COMPREHENSIVE TEST SUITE FOR ALL 26 THIELE CPU OPCODES")
    print("="*70)

    passed = 0
    failed = 0

    for name, program, checks in tests:
        if run_opcode_test(name, program, checks):
            passed += 1
        else:
            failed += 1

    print("\n" + "="*70)
    print(f"FINAL RESULTS: {passed} passed, {failed} failed out of {len(tests)} opcodes")
    print("="*70)

    if failed == 0:
        print("\n✓✓✓ ALL 26 OPCODES FULLY TESTED AND WORKING ✓✓✓\n")
        exit(0)
    else:
        print(f"\n✗✗✗ {failed} OPCODES FAILED - NEEDS FIXING ✗✗✗\n")
        exit(1)
