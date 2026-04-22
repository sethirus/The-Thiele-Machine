#!/usr/bin/env python3
"""Comprehensive test of all Thiele CPU opcodes via RTL cosim.

Each test provides the necessary init preamble for the RTL:
- INIT_LOGIC_ACC: unlocks high-value ops (CHSH_TRIAL, REVEAL, PDISCOVER)
- INIT_PT + INIT_ACTIVE_MODULE: unlocks locality-guarded ops (LOAD/STORE/CALL/RET/XOR_LOAD/HEAP_*)
- NoFI constraint: PDISCOVER still uses a declared-cost bound; EMIT pays
  op_b payload bits directly as op_b + S(cost)
"""

from __future__ import annotations

from typing import Callable

import pytest

pytestmark = pytest.mark.strict_rtl

from thielecpu.hardware.cosim import run_verilog

# Standard preambles
LOGIC_PREAMBLE = "INIT_LOGIC_ACC -889263410\n"
LOCALITY_PREAMBLE = "INIT_PT 0 256\nINIT_ACTIVE_MODULE 0\n"
FULL_PREAMBLE = LOGIC_PREAMBLE + LOCALITY_PREAMBLE


def run_opcode_test(name: str, program: str, checks: dict[str, Callable[[dict], bool]]) -> dict:
    """Run a single opcode program and assert all checks on the returned state."""
    result = run_verilog(program, timeout=30)
    assert result is not None, (
        f"run_verilog returned None for opcode {name}; backend gating should have skipped this test earlier"
    )

    failures: list[str] = []
    for check_name, check_fn in checks.items():
        try:
            passed = check_fn(result)
        except Exception as exc:
            failures.append(f"{check_name}: raised {exc!r}")
            continue
        if passed is False:
            failures.append(f"{check_name}: returned False")

    assert not failures, (
        f"Opcode {name} failed checks:\n- " + "\n- ".join(failures) + f"\nResult: {result}"
    )
    return result

# Legacy comprehensive RTL smoke suite for the 40 pre-morphism execution cases
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

# 4. LASSERT — UNSAT path (op_a[5]=0 → kind=UNSAT → immediate trap with ERR_LOGIC).
#    The RTL uses bit 5 of op_a as the SAT/UNSAT kind flag.
#    Here op_a=0, so kind=0 (UNSAT), which traps immediately and charges S(cost).
tests.append(("LASSERT", "LASSERT 0 0 0 0 3\nHALT", {
    "charges_mu": lambda r: r["mu"] == 4,  # S(3)=4: cert-setters charge cost+1
    "traps_with_err": lambda r: r["status"] == 3,  # err trap, not halted
    "sets_err_logic": lambda r: r["error_code"] == 0xC43471A1,
}))

# 5. LJOIN
tests.append(("LJOIN", "LJOIN 0 0 4\nHALT", {
    "charges_mu": lambda r: r["mu"] == 5,  # S(4)=5: cert-setters charge cost+1
    "advances_pc": lambda r: r["pc"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 6. MDLACC — charges mdl_ops but does NOT increment the global mu counter
tests.append(("MDLACC", "MDLACC 0 6\nHALT", {
    "increments_mdl_ops": lambda r: r["mdl_ops"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 7. PDISCOVER — needs logic gate + NoFI (cost >= info_gain)
tests.append(("PDISCOVER", LOGIC_PREAMBLE + "PDISCOVER 0 8 8\nHALT", {
    "charges_mu": lambda r: r["mu"] == 8,
    "increments_info_gain": lambda r: r["info_gain"] == 8,
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

# 10. CHSH_TRIAL — needs logic gate
tests.append(("CHSH_TRIAL", LOGIC_PREAMBLE + "CHSH_TRIAL 0 0 1\nHALT", {
    "charges_mu": lambda r: r["mu"] == 1,
    "no_error": lambda r: r["err"] is False,
    "halts": lambda r: r["status"] == 2,
}))

# 11. XOR_LOAD — needs locality
tests.append(("XOR_LOAD", LOCALITY_PREAMBLE + "INIT_MEM 10 99\nXOR_LOAD 3 10 1\nHALT", {
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

# 15. EMIT — op_b is the emitted bit count; cost is the declared delta
tests.append(("EMIT", "EMIT 0 15 15\nHALT", {
    "charges_mu": lambda r: r["mu"] == 31,  # 15 payload bits + S(15)=16
    "increments_info_gain": lambda r: r["info_gain"] == 15,
    "halts": lambda r: r["status"] == 2,
}))

# 16. REVEAL — needs logic gate; op_b is the revealed bit count
tests.append(("REVEAL", LOGIC_PREAMBLE + "REVEAL 0 5 0\nHALT", {
    "charges_mu": lambda r: r["mu"] == 6,  # 5 revealed bits + S(0)=1
    "charges_tensor": lambda r: r["mu_tensor_0"] == 5,
    "halts": lambda r: r["status"] == 2,
}))

# 18. LOAD — register-indirect: LOAD dst rs_addr cost → regs[dst] = mem[regs[rs_addr]]
tests.append(("LOAD", LOCALITY_PREAMBLE + "INIT_MEM 5 77\nLOAD_IMM 5 5 0\nLOAD 3 5 1\nHALT", {
    "loads_from_memory": lambda r: r["regs"][3] == 77,
    "charges_mu": lambda r: r["mu"] == 1,
}))

# 19. STORE — register-indirect: STORE rs_addr src cost → mem[regs[rs_addr]] = regs[src]
tests.append(("STORE", LOCALITY_PREAMBLE + "LOAD_IMM 1 88 1\nLOAD_IMM 10 10 0\nSTORE 10 1 1\nHALT", {
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

# 22. JUMP — target is 16-bit packed into {op_a, op_b}
tests.append(("JUMP", "JUMP 2 1\nLOAD_IMM 1 99 1\nLOAD_IMM 2 55 1\nHALT", {
    "jumps_to_target": lambda r: r["regs"][2] == 55,
    "skips_jumped_over": lambda r: r["regs"][1] == 0,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 23. JNEZ
tests.append(("JNEZ", "LOAD_IMM 1 1 1\nJNEZ 1 3 1\nLOAD_IMM 2 99 1\nLOAD_IMM 3 77 1\nHALT", {
    "jumps_when_nonzero": lambda r: r["regs"][3] == 77,
    "skips_when_jumped": lambda r: r["regs"][2] == 0,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 24. CALL — needs locality for stack writes
tests.append(("CALL", LOCALITY_PREAMBLE + "CALL 2 1\nHALT\nLOAD_IMM 1 33 1\nHALT", {
    "jumps_to_target": lambda r: r["regs"][1] == 33,
    "charges_mu": lambda r: r["mu"] == 2,
}))

# 25. RET — needs locality for stack reads
tests.append(("RET", LOCALITY_PREAMBLE + "CALL 3 1\nLOAD_IMM 2 55 1\nHALT\nLOAD_IMM 1 44 1\nRET 1\nHALT", {
    "returns_from_subroutine": lambda r: r["regs"][2] == 55,
    "executed_subroutine": lambda r: r["regs"][1] == 44,
    "charges_mu": lambda r: r["mu"] == 4,
}))

# 26. HALT
tests.append(("HALT", "HALT", {
    "sets_halted_flag": lambda r: r["status"] == 2,
    "stops_at_halt": lambda r: r["pc"] == 0,
}))

# 27. CHECKPOINT — NOP in hardware (advances PC only)
tests.append(("CHECKPOINT", "CHECKPOINT 0 5\nHALT", {
    "advances_pc": lambda r: r["pc"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 28. READ_PORT — hardware always returns 0; op_b is the read bit count
tests.append(("READ_PORT", "READ_PORT 3 1 0\nHALT", {
    "charges_mu": lambda r: r["mu"] == 2,  # 1 read bit + S(0)=1
    "halts": lambda r: r["status"] == 2,
}))

# 29. WRITE_PORT
tests.append(("WRITE_PORT", "LOAD_IMM 1 42 1\nWRITE_PORT 0 1 1\nHALT", {
    "charges_mu": lambda r: r["mu"] == 2,
    "halts": lambda r: r["status"] == 2,
}))

# 30. HEAP_LOAD — register-indirect (identical to LOAD since heap_base=0)
tests.append(("HEAP_LOAD", LOCALITY_PREAMBLE + "INIT_MEM 5 99\nLOAD_IMM 5 5 0\nHEAP_LOAD 3 5 1\nHALT", {
    "reads_heap": lambda r: r["regs"][3] == 99,
    "charges_mu": lambda r: r["mu"] == 1,
    "halts": lambda r: r["status"] == 2,
}))

# 31. HEAP_STORE — register-indirect (identical to STORE since heap_base=0)
tests.append(("HEAP_STORE", LOCALITY_PREAMBLE + "LOAD_IMM 1 77 1\nLOAD_IMM 10 10 0\nHEAP_STORE 10 1 1\nHALT", {
    "writes_heap": lambda r: r["mem"][10] == 77,
    "charges_mu": lambda r: r["mu"] == 2,
    "halts": lambda r: r["status"] == 2,
}))

# 32. CERTIFY — sets certified flag, charges S(cost) = cost + 1 mu (structurally positive)
tests.append(("CERTIFY", "CERTIFY 0 0 5\nHALT", {
    "charges_mu": lambda r: r["mu"] == 6,  # S(5) = 6 per ThieleCPUCore.v CERTIFY handling
    "halts": lambda r: r["status"] == 2,
}))

# 33. AND
tests.append(("AND", "LOAD_IMM 1 255 1\nLOAD_IMM 2 15 1\nAND 3 1 2 1\nHALT", {
    "ands_correctly": lambda r: r["regs"][3] == 15,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 34. OR
tests.append(("OR", "LOAD_IMM 1 240 1\nLOAD_IMM 2 15 1\nOR 3 1 2 1\nHALT", {
    "ors_correctly": lambda r: r["regs"][3] == 255,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 35. SHL
tests.append(("SHL", "LOAD_IMM 1 1 1\nLOAD_IMM 2 4 1\nSHL 3 1 2 1\nHALT", {
    "shifts_left": lambda r: r["regs"][3] == 16,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 36. SHR — 64 >> 2 = 16
tests.append(("SHR", "LOAD_IMM 1 64 1\nLOAD_IMM 2 2 1\nSHR 3 1 2 1\nHALT", {
    "shifts_right": lambda r: r["regs"][3] == 16,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 37. MUL
tests.append(("MUL", "LOAD_IMM 1 7 1\nLOAD_IMM 2 6 1\nMUL 3 1 2 1\nHALT", {
    "multiplies_correctly": lambda r: r["regs"][3] == 42,
    "charges_mu": lambda r: r["mu"] == 3,
}))

# 38. LUI — load upper immediate: regs[dst] = imm << 8
tests.append(("LUI", "LUI 1 1 1\nHALT", {
    "loads_upper_immediate": lambda r: r["regs"][1] == (1 << 8),
    "charges_mu": lambda r: r["mu"] == 1,
}))

# 39. TENSOR_SET — writes regs[src] to mu_tensor[tensor_idx]
# tensor_idx = op_a[3:0], src_val = regs[op_b[4:0]]
# Use LOAD_IMM to put a value in regs[1], then TENSOR_SET to write it to tensor slot 0
tests.append(("TENSOR_SET", "LOAD_IMM 1 42 1\nTENSOR_SET 0 1 1\nHALT", {
    "writes_tensor": lambda r: r["mu_tensor_0"] == 42,
    "charges_mu": lambda r: r["mu"] == 2,
    "halts": lambda r: r["status"] == 2,
}))

# 40. TENSOR_GET — reads mu_tensor[tensor_idx] into regs[dst]
# Both tensor_idx (op_a[3:0]) and dst_idx (op_a[4:0]) come from op_a,
# so tensor slot N maps to reg N.
# Strategy: accumulate mu via LOAD_IMM instructions, then TENSOR_SET to store a value,
# then TENSOR_GET to read it back.  Avoids INIT_MU force/release timing issue.
tests.append(("TENSOR_GET", "LOAD_IMM 2 42 50\nTENSOR_SET 3 2 50\nTENSOR_GET 3 0 1\nHALT", {
    "reads_tensor": lambda r: r["regs"][3] == 42,
    "charges_mu": lambda r: r["mu"] == 101,  # 50 + 50 + 1
    "halts": lambda r: r["status"] == 2,
}))

# 41. MORPH — categorical morphism creation; SimulationProof.vm_apply requires
#     source/target modules to exist. Without modules, → error path (err=true).
tests.append(("MORPH", "MORPH 1 0 1 0 1\nHALT 0", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_modules": lambda r: r["err"] is True,
}))

# 42. COMPOSE — categorical composition; no morphisms → ERR_MORPH_NOT_FOUND
tests.append(("COMPOSE", LOGIC_PREAMBLE + "COMPOSE 1 0 1\nHALT", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_morphisms": lambda r: r["err"] is True,
}))

# 43. MORPH_ID — identity morphism; no modules → ERR_MORPH_NOT_FOUND
tests.append(("MORPH_ID", LOGIC_PREAMBLE + "MORPH_ID 1 0 1\nHALT", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_modules": lambda r: r["err"] is True,
}))

# 44. MORPH_DELETE — deletes morphism; no morphisms → ERR_MORPH_NOT_FOUND
tests.append(("MORPH_DELETE", LOGIC_PREAMBLE + "MORPH_DELETE 0 0 1\nHALT", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_morphisms": lambda r: r["err"] is True,
}))

# 45. MORPH_ASSERT — cert-setter op; no morphisms → ERR_MORPH_NOT_FOUND
tests.append(("MORPH_ASSERT", LOGIC_PREAMBLE + "MORPH_ASSERT 0 0 3\nHALT", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_morphisms": lambda r: r["err"] is True,
}))

# 46. MORPH_TENSOR — tensor product of morphisms; no morphisms → error path
tests.append(("MORPH_TENSOR", "MORPH_TENSOR 1 0 1 1\nHALT 0", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_morphisms": lambda r: r["err"] is True,
}))

# 47. MORPH_GET — get morphism property; no morphisms → error path
tests.append(("MORPH_GET", "MORPH_GET 1 0 0 1\nHALT 0", {
    "charges_mu": lambda r: r["mu"] >= 1,
    "err_on_missing_morphisms": lambda r: r["err"] is True,
}))

@pytest.mark.integration
@pytest.mark.strict_rtl
@pytest.mark.parametrize("name,program,checks", tests, ids=[t[0] for t in tests])
def test_opcode_parametrized(name, program, checks):
    """Run a single opcode test via pytest parametrize."""
    run_opcode_test(name, program, checks)
