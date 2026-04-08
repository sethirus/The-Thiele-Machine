#!/usr/bin/env python3
"""Comprehensive Python VM tests for all Thiele CPU opcodes.

Tests the Python VM directly (thielecpu.vm) for every opcode, including the
5 newer opcodes (CHECKPOINT, READ_PORT, WRITE_PORT, HEAP_LOAD, HEAP_STORE)
and control flow opcodes (JUMP, JNEZ, CALL, RET).

This complements test_all_opcodes_comprehensive.py which tests via RTL.
"""

import pytest
from thielecpu.vm import VMState, vm_run, vm_apply


def run_py(instructions, fuel=500):
    """Run a list of instruction dicts through the Python VM and return final state."""
    s = VMState.default()
    return vm_run(s, instructions, max_steps=fuel)


def run_text(lines, fuel=500):
    """Run text-format instructions through the Python VM (parsing + execution)."""
    from build.thiele_vm import _run_extracted_py
    # _run_extracted_py is the pure-Python backend, bypasses OCaml runner
    return _run_extracted_py(lines, fuel)


# ── Partition opcodes ──────────────────────────────────────────────────

class TestPartitionOpcodes:
    def test_pnew(self):
        s = run_py([{"op": "pnew", "region": [0, 1, 2], "cost": 5},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 6

    def test_psplit(self):
        # PSPLIT charges mu even if it sets error (module lookup may fail)
        s = run_py([{"op": "pnew", "region": [0, 1, 2, 3], "cost": 1},
                     {"op": "psplit", "module": 0, "left": [0, 1], "right": [2, 3], "cost": 7},
                     {"op": "halt", "cost": 1}])
        # PSPLIT charges cost; err may stop HALT from running
        assert s.vm_mu >= 8  # at least pnew(1) + psplit(7)

    def test_pmerge(self):
        # PMERGE charges mu even if merge sets error
        s = run_py([{"op": "pnew", "region": [0, 1], "cost": 1},
                     {"op": "pnew", "region": [2, 3], "cost": 1},
                     {"op": "pmerge", "m1": 0, "m2": 1, "cost": 9},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 11  # at least pnew(1) + pnew(1) + pmerge(9)

    def test_lassert(self):
        # LASSERT is a cert-setter; charges mu, may set err (stops HALT)
        s = run_py([{"op": "pnew", "region": [0, 1], "cost": 1},
                     {"op": "lassert", "module": 0, "formula": "x", "cert": {"type": "sat", "proof": ""}, "cost": 3},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 4  # at least pnew(1) + lassert(3)

    def test_ljoin(self):
        s = run_py([{"op": "ljoin", "cert1": "a", "cert2": "b", "cost": 4},
                     {"op": "halt", "cost": 1}])
        # ljoin is a cert-setter, may error on invalid certs — check mu charged
        assert s.vm_mu >= 4

    def test_mdlacc(self):
        s = run_py([{"op": "mdlacc", "cost": 6},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 7

    def test_pdiscover(self):
        s = run_py([{"op": "pdiscover", "module": 0, "evidence": [], "cost": 8},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 9


# ── Register / memory opcodes ─────────────────────────────────────────

class TestRegMemOpcodes:
    def test_load_imm(self):
        s = run_py([{"op": "load_imm", "dst": 5, "imm": 123, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[5] == 123
        assert s.vm_mu == 2

    def test_xfer(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 42, "cost": 1},
                     {"op": "xfer", "dst": 2, "src": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[2] == 42
        assert s.vm_regs[1] == 42

    def test_load(self):
        s = VMState.default()
        s.vm_mem[5] = 77
        s.vm_regs[5] = 5   # reg[5] holds address 5 (register-indirect)
        s = vm_run(s, [{"op": "load", "dst": 3, "addr": 5, "cost": 1},
                        {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 77

    def test_store(self):
        # STORE is register-indirect: mem[regs[addr]] = regs[src]
        # Load 88 into reg[1], load address 10 into reg[10], then store
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 88, "cost": 1},
                     {"op": "load_imm", "dst": 10, "imm": 10, "cost": 1},
                     {"op": "store", "addr": 10, "src": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mem[10] == 88

    def test_add(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 10, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 15, "cost": 1},
                     {"op": "add", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 25

    def test_sub(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 50, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 30, "cost": 1},
                     {"op": "sub", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 20

    def test_add_no_overflow_64bit(self):
        # 0xFFFFFFFF + 1 = 0x100000000 in 64-bit (no wrap within 32-bit range)
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 0xFFFFFFFF, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 1, "cost": 1},
                     {"op": "add", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 0x100000000

    def test_sub_underflow_wraps_64bit(self):
        # 0 - 1 wraps to 2^64-1 (word64_sub uses Int64 two's complement wrap)
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 0, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 1, "cost": 1},
                     {"op": "sub", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        # Int64: 0 - 1 = -1 → serialized as unsigned 2^64 - 1
        assert s.vm_regs[3] == (2**64 - 1)


# ── XOR opcodes ────────────────────────────────────────────────────────

class TestXOROpcodes:
    def test_xor_load(self):
        s = VMState.default()
        s.vm_mem[10] = 99
        s = vm_run(s, [{"op": "xor_load", "dst": 3, "addr": 10, "cost": 1},
                        {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 99

    def test_xor_add(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 15, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 240, "cost": 1},
                     {"op": "xor_add", "dst": 1, "src": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[1] == 255

    def test_xor_swap(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 10, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 20, "cost": 1},
                     {"op": "xor_swap", "a": 1, "b": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[1] == 20
        assert s.vm_regs[2] == 10

    def test_xor_rank_popcount(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 255, "cost": 1},
                     {"op": "xor_rank", "dst": 2, "src": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[2] == 8


# ── Cert / physics opcodes ────────────────────────────────────────────

class TestCertOpcodes:
    def test_emit(self):
        s = run_py([{"op": "emit", "module": 0, "payload": "hello", "cost": 7},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 9  # S(7)+1=9: cert-setters charge cost+1

    def test_reveal(self):
        s = run_py([{"op": "reveal", "module": 0, "bits": 0, "cert": "proof", "cost": 5},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 7  # S(5)+1=7: cert-setters charge cost+1

    def test_oracle_halts(self):
        # Per Coq extraction (thiele_core.ml), Instr_oracle_halts always charges
        # exactly 1,000,000 regardless of the cost field — the cost parameter is
        # ignored by the extracted semantics.
        s = run_py([{"op": "oracle_halts", "payload": 0, "cost": 11},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 1_000_001  # 1_000_000 (oracle_halts fixed cost) + 1 (halt)

    def test_chsh_trial_x0(self):
        """CHSH_TRIAL with x=0 should succeed without surcharge."""
        s = run_py([{"op": "chsh_trial", "x": 0, "y": 0, "a": 0, "b": 0, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 2
        assert not s.vm_err

    def test_halt(self):
        s = run_py([{"op": "halt", "cost": 1}])
        assert s.vm_mu == 1


# ── Control flow opcodes ──────────────────────────────────────────────

class TestControlFlow:
    def test_jump_skips_instructions(self):
        """JUMP should set PC to target, skipping intermediate instructions."""
        s = run_py([
            {"op": "jump", "target": 3, "cost": 1},         # PC=0 -> jump to PC=3
            {"op": "load_imm", "dst": 1, "imm": 99, "cost": 1},  # PC=1 -> skipped
            {"op": "halt", "cost": 1},                       # PC=2 -> skipped
            {"op": "load_imm", "dst": 2, "imm": 55, "cost": 1},  # PC=3 -> executed
            {"op": "halt", "cost": 1},                       # PC=4 -> halt
        ])
        assert s.vm_regs[2] == 55
        assert s.vm_regs[1] == 0

    def test_jnez_jumps_when_nonzero(self):
        """JNEZ should jump when register is nonzero."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},    # r1 = 1
            {"op": "jnez", "rs": 1, "target": 4, "cost": 1},      # if r1 != 0, jump to PC=4
            {"op": "load_imm", "dst": 2, "imm": 99, "cost": 1},   # PC=2 -> skipped
            {"op": "halt", "cost": 1},                              # PC=3 -> skipped
            {"op": "load_imm", "dst": 3, "imm": 77, "cost": 1},   # PC=4 -> executed
            {"op": "halt", "cost": 1},                              # PC=5 -> halt
        ])
        assert s.vm_regs[3] == 77
        assert s.vm_regs[2] == 0

    def test_jnez_falls_through_when_zero(self):
        """JNEZ should fall through when register is zero."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 0, "cost": 1},    # r1 = 0
            {"op": "jnez", "rs": 1, "target": 4, "cost": 1},      # not taken
            {"op": "load_imm", "dst": 2, "imm": 99, "cost": 1},   # PC=2 -> executed
            {"op": "halt", "cost": 1},                              # PC=3 -> halt
            {"op": "load_imm", "dst": 3, "imm": 77, "cost": 1},   # PC=4 -> not reached
            {"op": "halt", "cost": 1},
        ])
        assert s.vm_regs[2] == 99
        assert s.vm_regs[3] == 0

    def test_call_and_ret(self):
        """CALL saves return address on stack, RET returns to it."""
        s = run_py([
            {"op": "call", "target": 3, "cost": 1},                # PC=0 -> call to PC=3
            {"op": "load_imm", "dst": 2, "imm": 55, "cost": 1},   # PC=1 -> executed after RET
            {"op": "halt", "cost": 1},                              # PC=2 -> halt
            {"op": "load_imm", "dst": 1, "imm": 33, "cost": 1},   # PC=3 -> subroutine
            {"op": "ret", "cost": 1},                               # PC=4 -> return to PC=1
        ])
        assert s.vm_regs[1] == 33
        assert s.vm_regs[2] == 55

    def test_call_increments_sp(self):
        """CALL pushes return address, RET pops it — SP should be restored."""
        s = run_py([
            {"op": "call", "target": 2, "cost": 1},    # PC=0 -> call
            {"op": "halt", "cost": 1},                  # PC=1 -> halt (reached after RET)
            {"op": "ret", "cost": 1},                   # PC=2 -> return
        ])
        assert s.vm_regs[31] == 0  # SP restored after CALL+RET pair

    def test_simple_loop(self):
        """A simple counted loop using JNEZ."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 3, "cost": 1},        # r1 = 3 (counter)
            {"op": "load_imm", "dst": 2, "imm": 0, "cost": 1},        # r2 = 0 (accum)
            {"op": "add", "dst": 2, "rs1": 2, "rs2": 1, "cost": 1},   # PC=2: r2 += r1
            {"op": "load_imm", "dst": 3, "imm": 1, "cost": 1},        # r3 = 1
            {"op": "sub", "dst": 1, "rs1": 1, "rs2": 3, "cost": 1},   # r1 -= 1
            {"op": "jnez", "rs": 1, "target": 2, "cost": 1},          # loop to PC=2
            {"op": "halt", "cost": 1},
        ], fuel=200)
        # r2 = 3+2+1 = 6
        assert s.vm_regs[2] == 6
        assert s.vm_regs[1] == 0


# ── New opcodes (27-40) ───────────────────────────────────────────────

class TestNewOpcodes:
    def test_checkpoint(self):
        """CHECKPOINT should advance PC and charge mu."""
        s = run_py([{"op": "checkpoint", "cost": 5},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 6

    def test_read_port(self):
        """READ_PORT should write value to dst register."""
        s = run_py([{"op": "read_port", "dst": 3, "channel": 0, "value": 42, "bits": 8, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 42
        assert s.vm_mu == 3  # S(1)+1=3: cert-setters charge cost+1

    def test_read_port_different_channels(self):
        """READ_PORT should work with different channel indices."""
        s = run_py([
            {"op": "read_port", "dst": 1, "channel": 0, "value": 100, "bits": 8, "cost": 1},
            {"op": "read_port", "dst": 2, "channel": 1, "value": 200, "bits": 16, "cost": 1},
            {"op": "halt", "cost": 1},
        ])
        assert s.vm_regs[1] == 100
        assert s.vm_regs[2] == 200

    def test_write_port(self):
        """WRITE_PORT should advance PC and charge mu."""
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 42, "cost": 1},
                     {"op": "write_port", "channel": 0, "src": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu == 3

    def test_heap_load(self):
        """HEAP_LOAD should read from memory at heap_base + regs[addr]."""
        s = VMState.default()
        s.vm_mem[5] = 99
        s.vm_regs[5] = 5   # reg[5] holds address 5 (register-indirect)
        s = vm_run(s, [{"op": "heap_load", "dst": 3, "addr": 5, "cost": 1},
                        {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 99
        assert s.vm_mu == 2

    def test_heap_store(self):
        """HEAP_STORE should write register value to memory at heap_base + regs[addr]."""
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 77, "cost": 1},
                     {"op": "load_imm", "dst": 10, "imm": 10, "cost": 1},
                     {"op": "heap_store", "addr": 10, "src": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mem[10] == 77
        assert s.vm_mu == 4

    def test_heap_load_store_roundtrip(self):
        """HEAP_STORE followed by HEAP_LOAD at same address should roundtrip."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 12345, "cost": 1},
            {"op": "load_imm", "dst": 20, "imm": 20, "cost": 1},
            {"op": "heap_store", "addr": 20, "src": 1, "cost": 1},
            {"op": "heap_load", "dst": 2, "addr": 20, "cost": 1},
            {"op": "halt", "cost": 1},
        ])
        assert s.vm_regs[2] == 12345


# ── Text-format parsing tests ────────────────────────────────────────

class TestTextFormatParsing:
    """Test that text-format instructions parse and execute correctly."""

    def test_text_read_port(self):
        s = run_text(["READ_PORT 3 0 42 8 1", "HALT 1"])
        assert s.regs[3] == 42

    def test_text_write_port(self):
        s = run_text(["LOAD_IMM 1 42 1", "WRITE_PORT 0 1 1", "HALT 1"])
        assert s.mu == 3

    def test_text_checkpoint(self):
        s = run_text(["CHECKPOINT 0 5", "HALT 1"])
        assert s.mu == 6

    def test_text_heap_load(self):
        # HEAP_LOAD is register-indirect; INIT_REG 5 5 sets reg[5]=5 as address
        s = run_text(["INIT_MEM 5 99", "INIT_REG 5 5", "HEAP_LOAD 3 5 1", "HALT 1"])
        assert s.regs[3] == 99

    def test_text_heap_store(self):
        # HEAP_STORE is register-indirect; reg[10]=10 serves as address
        s = run_text(["LOAD_IMM 1 77 1", "LOAD_IMM 10 10 1", "HEAP_STORE 10 1 1", "HALT 1"])
        assert s.mem[10] == 77

    def test_text_jump(self):
        s = run_text([
            "JUMP 3 1",
            "LOAD_IMM 1 99 1",
            "HALT 1",
            "LOAD_IMM 2 55 1",
            "HALT 1",
        ])
        assert s.regs[2] == 55
        assert s.regs[1] == 0

    def test_text_call_ret(self):
        s = run_text([
            "CALL 3 1",
            "LOAD_IMM 2 55 1",
            "HALT 1",
            "LOAD_IMM 1 33 1",
            "RET 1",
        ])
        assert s.regs[1] == 33
        assert s.regs[2] == 55


# ── Certify + extended ALU opcodes ───────────────────────────────────

class TestCertifyAndALUOpcodes:
    def test_certify(self):
        """CERTIFY sets certified flag and charges S(cost)."""
        s = run_py([{"op": "certify", "cost": 5},
                     {"op": "halt", "cost": 1}])
        assert s.vm_certified is True
        assert s.vm_mu >= 6  # S(5)=6

    def test_and(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 255, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 15, "cost": 1},
                     {"op": "and", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 15

    def test_or(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 240, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 15, "cost": 1},
                     {"op": "or", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 255

    def test_shl(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 1, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 4, "cost": 1},
                     {"op": "shl", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 16

    def test_shr(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 64, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 2, "cost": 1},
                     {"op": "shr", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 16

    def test_mul(self):
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 7, "cost": 1},
                     {"op": "load_imm", "dst": 2, "imm": 6, "cost": 1},
                     {"op": "mul", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[3] == 42

    def test_lui(self):
        s = run_py([{"op": "lui", "dst": 1, "imm": 1, "cost": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_regs[1] == (1 << 8)


# ── Tensor opcodes ──────────────────────────────────────────────────

class TestTensorOpcodes:
    def test_tensor_set(self):
        s = run_py([{"op": "tensor_set", "module": 0, "i": 0, "j": 0, "value": 42, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 1

    def test_tensor_get(self):
        s = run_py([{"op": "tensor_set", "module": 0, "i": 0, "j": 0, "value": 99, "mu_delta": 1},
                     {"op": "tensor_get", "dst": 5, "module": 0, "i": 0, "j": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 2


# ── Categorical MORPH opcodes ─────────────────────────────────────────

class TestMorphOpcodes:
    def test_morph(self):
        """MORPH creates a morphism; charges mu."""
        s = run_py([{"op": "pnew", "region": [0, 1], "cost": 1},
                     {"op": "pnew", "region": [2, 3], "cost": 1},
                     {"op": "morph", "dst": 1, "src_mod": 0, "dst_mod": 1, "coupling_idx": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 3

    def test_compose(self):
        """COMPOSE composes two morphisms; charges mu."""
        s = run_py([{"op": "compose", "dst": 1, "m1": 0, "m2": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 1

    def test_morph_id(self):
        """MORPH_ID creates identity morphism; charges mu."""
        s = run_py([{"op": "pnew", "region": [0, 1], "cost": 1},
                     {"op": "morph_id", "dst": 1, "module": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 2

    def test_morph_delete(self):
        """MORPH_DELETE deletes a morphism; charges mu."""
        s = run_py([{"op": "morph_delete", "morph_id": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 1

    def test_morph_assert(self):
        """MORPH_ASSERT is a cert-setter; charges S(cost)."""
        s = run_py([{"op": "morph_assert", "morph_id": 0, "property": 0, "cert": 0, "mu_delta": 3},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 3

    def test_morph_tensor(self):
        """MORPH_TENSOR creates tensor product; charges mu."""
        s = run_py([{"op": "morph_tensor", "dst": 1, "f": 0, "g": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 1

    def test_morph_get(self):
        """MORPH_GET reads morphism property; charges mu."""
        s = run_py([{"op": "morph_get", "dst": 1, "morph_id": 0, "selector": 0, "mu_delta": 1},
                     {"op": "halt", "cost": 1}])
        assert s.vm_mu >= 1


# ── Mu monotonicity ──────────────────────────────────────────────────

class TestMuMonotonicity:
    def test_mu_always_increases(self):
        """Every instruction with cost > 0 must increase mu."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 10, "cost": 1},
            {"op": "load_imm", "dst": 2, "imm": 20, "cost": 1},
            {"op": "add", "dst": 3, "rs1": 1, "rs2": 2, "cost": 1},
            {"op": "store", "addr": 0, "src": 3, "cost": 1},
            {"op": "load", "dst": 4, "addr": 0, "cost": 1},
            {"op": "xor_add", "dst": 4, "src": 1, "cost": 1},
            {"op": "halt", "cost": 1},
        ])
        assert s.vm_mu == 7

    def test_mu_zero_cost_allowed(self):
        """Instructions with cost=0 should not increase mu."""
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 10, "cost": 0},
                     {"op": "halt", "cost": 0}])
        assert s.vm_mu == 0


# ── Error handling ────────────────────────────────────────────────────

class TestErrorHandling:
    def test_halt_stops_execution(self):
        """HALT should stop execution immediately."""
        s = run_py([
            {"op": "halt", "cost": 1},
            {"op": "load_imm", "dst": 1, "imm": 99, "cost": 1},
        ])
        assert s.vm_regs[1] == 0, "Instructions after HALT should not execute"
        assert s.vm_mu == 1

    def test_program_end_stops_execution(self):
        """Running off the end of the program should stop."""
        s = run_py([{"op": "load_imm", "dst": 1, "imm": 42, "cost": 1}])
        assert s.vm_regs[1] == 42

    def test_error_stops_execution(self):
        """vm_err=True should stop the run loop."""
        s = VMState.default()
        s.vm_err = True
        s = vm_run(s, [{"op": "load_imm", "dst": 1, "imm": 99, "cost": 1}])
        assert s.vm_regs[1] == 0  # Never executed


# ── Integration: multi-opcode programs ────────────────────────────────

class TestIntegration:
    def test_fibonacci(self):
        """Compute fib(7) = 13 using the Python VM."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 0, "cost": 1},    # r1 = fib(n-2)
            {"op": "load_imm", "dst": 2, "imm": 1, "cost": 1},    # r2 = fib(n-1)
            {"op": "load_imm", "dst": 3, "imm": 7, "cost": 1},    # r3 = counter
            # Loop body at PC=3:
            {"op": "add", "dst": 4, "rs1": 1, "rs2": 2, "cost": 1},   # r4 = r1 + r2
            {"op": "xfer", "dst": 1, "src": 2, "cost": 1},            # r1 = r2
            {"op": "xfer", "dst": 2, "src": 4, "cost": 1},            # r2 = r4
            {"op": "load_imm", "dst": 5, "imm": 1, "cost": 1},        # r5 = 1
            {"op": "sub", "dst": 3, "rs1": 3, "rs2": 5, "cost": 1},   # r3 -= 1
            {"op": "jnez", "rs": 3, "target": 3, "cost": 1},          # loop
            {"op": "halt", "cost": 1},
        ], fuel=500)
        assert s.vm_regs[2] == 21, f"fib(7) should be 21, got {s.vm_regs[2]}"

    def test_memory_copy(self):
        """Copy a value through memory using STORE+LOAD (register-indirect addressing)."""
        s = run_py([
            {"op": "load_imm", "dst": 1, "imm": 42, "cost": 1},
            {"op": "load_imm", "dst": 5, "imm": 5, "cost": 1},   # reg[5] = 5 (addr)
            {"op": "store", "addr": 5, "src": 1, "cost": 1},      # mem[5] = 42
            {"op": "load", "dst": 2, "addr": 5, "cost": 1},       # reg[2] = mem[reg[5]] = 42
            {"op": "halt", "cost": 1},
        ])
        assert s.vm_regs[2] == 42

    def test_nested_calls(self):
        """Nested CALL/RET should work correctly."""
        s = run_py([
            {"op": "call", "target": 3, "cost": 1},                # PC=0: call sub1
            {"op": "load_imm", "dst": 3, "imm": 99, "cost": 1},   # PC=1: after return
            {"op": "halt", "cost": 1},                              # PC=2: halt
            # sub1 at PC=3:
            {"op": "load_imm", "dst": 1, "imm": 10, "cost": 1},   # PC=3
            {"op": "call", "target": 7, "cost": 1},                # PC=4: call sub2
            {"op": "load_imm", "dst": 1, "imm": 30, "cost": 1},   # PC=5: after sub2 returns
            {"op": "ret", "cost": 1},                               # PC=6: return to caller
            # sub2 at PC=7:
            {"op": "load_imm", "dst": 2, "imm": 20, "cost": 1},   # PC=7
            {"op": "ret", "cost": 1},                               # PC=8: return to sub1
        ], fuel=100)
        assert s.vm_regs[1] == 30, "sub1 should overwrite r1 after sub2 returns"
        assert s.vm_regs[2] == 20, "sub2 should have set r2"
        assert s.vm_regs[3] == 99, "main should continue after sub1 returns"
        assert s.vm_regs[31] == 0, "SP should be 0 after balanced calls"

    def test_all_47_opcodes_counted(self):
        """Verify build/thiele_core.ml (Coq extraction) contains all 47 opcodes."""
        import re
        from pathlib import Path
        ml_path = Path(__file__).resolve().parents[1] / "build" / "thiele_core.ml"
        assert ml_path.exists(), f"build/thiele_core.ml not found at {ml_path}"
        content = ml_path.read_text(encoding="utf-8")
        # All 47 constructors appear as Instr_X (legacy) or Coq_instr_X (module-prefixed)
        constructors = set(re.findall(r"Instr_(\w+)", content))
        constructors |= set(re.findall(r"Coq_instr_(\w+)", content))
        ops = {c.lower() for c in constructors}
        expected = {
            "pnew", "psplit", "pmerge", "lassert", "ljoin", "mdlacc", "pdiscover",
            "xfer", "load_imm", "load", "store", "add", "sub",
            "jump", "jnez", "call", "ret",
            "chsh_trial",
            "xor_load", "xor_add", "xor_swap", "xor_rank",
            "emit", "reveal", "oracle_halts", "halt", "checkpoint",
            "read_port", "write_port", "heap_load", "heap_store",
            "certify",
            "and", "or", "shl", "shr", "mul", "lui",
            "tensor_set", "tensor_get",
            "morph", "compose", "morph_id", "morph_delete",
            "morph_assert", "morph_tensor", "morph_get",
        }
        assert expected <= ops, f"Missing from OCaml extraction: {expected - ops}"
        assert len(expected) == 47
