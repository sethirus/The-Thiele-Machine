"""Thiele CPU Interactive Debugger/Simulator.

Pure-Python cycle-accurate simulator matching the Kami-extracted RTL semantics.
Supports breakpoints, single-stepping, state inspection, and execution replay.

Usage:
    python -m thielecpu.debugger program.asm
    python -m thielecpu.debugger program.hex --hex
"""

from __future__ import annotations

import cmd
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

from thielecpu.assembler import OPCODES, Assembler

# Reverse opcode map
OPCODE_NAMES: Dict[int, str] = {v: k for k, v in OPCODES.items()}


class ThieleVM:
    """Pure-Python Thiele CPU simulator matching RTL semantics."""

    def __init__(self) -> None:
        self.regs: List[int] = [0] * 32   # r0-r31 (r31 = SP)
        self.mem: List[int] = [0] * 256    # data memory
        self.imem: List[int] = [0] * 256   # instruction memory
        self.pc: int = 0
        self.mu: int = 0
        self.mu_tensor: List[int] = [0] * 16
        self.halted: bool = False
        self.err: bool = False
        self.error_code: int = 0
        self.partition_ops: int = 0
        self.mdl_ops: int = 0
        self.info_gain: int = 0
        self.cycle: int = 0
        self.history: List[dict] = []  # for replay

    def _save_state(self) -> dict:
        return {
            "regs": list(self.regs),
            "mem": list(self.mem),
            "pc": self.pc,
            "mu": self.mu,
            "mu_tensor": list(self.mu_tensor),
            "halted": self.halted,
            "err": self.err,
            "error_code": self.error_code,
            "partition_ops": self.partition_ops,
            "mdl_ops": self.mdl_ops,
            "info_gain": self.info_gain,
            "cycle": self.cycle,
        }

    def _restore_state(self, state: dict) -> None:
        self.regs = list(state["regs"])
        self.mem = list(state["mem"])
        self.pc = state["pc"]
        self.mu = state["mu"]
        self.mu_tensor = list(state["mu_tensor"])
        self.halted = state["halted"]
        self.err = state["err"]
        self.error_code = state["error_code"]
        self.partition_ops = state["partition_ops"]
        self.mdl_ops = state["mdl_ops"]
        self.info_gain = state["info_gain"]
        self.cycle = state["cycle"]

    def load_program(self, instr_words: List[int], data_words: Optional[List[int]] = None) -> None:
        for i, w in enumerate(instr_words[:256]):
            self.imem[i] = w & 0xFFFFFFFF
        if data_words:
            for i, w in enumerate(data_words[:256]):
                self.mem[i] = w & 0xFFFFFFFF

    def _mask(self, val: int) -> int:
        return val & 0xFFFFFFFF

    def _popcount(self, val: int) -> int:
        """32-bit popcount matching RTL implementation."""
        v = val & 0xFFFFFFFF
        return bin(v).count("1")

    def step(self) -> None:
        """Execute one instruction. Matches RTL single-cycle semantics."""
        if self.halted:
            return

        self.history.append(self._save_state())

        instr = self.imem[self.pc & 0xFF]
        opcode = (instr >> 24) & 0xFF
        op_a = (instr >> 16) & 0xFF
        op_b = (instr >> 8) & 0xFF
        cost = instr & 0xFF
        cost32 = cost

        # Bianchi conservation check
        tensor_sum = sum(self.mu_tensor)
        bianchi_violation = tensor_sum > self.mu

        if bianchi_violation:
            self.halted = True
            self.err = True
            self.error_code = 0x0B1A4C81
            return

        # Charge mu
        new_mu = self._mask(self.mu + cost32)

        op_name = OPCODE_NAMES.get(opcode, f"UNKNOWN({opcode:#x})")

        if opcode == 0xFF:  # HALT
            self.mu = new_mu
            self.halted = True
            return

        # CHSH validation
        if opcode == 0x09:  # CHSH_TRIAL
            if op_a > 1 or op_b > 1:
                self.err = True
                self.error_code = 0xC43471A1
                self.mu = new_mu
                self.pc = (self.pc + 1) & 0xFF
                return

        # Execute instruction
        if opcode == 0x00:  # PNEW
            self.partition_ops += 1
        elif opcode == 0x01:  # PSPLIT
            self.partition_ops += 1
        elif opcode == 0x02:  # PMERGE
            self.partition_ops += 1
        elif opcode == 0x03:  # LASSERT
            pass
        elif opcode == 0x04:  # LJOIN
            pass
        elif opcode == 0x05:  # MDLACC
            self.mdl_ops += 1
            # Q16.16 scaling: acc += (cost * 65536)
        elif opcode == 0x06:  # PDISCOVER
            self.info_gain += op_b
        elif opcode == 0x07:  # XFER
            dst = op_a & 0x1F
            src = op_b & 0x1F
            self.regs[dst] = self.regs[src]
        elif opcode == 0x08:  # LOAD_IMM
            dst = op_a & 0x1F
            self.regs[dst] = op_b
        elif opcode == 0x09:  # CHSH_TRIAL
            pass  # validation handled above
        elif opcode == 0x0A:  # XOR_LOAD
            dst = op_a & 0x1F
            addr = op_b & 0xFF
            self.regs[dst] = self.mem[addr]
        elif opcode == 0x0B:  # XOR_ADD
            dst = op_a & 0x1F
            src = op_b & 0x1F
            self.regs[dst] = self._mask(self.regs[dst] ^ self.regs[src])
        elif opcode == 0x0C:  # XOR_SWAP
            a = op_a & 0x1F
            b = op_b & 0x1F
            self.regs[a], self.regs[b] = self.regs[b], self.regs[a]
        elif opcode == 0x0D:  # XOR_RANK
            dst = op_a & 0x1F
            src = op_b & 0x1F
            self.regs[dst] = self._popcount(self.regs[src])
        elif opcode == 0x0E:  # EMIT
            self.info_gain += op_b
        elif opcode == 0x0F:  # REVEAL
            idx = op_a & 0xF
            self.mu_tensor[idx] = self._mask(self.mu_tensor[idx] + cost32)
        elif opcode == 0x10:  # ORACLE_HALTS
            pass
        elif opcode == 0x11:  # LOAD
            dst = op_a & 0x1F
            addr = op_b & 0xFF
            self.regs[dst] = self.mem[addr]
        elif opcode == 0x12:  # STORE
            addr = op_a & 0xFF
            src = op_b & 0x1F
            self.mem[addr] = self.regs[src]
        elif opcode == 0x13:  # ADD
            dst = op_a & 0x1F
            rs1 = (op_b >> 4) & 0xF
            rs2 = op_b & 0xF
            self.regs[dst] = self._mask(self.regs[rs1] + self.regs[rs2])
        elif opcode == 0x14:  # SUB
            dst = op_a & 0x1F
            rs1 = (op_b >> 4) & 0xF
            rs2 = op_b & 0xF
            self.regs[dst] = self._mask(self.regs[rs1] - self.regs[rs2])
        elif opcode == 0x15:  # JUMP
            target = op_a & 0xFF
            self.mu = new_mu
            self.pc = target
            self.cycle += 1
            return
        elif opcode == 0x16:  # JNEZ
            reg = op_a & 0x1F
            target = op_b & 0xFF
            if self.regs[reg] != 0:
                self.mu = new_mu
                self.pc = target
                self.cycle += 1
                return
        elif opcode == 0x17:  # CALL
            target = op_a & 0xFF
            sp = self.regs[31]
            self.mem[sp & 0xFF] = (self.pc + 1) & 0xFF
            self.regs[31] = self._mask(sp + 1)
            self.mu = new_mu
            self.pc = target
            self.cycle += 1
            return
        elif opcode == 0x18:  # RET
            sp = self._mask(self.regs[31] - 1)
            self.regs[31] = sp
            ret_addr = self.mem[sp & 0xFF]
            self.mu = new_mu
            self.pc = ret_addr & 0xFF
            self.cycle += 1
            return

        self.mu = new_mu
        self.pc = (self.pc + 1) & 0xFF
        self.cycle += 1

    def back(self) -> bool:
        """Step backwards one instruction. Returns False if at start."""
        if not self.history:
            return False
        self._restore_state(self.history.pop())
        return True

    def disassemble(self, addr: int) -> str:
        """Disassemble instruction at given address."""
        instr = self.imem[addr & 0xFF]
        opcode = (instr >> 24) & 0xFF
        op_a = (instr >> 16) & 0xFF
        op_b = (instr >> 8) & 0xFF
        cost = instr & 0xFF

        name = OPCODE_NAMES.get(opcode, f"???({opcode:#04x})")

        if opcode == 0xFF:
            return "HALT"
        elif opcode == 0x08:  # LOAD_IMM
            return f"LOAD_IMM r{op_a & 0x1F} {op_b} {cost}"
        elif opcode == 0x07:  # XFER
            return f"XFER r{op_a & 0x1F} r{op_b & 0x1F} {cost}"
        elif opcode in (0x13, 0x14):  # ADD/SUB
            rs1 = (op_b >> 4) & 0xF
            rs2 = op_b & 0xF
            return f"{name} r{op_a & 0x1F} r{rs1} r{rs2} {cost}"
        elif opcode == 0x15:  # JUMP
            return f"JUMP {op_a} {cost}"
        elif opcode == 0x16:  # JNEZ
            return f"JNEZ r{op_a & 0x1F} {op_b} {cost}"
        elif opcode == 0x17:  # CALL
            return f"CALL {op_a} {cost}"
        elif opcode == 0x18:  # RET
            return f"RET {cost}"
        elif opcode == 0x11:  # LOAD
            return f"LOAD r{op_a & 0x1F} [{op_b}] {cost}"
        elif opcode == 0x12:  # STORE
            return f"STORE [{op_a}] r{op_b & 0x1F} {cost}"
        elif opcode == 0x0F:  # REVEAL
            return f"REVEAL [{op_a & 0xF}] {cost}"
        elif opcode == 0x0D:  # XOR_RANK
            return f"XOR_RANK r{op_a & 0x1F} r{op_b & 0x1F} {cost}"
        elif opcode == 0x0C:  # XOR_SWAP
            return f"XOR_SWAP r{op_a & 0x1F} r{op_b & 0x1F} {cost}"
        elif opcode == 0x0B:  # XOR_ADD
            return f"XOR_ADD r{op_a & 0x1F} r{op_b & 0x1F} {cost}"
        elif opcode == 0x0A:  # XOR_LOAD
            return f"XOR_LOAD r{op_a & 0x1F} [{op_b}] {cost}"
        else:
            return f"{name} {op_a} {op_b} {cost}"


class ThieleDebugger(cmd.Cmd):
    """Interactive debugger for the Thiele CPU."""

    intro = "Thiele CPU Debugger. Type 'help' for commands."
    prompt = "(thiele) "

    def __init__(self, vm: ThieleVM, labels: Dict[str, int] = None) -> None:
        super().__init__()
        self.vm = vm
        self.breakpoints: Set[int] = set()
        self.labels = labels or {}
        self.rev_labels: Dict[int, str] = {v: k for k, v in self.labels.items()}
        self._show_current()

    def _show_current(self) -> None:
        """Show current instruction."""
        label = self.rev_labels.get(self.vm.pc, "")
        prefix = f"{label}: " if label else ""
        dis = self.vm.disassemble(self.vm.pc)
        status = "HALTED" if self.vm.halted else "ERROR" if self.vm.err else ""
        print(f"  [{self.vm.cycle:4d}] PC={self.vm.pc:3d}  {prefix}{dis}  mu={self.vm.mu}  {status}")

    def do_step(self, arg: str) -> None:
        """Step N instructions (default 1)."""
        n = int(arg) if arg else 1
        for _ in range(n):
            if self.vm.halted:
                print("CPU is halted.")
                break
            self.vm.step()
        self._show_current()

    do_s = do_step

    def do_back(self, arg: str) -> None:
        """Step backwards N instructions (default 1)."""
        n = int(arg) if arg else 1
        for _ in range(n):
            if not self.vm.back():
                print("At start of execution.")
                break
        self._show_current()

    do_b = do_back

    def do_run(self, arg: str) -> None:
        """Run until halt, error, or breakpoint (max 100000 cycles)."""
        limit = int(arg) if arg else 100000
        for _ in range(limit):
            if self.vm.halted:
                print("CPU halted.")
                break
            if self.vm.pc in self.breakpoints and self.vm.cycle > 0:
                print(f"Breakpoint hit at PC={self.vm.pc}")
                break
            self.vm.step()
        else:
            print(f"Stopped after {limit} cycles (use 'run N' to increase).")
        self._show_current()

    do_r = do_run

    def do_continue(self, arg: str) -> None:
        """Continue execution from current position."""
        self.vm.step()  # skip current breakpoint
        self.do_run(arg)

    do_c = do_continue

    def do_break(self, arg: str) -> None:
        """Set breakpoint: break <addr|label>."""
        if not arg:
            if self.breakpoints:
                for bp in sorted(self.breakpoints):
                    label = self.rev_labels.get(bp, "")
                    print(f"  BP @ PC={bp}  {label}")
            else:
                print("No breakpoints set.")
            return
        if arg in self.labels:
            addr = self.labels[arg]
        else:
            try:
                addr = int(arg, 0)
            except ValueError:
                print(f"Unknown label or address: {arg}")
                return
        self.breakpoints.add(addr)
        print(f"Breakpoint set at PC={addr}")

    do_bp = do_break

    def do_delete(self, arg: str) -> None:
        """Delete breakpoint: delete <addr|label|all>."""
        if arg == "all":
            self.breakpoints.clear()
            print("All breakpoints deleted.")
            return
        if arg in self.labels:
            addr = self.labels[arg]
        else:
            try:
                addr = int(arg, 0)
            except ValueError:
                print(f"Unknown: {arg}")
                return
        self.breakpoints.discard(addr)
        print(f"Breakpoint at PC={addr} deleted.")

    def do_print(self, arg: str) -> None:
        """Print state: print regs|mu|tensor|mem|pc|sp|r<N>|all."""
        arg = arg.strip().lower()
        if not arg or arg == "all":
            self._print_regs()
            self._print_mu()
            return

        if arg == "regs" or arg == "registers":
            self._print_regs()
        elif arg == "mu":
            print(f"  mu = {self.vm.mu}")
        elif arg == "tensor":
            for i in range(16):
                print(f"  mu_tensor[{i:2d}] = {self.vm.mu_tensor[i]}")
            print(f"  tensor_sum = {sum(self.vm.mu_tensor)}")
            print(f"  bianchi_ok = {sum(self.vm.mu_tensor) <= self.vm.mu}")
        elif arg == "mem":
            # Show non-zero memory
            for i in range(256):
                if self.vm.mem[i] != 0:
                    print(f"  mem[{i:3d}] = {self.vm.mem[i]}")
        elif arg == "pc":
            print(f"  PC = {self.vm.pc}")
        elif arg == "sp":
            print(f"  SP (r31) = {self.vm.regs[31]}")
        elif arg.startswith("r") and arg[1:].isdigit():
            idx = int(arg[1:])
            if 0 <= idx <= 31:
                print(f"  r{idx} = {self.vm.regs[idx]}")
            else:
                print(f"  Invalid register: {arg}")
        elif arg == "stats":
            print(f"  cycles       = {self.vm.cycle}")
            print(f"  mu           = {self.vm.mu}")
            print(f"  partition_ops= {self.vm.partition_ops}")
            print(f"  mdl_ops      = {self.vm.mdl_ops}")
            print(f"  info_gain    = {self.vm.info_gain}")
            print(f"  err          = {self.vm.err}")
            print(f"  error_code   = {self.vm.error_code:#010x}")
        else:
            print(f"Unknown: {arg}. Try: regs, mu, tensor, mem, pc, sp, r<N>, stats, all")

    do_p = do_print

    def _print_regs(self) -> None:
        for i in range(0, 32, 4):
            vals = "  ".join(f"r{i+j:2d}={self.vm.regs[i+j]:10d}" for j in range(4))
            print(f"  {vals}")

    def _print_mu(self) -> None:
        print(f"  mu={self.vm.mu}  PC={self.vm.pc}  SP={self.vm.regs[31]}  "
              f"cycle={self.vm.cycle}  halted={self.vm.halted}  err={self.vm.err}")

    def do_disasm(self, arg: str) -> None:
        """Disassemble instructions: disasm [start] [count]."""
        parts = arg.split()
        start = int(parts[0], 0) if parts else self.vm.pc
        count = int(parts[1]) if len(parts) > 1 else 10
        for i in range(count):
            addr = (start + i) & 0xFF
            marker = ">>>" if addr == self.vm.pc else "   "
            bp = "*" if addr in self.breakpoints else " "
            label = self.rev_labels.get(addr, "")
            if label:
                print(f"  {label}:")
            dis = self.vm.disassemble(addr)
            print(f"  {marker}{bp} {addr:3d}  {dis}")

    do_d = do_disasm

    def do_reset(self, arg: str) -> None:
        """Reset CPU to initial state."""
        if self.vm.history:
            self._restore_state(self.vm.history[0])
            self.vm.history.clear()
            print("Reset to initial state.")
        else:
            print("No history available.")
        self._show_current()

    def do_quit(self, arg: str) -> Optional[bool]:
        """Exit debugger."""
        return True

    do_q = do_quit
    do_exit = do_quit
    do_EOF = do_quit


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(
        prog="thiele-debug",
        description="Thiele CPU Interactive Debugger"
    )
    parser.add_argument("input", help="Assembly (.asm) or hex (.hex) file")
    parser.add_argument("--hex", action="store_true", help="Input is hex format")
    parser.add_argument("--run", action="store_true", help="Run to completion (non-interactive)")
    args = parser.parse_args()

    vm = ThieleVM()
    labels: Dict[str, int] = {}

    if args.hex:
        lines = Path(args.input).read_text().strip().split("\n")
        words = [int(line.strip(), 16) for line in lines if line.strip()]
        vm.load_program(words)
    else:
        asm = Assembler()
        try:
            source = Path(args.input).read_text()
            instr_hex, data_hex = asm.assemble(source, filename=args.input)
            labels = asm.labels
        except Exception as e:
            print(f"Assembly error: {e}", file=sys.stderr)
            sys.exit(1)
        instr_words = [int(h, 16) for h in instr_hex]
        data_words = [int(h, 16) for h in data_hex]
        vm.load_program(instr_words, data_words)

    if args.run:
        # Non-interactive: run to completion
        max_cycles = 100000
        for _ in range(max_cycles):
            if vm.halted:
                break
            vm.step()
        print(f"Execution complete: {vm.cycle} cycles")
        print(f"  mu={vm.mu}  halted={vm.halted}  err={vm.err}")
        print(f"  PC={vm.pc}  SP={vm.regs[31]}")
        for i in range(32):
            if vm.regs[i] != 0:
                print(f"  r{i} = {vm.regs[i]}")
        sys.exit(0 if vm.halted and not vm.err else 1)

    dbg = ThieleDebugger(vm, labels)
    dbg.cmdloop()


if __name__ == "__main__":
    main()
