
import sys

# ==============================================================================
# CPU Definitions
# ==============================================================================

REG_PC    = 0
REG_Q     = 1
REG_HEAD  = 2
REG_SYM   = 3
REG_Q_PR  = 4
REG_WRITE = 5
REG_MOVE  = 6
REG_ADDR  = 7
REG_TEMP1 = 8
REG_TEMP2 = 9

class Instr: pass
class LoadConst(Instr):
    def __init__(self, rd, val): self.rd, self.val = rd, val
class LoadIndirect(Instr):
    def __init__(self, rd, ra): self.rd, self.ra = rd, ra
class StoreIndirect(Instr):
    def __init__(self, ra, rv): self.ra, self.rv = ra, rv
class CopyReg(Instr):
    def __init__(self, rd, rs): self.rd, self.rs = rd, rs
class AddConst(Instr):
    def __init__(self, rd, val): self.rd, self.val = rd, val
class AddReg(Instr):
    def __init__(self, rd, rs1, rs2): self.rd, self.rs1, self.rs2 = rd, rs1, rs2
class SubReg(Instr):
    def __init__(self, rd, rs1, rs2): self.rd, self.rs1, self.rs2 = rd, rs1, rs2
class Jz(Instr):
    def __init__(self, rc, target): self.rc, self.target = rc, target
class Jnz(Instr):
    def __init__(self, rc, target): self.rc, self.target = rc, target
class Halt(Instr): pass

class State:
    def __init__(self, regs, mem, cost):
        self.regs = list(regs)
        self.mem = list(mem)
        self.cost = cost
    def clone(self): return State(list(self.regs), list(self.mem), self.cost)

def read_reg(r, st): return st.regs[r] if r < len(st.regs) else 0
def write_reg(r, v, st):
    st = st.clone()
    if r < len(st.regs): st.regs[r] = v
    else:
        st.regs.extend([0] * (r - len(st.regs) + 1))
        st.regs[r] = v
    return st
def read_mem(addr, st): return st.mem[addr] if addr < len(st.mem) else 0
def write_mem(addr, v, st):
    st = st.clone()
    if addr < len(st.mem): st.mem[addr] = v
    else:
        st.mem.extend([0] * (addr - len(st.mem) + 1))
        st.mem[addr] = v
    return st

def step(i, st):
    pc = read_reg(REG_PC, st)
    st_next = write_reg(REG_PC, pc + 1, st)
    cost = 1
    if isinstance(i, LoadConst): st_next = write_reg(i.rd, i.val, st_next)
    elif isinstance(i, LoadIndirect):
        cost = 2; val = read_mem(read_reg(i.ra, st), st)
        st_next = write_reg(i.rd, val, st_next)
    elif isinstance(i, StoreIndirect):
        cost = 5; st_next = write_mem(read_reg(i.ra, st), read_reg(i.rv, st), st_next)
    elif isinstance(i, CopyReg): st_next = write_reg(i.rd, read_reg(i.rs, st), st_next)
    elif isinstance(i, AddConst): st_next = write_reg(i.rd, read_reg(i.rd, st) + i.val, st_next)
    elif isinstance(i, AddReg): st_next = write_reg(i.rd, read_reg(i.rs1, st) + read_reg(i.rs2, st), st_next)
    elif isinstance(i, SubReg):
        val = read_reg(i.rs1, st) - read_reg(i.rs2, st)
        if val < 0: val = 0
        st_next = write_reg(i.rd, val, st_next)
    elif isinstance(i, Jz):
        if read_reg(i.rc, st) == 0: st_next = write_reg(REG_PC, i.target, st)
    elif isinstance(i, Jnz):
        if read_reg(i.rc, st) != 0: st_next = write_reg(REG_PC, i.target, st)
    elif isinstance(i, Halt): st_next = st.clone()
    st_next.cost += cost
    return st_next

def run_n(st, n, program_instrs):
    for _ in range(n):
        pc = read_reg(REG_PC, st)
        instr = program_instrs[pc] if pc < len(program_instrs) else Halt()
        st = step(instr, st)
    return st

# ==============================================================================
# UTM Encoding
# ==============================================================================
RULES_START_ADDR = 100
TAPE_START_ADDR = 1000
program_instrs = [
    LoadConst(REG_TEMP1, TAPE_START_ADDR), AddReg(REG_ADDR, REG_TEMP1, REG_HEAD), LoadIndirect(REG_SYM, REG_ADDR),
    LoadConst(REG_ADDR, RULES_START_ADDR), LoadIndirect(REG_Q_PR, REG_ADDR), CopyReg(REG_TEMP1, REG_Q),
    SubReg(REG_TEMP1, REG_TEMP1, REG_Q_PR), Jz(REG_TEMP1, 12), AddConst(REG_ADDR, 5), Jnz(REG_TEMP1, 4),
    LoadConst(REG_TEMP1, 0), Jnz(REG_TEMP1, 0), CopyReg(REG_TEMP1, REG_ADDR), AddConst(REG_TEMP1, 1),
    LoadIndirect(REG_TEMP2, REG_TEMP1), CopyReg(REG_TEMP1, REG_SYM), SubReg(REG_TEMP1, REG_TEMP1, REG_TEMP2),
    Jz(REG_TEMP1, 22), AddConst(REG_ADDR, 5), LoadConst(REG_TEMP1, 1), Jnz(REG_TEMP1, 4),
    LoadConst(REG_TEMP1, 0), CopyReg(REG_TEMP1, REG_ADDR), AddConst(REG_TEMP1, 2), LoadIndirect(REG_Q_PR, REG_TEMP1),
    AddConst(REG_TEMP1, 1), LoadIndirect(REG_WRITE, REG_TEMP1), AddConst(REG_TEMP1, 1), LoadIndirect(REG_MOVE, REG_TEMP1),
    CopyReg(REG_TEMP1, REG_HEAD), LoadConst(REG_TEMP2, TAPE_START_ADDR), AddReg(REG_ADDR, REG_TEMP1, REG_TEMP2),
    StoreIndirect(REG_ADDR, REG_WRITE), CopyReg(REG_TEMP1, REG_MOVE), Jnz(REG_TEMP1, 38), LoadConst(REG_TEMP2, 1),
    SubReg(REG_HEAD, REG_HEAD, REG_TEMP2), Jnz(REG_TEMP2, 46), LoadConst(REG_TEMP2, 1), SubReg(REG_TEMP1, REG_MOVE, REG_TEMP2),
    Jnz(REG_TEMP1, 43), LoadConst(REG_TEMP1, 1), Jnz(REG_TEMP1, 46), LoadConst(REG_TEMP2, 1), AddReg(REG_HEAD, REG_HEAD, REG_TEMP2),
    Jnz(REG_TEMP2, 46), CopyReg(REG_Q, REG_Q_PR), LoadConst(REG_TEMP1, 1), Jnz(REG_TEMP1, 0)
]

def encode_instr_words(i):
    if isinstance(i, LoadConst): return [0, i.rd, i.val, 0]
    if isinstance(i, LoadIndirect): return [1, i.rd, i.ra, 0]
    if isinstance(i, StoreIndirect): return [2, i.ra, i.rv, 0]
    if isinstance(i, CopyReg): return [3, i.rd, i.rs, 0]
    if isinstance(i, AddConst): return [4, i.rd, i.val, 0]
    if isinstance(i, AddReg): return [5, i.rd, i.rs1, i.rs2]
    if isinstance(i, SubReg): return [6, i.rd, i.rs1, i.rs2]
    if isinstance(i, Jz): return [7, i.rc, i.target, 0]
    if isinstance(i, Jnz): return [8, i.rc, i.target, 0]
    return [9, 0, 0, 0]

def encode_z(z): return 0 if z == -1 else (1 if z == 0 else 2)
def encode_rules(rules):
    res = []
    for (q, s, q_next, w, m) in rules: res.extend([q, s, q_next, w, encode_z(m)])
    return res
def pad_to(n, l): return l + [0] * (n - len(l)) if len(l) < n else l

def setup_state(tm_rules, q, tape, head):
    regs0 = [0] * 10
    regs0[REG_Q] = q; regs0[REG_HEAD] = head; regs0[REG_PC] = 0
    encoded_program = []
    for instr in program_instrs: encoded_program.extend(encode_instr_words(instr))
    encoded_rules = encode_rules(tm_rules)
    mem = pad_to(TAPE_START_ADDR, pad_to(RULES_START_ADDR, encoded_program) + encoded_rules) + tape
    return State(regs0, mem, 0)

def main():
    tm_rules = [(99, 0, 99, 0, 0), (98, 0, 98, 0, 0), (0, 0, 0, 1, 1), (0, 1, 1, 0, -1)]
    tape = [0, 0, 0, 0, 0]; q = 0; head = 0
    cpu_state = setup_state(tm_rules, q, tape, head)

    output_path = "coq/thielemachine/verification/BridgeCheckpoints.v"
    with open(output_path, "w") as f:
        f.write("From ThieleUniversal Require Import CPU.\nRequire Import List.\nImport ListNotations.\n\n")
        checkpoints = [0, 3, 9, 15, 19]
        current_step = 0
        for target in checkpoints:
            steps_needed = target - current_step
            if steps_needed > 0:
                cpu_state = run_n(cpu_state, steps_needed, program_instrs)
                current_step = target
            regs_str = "[" + "; ".join(map(str, cpu_state.regs)) + "]"
            mem_str = "[" + "; ".join(map(str, cpu_state.mem)) + "]"
            f.write(f"Definition checkpoint_{target} : CPU.State := {{| CPU.regs := {regs_str}; CPU.mem := {mem_str}; CPU.cost := {cpu_state.cost} |}}.\n\n")

if __name__ == "__main__": main()
