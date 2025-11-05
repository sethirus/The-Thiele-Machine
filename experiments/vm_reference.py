#!/usr/bin/env python3
# experiments/vm_reference.py
# Minimal reference VM that mirrors the Coq notions needed for instrumentation:
# - simple instruction set with instruction_cost
# - vm_apply updates vm_mu = vm_mu + instruction_cost(instr)
# - run_vm executes up to `fuel` steps and logs per-step (step,vm_mu,delta)
#
# Usage:
#  python3 experiments/vm_reference.py --seed 0 --fuel 20 --trace_len 50 --out logs/run0.log

import os
import csv
import argparse
import random
import math

def ensure_dir(p):
    os.makedirs(p, exist_ok=True)

# Simple instruction representation
class Instr:
    def __init__(self, name, cost_bits):
        self.name = name
        self.cost_bits = cost_bits  # interpret as "bits" for ledger

def instruction_cost(instr: Instr) -> float:
    return float(instr.cost_bits)

# Simple VM state
class VMState:
    def __init__(self, pc=0, vm_mu=0.0):
        self.vm_pc = pc
        self.vm_mu = float(vm_mu)

def vm_apply(s: VMState, instr: Instr) -> VMState:
    # advance pc by 1 and update vm_mu by instruction_cost
    new = VMState(pc=s.vm_pc + 1, vm_mu=s.vm_mu + instruction_cost(instr))
    return new

def ledger_entries(fuel, trace, s):
    entries = []
    st = VMState(pc=s.vm_pc, vm_mu=s.vm_mu)
    for _ in range(fuel):
        if st.vm_pc < 0 or st.vm_pc >= len(trace):
            break
        instr = trace[st.vm_pc]
        entries.append(instruction_cost(instr))
        st = vm_apply(st, instr)
    return entries

def bounded_run(fuel, trace, s):
    states = []
    st = VMState(pc=s.vm_pc, vm_mu=s.vm_mu)
    for _ in range(fuel):
        states.append(VMState(pc=st.vm_pc, vm_mu=st.vm_mu))
        if st.vm_pc < 0 or st.vm_pc >= len(trace):
            break
        instr = trace[st.vm_pc]
        st = vm_apply(st, instr)
    # include final state if loop ended early or fuel exhausted
    states.append(VMState(pc=st.vm_pc, vm_mu=st.vm_mu))
    return states

def generate_random_trace(length, rng, max_cost_bits=3):
    trace = []
    for i in range(length):
        cost = rng.randint(0, max_cost_bits)  # bits
        trace.append(Instr(name=f"instr_{i}", cost_bits=cost))
    return trace

def write_log(path, records):
    ensure_dir(os.path.dirname(path) or ".")
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        # header
        w.writerow(["step", "vm_mu", "delta"])
        for rec in records:
            # delta may be empty for initial row
            step = rec.get("step")
            vm_mu = rec.get("vm_mu")
            delta = rec.get("delta")
            if delta is None:
                w.writerow([step, vm_mu, ""])
            else:
                w.writerow([step, vm_mu, delta])

def run_reference(seed, fuel, trace_len, out, initial_mu, max_cost_bits):
    rng = random.Random(seed)
    trace = generate_random_trace(trace_len, rng, max_cost_bits=max_cost_bits)
    s0 = VMState(pc=0, vm_mu=initial_mu)
    records = []
    # initial record (step 0)
    records.append({"step": 0, "vm_mu": s0.vm_mu, "delta": None})
    st = VMState(pc=s0.vm_pc, vm_mu=s0.vm_mu)
    for step in range(1, fuel + 1):
        if st.vm_pc < 0 or st.vm_pc >= len(trace):
            # no instruction, end
            records.append({"step": step, "vm_mu": st.vm_mu, "delta": None})
            break
        instr = trace[st.vm_pc]
        st_next = vm_apply(st, instr)
        # delta recorded is instruction_cost(instr)
        records.append({"step": step, "vm_mu": st_next.vm_mu, "delta": instruction_cost(instr)})
        st = st_next
    write_log(out, records)
    return out

def main():
    parser = argparse.ArgumentParser(description="Reference VM that emits per-step ledger logs.")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--fuel", type=int, default=20)
    parser.add_argument("--trace_len", type=int, default=50)
    parser.add_argument("--out", type=str, default="logs/run0.log")
    parser.add_argument("--initial_mu", type=float, default=0.0)
    parser.add_argument("--max_cost_bits", type=int, default=3)
    args = parser.parse_args()

    out = run_reference(args.seed, args.fuel, args.trace_len, args.out, args.initial_mu, args.max_cost_bits)
    print("Wrote VM ledger log:", out)

if __name__ == "__main__":
    main()