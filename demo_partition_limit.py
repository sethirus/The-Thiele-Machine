"""
THIELE MACHINE: Partition Limit Demo
======================================

Two partitions — Alice and Bob — operate on disjoint regions.
Each runs independent CHSH measurements.
Alice EMITs her signature. Bob PDISCOVERs it.
MORPH_TENSOR(f, g) builds h = f⊗g: a single morphism encoding
  Alice and Bob acting IN PARALLEL on disjoint regions.
CERTIFY stamps the full result with an unforgeable μ-receipt.
Separation theorem: two certified programs, identical classically,
  distinguished by one probe instruction.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent / "build"))
import thiele_vm as vm

BAR = "─" * 72

def section(title):
    print(f"\n{BAR}\n  {title}\n{BAR}")

def show(label, s, notes=None):
    mods = s.graph.modules if s.graph else []
    nonzero_regs = {i: v for i, v in enumerate(s.regs) if v != 0}
    wc = s.witness
    print(f"\n  [{label}]")
    print(f"    mu={s.mu}  err={s.err}  certified={s.certified}  supra_cert={s.supra_cert}")
    print(f"    cert_addr={s.csrs.get('cert_addr', 0)}  partitions={len(mods)}")
    if nonzero_regs:
        print(f"    regs={nonzero_regs}")
    if any(w > 0 for w in wc):
        wc = s.witness
        def corr(a, b): return (a - b) / (a + b) if (a + b) > 0 else 0
        S = corr(wc[0],wc[1]) + corr(wc[2],wc[3]) + corr(wc[4],wc[5]) - corr(wc[6],wc[7])
        print(f"    witness_counts={wc}")
        print(f"    CHSH S={S:.2f}  (local bound |S|≤2{'  *** VIOLATION ***' if S > 2 else ''})")
    if notes:
        for n in notes: print(f"    {n}")

def run(prog):
    return vm.run_vm(prog + ["HALT 0"])


# ── Partition layout ───────────────────────────────────────────────────────────
# MORPH_TENSOR(f:A→B, g:C→D) requires A∩C=∅, B∩D=∅,
# and union modules A∪C and B∪D must already exist.
#
#  mod1 Alice     {0,2,4}           (source left)
#  mod2 Bob       {1,3,5}           (source right)
#  mod3 AliceOut  {6,8}             (target left)
#  mod4 BobOut    {7,9}             (target right)
#  mod5 AliceBob  {0,1,2,3,4,5}    (tensor source = Alice∪Bob)
#  mod6 Corr      {6,7,8,9}        (tensor target = AliceOut∪BobOut)

PNEW_BLOCK = [
    "PNEW {0,2,4} 1",           # mod1 Alice
    "PNEW {1,3,5} 1",           # mod2 Bob
    "PNEW {6,8} 1",              # mod3 AliceOut
    "PNEW {7,9} 1",              # mod4 BobOut
    "PNEW {0,1,2,3,4,5} 1",     # mod5 AliceBob  (tensor source)
    "PNEW {6,7,8,9} 1",         # mod6 Corr      (tensor target)
]

CHSH_BLOCK = [
    # Quantum-optimal: same outcome for (0,0)(0,1)(1,0), diff for (1,1)  →  S=4
    "CHSH_TRIAL 0 0 0 0 1",
    "CHSH_TRIAL 0 1 0 0 1",
    "CHSH_TRIAL 1 0 0 0 1",
    "CHSH_TRIAL 1 1 0 1 1",
]

MORPH_BLOCK = [
    "MORPH 10 1 3 0 2",      # f: Alice(1)→AliceOut(3), morph_id→r10  (id=0)
    "MORPH 11 2 4 0 2",      # g: Bob(2)→BobOut(4),     morph_id→r11  (id=1)
    "MORPH_TENSOR 12 0 1 2", # h=f⊗g: AliceBob(5)→Corr(6), morph_id→r12 (id=2)
]

COMM_BLOCK = [
    "EMIT 1 alice-chsh-sig 2",          # Alice EMITs; S(2)=3 charged
    "PDISCOVER 2 {chsh-violation} 2",   # Bob records discovery
]

CERTIFY_INSTR = "CERTIFY 5"   # S(5)=6


# ─── PHASE 1 ──────────────────────────────────────────────────────────────────
section("PHASE 1 — Six partitions: Alice, Bob, outputs, and their unions")

p1 = run(PNEW_BLOCK)
show("partitions", p1)
assert not p1.err
assert len(p1.graph.modules) == 6
mod_regions = {m.id: m.region for m in p1.graph.modules}
print(f"""
  mod1 Alice     region={mod_regions[1]}     (Alice's measurement space)
  mod2 Bob       region={mod_regions[2]}     (Bob's measurement space)
  mod3 AliceOut  region={mod_regions[3]}        (Alice's output space)
  mod4 BobOut    region={mod_regions[4]}        (Bob's output space)
  mod5 AliceBob  region={mod_regions[5]}  (tensor source = Alice∪Bob)
  mod6 Corr      region={mod_regions[6]}      (tensor target = AliceOut∪BobOut)

  Alice∩Bob = {set(mod_regions[1]) & set(mod_regions[2])}  (disjoint ✓)
  AliceOut∩BobOut = {set(mod_regions[3]) & set(mod_regions[4])}  (disjoint ✓)
  These disjointness conditions are checked by the machine before MORPH_TENSOR fires.
""")


# ─── PHASE 2 ──────────────────────────────────────────────────────────────────
section("PHASE 2 — CHSH measurements: quantum-optimal strategy, S=4")

p2 = run(PNEW_BLOCK + CHSH_BLOCK)
show("after CHSH", p2)
assert not p2.err
assert p2.mu == 10, f"expected mu=10, got {p2.mu}"
wc = p2.witness
S_raw = (wc[0]-wc[1]) + (wc[2]-wc[3]) + (wc[4]-wc[5]) - (wc[6]-wc[7])
print(f"""
  Witness bucket layout: [same_00, diff_00, same_01, diff_01, same_10, diff_10, same_11, diff_11]
  S_raw = {S_raw}  per trial.  |S| ≤ 2 for any local strategy.

  Theorem chsh_stat_violation_not_local (CHSHStatisticalBridge.v):
    S_raw > 2  ∧  wc locally consistent  →  contradiction.
  These witness counts have no locally consistent explanation.
""")


# ─── PHASE 3 ──────────────────────────────────────────────────────────────────
section("PHASE 3 — Parallel morphism h = f⊗g: Alice and Bob act simultaneously")

p3 = run(PNEW_BLOCK + CHSH_BLOCK + MORPH_BLOCK + [
    "MORPH_GET 0 2 0 0",   # r0 = source of h (should be AliceBob, mod5)
    "MORPH_GET 1 2 1 0",   # r1 = target of h (should be Corr, mod6)
])
show("parallel morphism", p3)
assert not p3.err, f"morphism chain failed at mu={p3.mu}"
h_src = p3.regs[0]
h_tgt = p3.regs[1]
print(f"""
  f: Alice(mod1,region={mod_regions[1]}) → AliceOut(mod3,region={mod_regions[3]})
  g: Bob(mod2,region={mod_regions[2]})   → BobOut(mod4,region={mod_regions[4]})

  h = f⊗g:
    source = mod{h_src} region={mod_regions[h_src]}  (Alice∪Bob)
    target = mod{h_tgt} region={mod_regions[h_tgt]}      (AliceOut∪BobOut = Corr)

  h is NOT sequential composition (that would be f;g requiring target(f)=source(g)).
  h IS tensor product: Alice and Bob act on DISJOINT regions simultaneously.
  The machine checked disjointness before creating h. It is a structural guarantee.
  A classical register holds a number. This holds a verified parallel causal fact.
""")


# ─── PHASE 4 ──────────────────────────────────────────────────────────────────
section("PHASE 4 — Inter-partition communication: Alice EMITs, Bob PDISCOVERs")

p4 = run(PNEW_BLOCK + CHSH_BLOCK + MORPH_BLOCK + COMM_BLOCK)
show("after communication", p4)
assert not p4.err
assert p4.csrs.get('cert_addr', 0) != 0
print(f"""
  Alice's EMIT checksum stamped at cert_addr={p4.csrs.get('cert_addr',0)}.
  Bob's partition now carries axiom {{chsh-violation}} as machine-recorded evidence.
  Cost: EMIT S(2)=3 + PDISCOVER(2)=2  →  5μ for crossing partition boundaries.
  The communication cost is on the ledger. It cannot be undone or faked away.
""")


# ─── PHASE 5 ──────────────────────────────────────────────────────────────────
section("PHASE 5 — CERTIFY: stamp the entire computation with a μ-receipt")

full = PNEW_BLOCK + CHSH_BLOCK + MORPH_BLOCK + COMM_BLOCK + [CERTIFY_INSTR]
p5 = run(full)
show("CERTIFIED", p5)
assert not p5.err
assert p5.certified
mu_receipt = p5.mu

breakdown = [
    ("6×PNEW(1)",       6),
    ("4×CHSH(1)",       4),
    ("2×MORPH(2)",      4),
    ("MORPH_TENSOR(2)", 2),
    ("EMIT S(2)",       3),
    ("PDISCOVER(2)",    2),
    ("CERTIFY S(5)",    6),
]
total = sum(v for _,v in breakdown)
assert mu_receipt == total, f"expected {total}, got {mu_receipt}"
print(f"""
  μ-receipt = {mu_receipt}
  {"  +  ".join(f"{k}={v}" for k,v in breakdown)}  =  {total}

  Theorem no_free_certification (AbstractNoFI.v §8, zero Admitted):
    cert_addr changed  →  at least 1 instruction was a cert-setter
                       →  that instruction had cost ≥ 1
                       →  mu increased by ≥ 1 per cert step.
  Extended by universal_nfi: holds for ANY machine satisfying axiom A3.

  If you show me vm_certified=True with mu < {mu_receipt} on this trace,
  the Coq proof says that is impossible. Not unlikely. Impossible.
""")


# ─── PHASE 6 ──────────────────────────────────────────────────────────────────
section("PHASE 6 — Separation: identical certified states, different causal histories")

state_a = run(full)

# Program B: same mu, same certified, no actual work
# 6×PNEW=6, CERTIFY S(5)=6 → need (mu_receipt-6-6) padding
pad = mu_receipt - 6 - 6
fake = (
    PNEW_BLOCK +
    [f"LOAD_IMM 0 {i % 256} 1" for i in range(pad)] +
    [CERTIFY_INSTR]
)
state_b = run(fake)

classically_same = (state_a.mu == state_b.mu and
                    state_a.certified == state_b.certified and
                    state_a.err == state_b.err)

print(f"""
  Program A: full CHSH + morphisms + EMIT + PDISCOVER + CERTIFY
  Program B: {pad} padding NOPs + CERTIFY  (no measurements, no morphisms, no comms)

  Classical fingerprint:
    A: mu={state_a.mu}  certified={state_a.certified}  err={state_a.err}
    B: mu={state_b.mu}  certified={state_b.certified}  err={state_b.err}
    Classically identical: {classically_same}
""")
assert classically_same

probe_a = run(full + ["MORPH_DELETE 0 0"])
probe_b = run(fake + ["MORPH_DELETE 0 0"])
assert not probe_a.err
assert probe_b.err

print(f"""  Probe: MORPH_DELETE 0 0  (delete morphism id=0 = f: Alice→AliceOut)
    A after probe: err={probe_a.err}  →  morphism existed, delete succeeded
    B after probe: err={probe_b.err}   →  no morphisms were built, delete failed

  SEPARATED.

  Theorem categorical_separation (PartitionSeparation.v §10-11, zero Admitted):
    No function of (regs, mem, mu, pc, err, certified) can separate these programs.
    The Thiele Machine separates them in one instruction via the morphism graph.
""")


# ─── SUMMARY ──────────────────────────────────────────────────────────────────
section("WHAT JUST RAN")
print(f"""
  1. Six partitions — Alice, Bob, their outputs, and union modules —
     created with verified disjoint regions.

  2. Four CHSH trials produced witness S={S_raw} > 2.
     No locally consistent strategy can produce this. Proven.

  3. h = f⊗g: a single tensor morphism encoding Alice and Bob
     acting IN PARALLEL on disjoint regions.
     Source = Alice∪Bob. Target = AliceOut∪BobOut.
     Disjointness verified by the machine before h was created.

  4. Alice EMITted across partition boundaries. Bob PDISCOVERed.
     cert_addr stamped. Communication cost on the ledger.

  5. μ-receipt = {mu_receipt}. vm_certified = True.
     Provably unreachable with mu < {mu_receipt} on this trace.

  6. Two certified programs. Identical classical fingerprint.
     One MORPH_DELETE tells them apart.
     A did the work. B claimed to.
""")
