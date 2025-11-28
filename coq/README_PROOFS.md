# Coq Proof Development - Verification Status

> **Status (November 2025):** All 88 Coq proof files compile successfully with zero admits and zero axioms. The flagship `thiele_formally_subsumes_turing` theorem is fully proved.

## Overview

This directory contains the mechanized Coq development for the Thiele Machine subsumption theorem. The complete development proves that Turing computation is strictly contained within Thiele computation, with exponential separation on structured problems.

**Statistics:**
- **Total files in build:** 88
- **Admitted statements:** 0 in compiled code
- **Axioms:** 0 in compiled code
- **Coq version:** 8.18.0

## Quick Start

```bash
# Install Coq 8.18.0
sudo apt-get update && sudo apt-get install -y coq coq-theories

# Build all proofs
cd coq
make clean && make all

# Verify build success
echo $?  # Should print 0
```

## Key Theorems

### 1. Subsumption Theorem (`Subsumption.v`)

```coq
Theorem thiele_formally_subsumes_turing :
  (forall tm : TM, forall (Hfit : rules_fit tm),
   thiele_simulates_tm_via_simulation tm Hfit) /\
  strict_advantage_statement.
```

**Meaning:** Every Turing Machine is simulated by a blind Thiele program (containment), AND sighted Thiele has exponential advantage on Tseitin problems (separation). Therefore TM ⊂ Thiele.

### 2. Simulation Theorem (`Simulation.v`)

```coq
Lemma thiele_step_n_tm_correct :
  forall tm p conf n,
    all_steps_ok tm conf n ->
    decode_state tm (thiele_step_n_tm tm p (encode_config tm conf) n) 
    = tm_step_n tm conf n.
```

**Meaning:** A Thiele program correctly simulates n steps of TM execution.

### 3. Separation Theorem (`Separation.v`)

```coq
Theorem thiele_exponential_separation :
  exists (N C D : nat), forall n, n >= N ->
    thiele_sighted_steps (tseitin_family n) <= C * cubic n /\
    thiele_mu_cost (tseitin_family n) <= D * quadratic n /\
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.
```

**Meaning:** Sighted Thiele achieves polynomial time on Tseitin problems while blind TMs require exponential time.

## Directory Structure

```
coq/
├── thieleuniversal/coqproofs/     # Core TM/UTM definitions (7 files)
│   ├── TM.v                       # Turing Machine definition
│   ├── CPU.v                      # CPU model for UTM
│   └── ...
├── thielemachine/coqproofs/       # Main Thiele proofs (35 files)
│   ├── ThieleMachine.v            # Abstract Thiele Machine
│   ├── Simulation.v               # TM simulation proof
│   ├── Separation.v               # Exponential separation
│   ├── Subsumption.v              # Flagship theorem
│   └── ...
├── thielemachine/verification/    # Bridge proofs (4 files)
├── kernel/                        # Kernel proofs (10 files)
├── modular_proofs/                # Reusable components (8 files)
├── physics/, spacetime/, etc.     # Physics studies (9 files)
└── other modules                  # (15 files)
```

## What Each Module Proves

### ThieleUniversal (`thieleuniversal/coqproofs/`)

- **TM.v:** Formal Turing Machine definition with `tm_step` semantics
- **CPU.v:** Simple CPU model for universal interpreter
- **UTM_Program.v:** Universal TM interpreter instruction sequence
- **ThieleUniversal.v:** Summary theorem `thiele_machine_subsumes_tm`

### ThieleMachine Core (`thielemachine/coqproofs/`)

- **ThieleMachine.v:** Abstract Thiele Machine with `Blind` predicate
- **Simulation.v:** TM simulation correctness (`thiele_step_n_tm_correct`)
- **Separation.v:** Exponential separation (`thiele_exponential_separation`)
- **Subsumption.v:** Main theorem (`thiele_formally_subsumes_turing`)
- **PartitionLogic.v:** Partition composition laws, μ-accounting
- **BellInequality.v:** Quantum correlations in Thiele framework
- **HyperThiele_Halting.v:** Halting oracle with μ-cost bounds

### Kernel (`kernel/`)

- **Kernel.v:** Core kernel definitions
- **SimulationProof.v:** Kernel-level simulation
- **MuLedgerConservation.v:** μ-bit conservation proof

## Excluded Files

The following are intentionally excluded from the build:

| Category | Files | Reason |
|----------|-------|--------|
| Sandboxes | `sandboxes/*.v` | Experimental |
| Debug | `debug_no_rule.v` | Debug only |
| Modular Bridge | `verification/modular/*.v` | Archived |

## Verification

```bash
# Check for admits (should find none in compiled code)
grep -r "Admitted\." --include="*.v" . | grep -v "(\*" | grep -v debug

# Check for axioms (should find none)
grep "^Axiom " $(cat _CoqProject | grep "\.v$")

# Full rebuild
make clean && make all
```

## Documentation

- **COMPREHENSIVE_COQ_AUDIT.md** - Complete audit of all 88 proof files
- **AXIOM_INVENTORY.md** - Axiom/admit status (all zero)
- **PROOF_SUCCESS_SUMMARY.md** - Proof completion status

## Related Files

- `documents/The_Thiele_Machine.tex` - Full mathematical paper
- `README.md` (root) - Project overview and receipt verification
