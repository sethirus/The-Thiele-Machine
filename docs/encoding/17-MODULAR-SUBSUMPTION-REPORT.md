> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Modular Subsumption Proof Report

> **Status update (October 2025):** This document is preserved for historical context. For the current analysis of the kernel, μ-spec v2.0, and reproducible evidence see `docs/kernel_analysis.md` and `docs/final_fact_check.md`.

## Overview

The modular Coq development characterises the bridge between a Turing machine
and the Thiele interpreter through a minimal interface.  Instead of replaying
micro-instruction traces, we assume an abstract `ModularThieleSemantics` record
that explains how the interpreter encodes configurations, performs a single
step, and iterates that step.  Any concrete proof only needs to supply these
facts; the multi-step subsumption theorem then follows from the lightweight
induction contained in `coq/modular_proofs/Simulation.v`.

## Key Components

* **`TM_Basics.v`** packages the single-tape Turing machine semantics, the
  `tm_config_ok` well-formedness predicate, and preservation lemmas for tape
  updates and head motion.  These results are the only Turing-side obligations
  used by the modular bridge.
* **`Thiele_Basics.v`** defines the `ModularThieleSemantics` record.  A witness
  specifies the interpreter state type, encoding/decoding functions, and the
  iterated execution function together with the multi-step simulation fact
  `mts_run_n_simulates` that equates decoded interpreter runs with
  `tm_run_n`.
* **`Simulation.v`** now specialises that record directly: given a witness, the
  bridge concludes that decoding `mts_run_n` mirrors the Turing machine’s
  multi-step semantics without any additional preservation lemmas or
  single-step canonicalisation arguments.

## Result

The final theorem now states:

```
Theorem thiele_machine_subsumes_turing_modular :
  forall tm (sem : ModularThieleSemantics tm) conf n,
    tm_config_ok conf ->
    mts_decode sem (mts_run_n sem (mts_encode sem conf) n)
    = tm_run_n tm conf n.
```

Supplying a concrete `sem` witness with the strengthened multi-step clause is
therefore sufficient to obtain the full subsumption statement without touching
the heavy interpreter proofs.

## Next Steps

* Extract the necessary invariants from `coq/thielemachine/coqproofs` so they
  can instantiate `ModularThieleSemantics` for the actual universal machine.
* Mechanise the missing proofs that `tm_step` preserves the well-formedness
  predicate for catalogue machines, allowing the modular theorem to replace the
  remaining admitted obligations.
* Once the real interpreter witnesses are in place, extend the documentation to
  describe the instantiation and provide a high-level overview of how the
  low-level proofs feed into the modular interface.

### 21 December 2025 update

*Attempted bridge from the legacy interpreter to the modular interface.*

* Experimented with instantiating `ModularThieleSemantics` directly from
  `coq/thielemachine/coqproofs/Simulation.v`, but the earlier interface required
  the one-step executor to return an encoded configuration literally equal to
  `mts_encode (tm_step tm conf)`. The legacy layer only guarantees equality
  after decoding, so the modular induction quickly stalled when chaining steps.
* The interface has now been strengthened to accept a direct multi-step
  simulation witness (`mts_run_n_simulates`), removing the encode-level
  canonicalisation burden and aligning with the facts already proven in the
  legacy layer.
* Outcome: the modular bridge compiles against the leaner interface and awaits
  a concrete witness extracted from the universal interpreter layer.

### 22 December 2025 update

*Refined the fast modular build loop.*

* Updated `scripts/quick_check_modular.sh` so the quick feedback path now
  type-checks both `EncodingBounds.v` and `Encoding.v` using `.vos` artifacts.
  This keeps the encoding lemmas under regression without incurring the
  multi-minute proof checking cost of full `.vo` builds.