> **ARCHIVAL NOTICE:** This document is preserved for historical context. The final, unified proof and analysis are now complete. For the authoritative summary, see `README.md` and `docs/final_fact_check.md`.

# Project Resonator Overview

The resonator experiment introduces a dedicated period-finding datapath that
contrasts a classical sequential search with a spatially enriched reasoning
network.  The implementation lives in `hardware/resonator/` and ships with a
repeatable synthesis harness so the physical differences between the two
architectures can be inspected directly.

## Hardware design

The `period_finder` module keeps the current claim for the period in hardware,
propagates the claim through a dense combinational evaluation network, and then
feeds the result back into its control loop.【F:hardware/resonator/period_finder.v†L15-L40】【F:hardware/resonator/period_finder.v†L305-L360】
Key datapath features include:

* A bespoke arithmetic library (`modular_reduce`, `modular_add`, `modular_mul`,
  and `modular_pow`) that operates entirely in combinational space while
  remaining parameterised by the modulus width.【F:hardware/resonator/period_finder.v†L46-L147】
* A structural minimiser (`reg_minimal`) that checks divisibility patterns for
  small factors (2, 3, 4, and 5) and vetoes any candidate whose modular orbit
  collapses too early.【F:hardware/resonator/period_finder.v†L198-L253】
* A feedback synthesiser that analyses the forward residue gradient to choose
  the next candidate step, moving effort from temporal iteration into spatial
  evaluation.【F:hardware/resonator/period_finder.v†L273-L303】

For comparison, `classical_period_finder` performs the textbook iteration where
one modular multiplication is executed per clock cycle until the baseline value
reappears.【F:hardware/resonator/classical_period_finder.v†L10-L123】 This design
is intentionally compact: the cost of the search is paid in cycles rather than
logic area.

## Synthesis harness

The script `hardware/resonator/run_the_final_synthesis.sh` runs both designs
through Yosys, emitting JSON netlists and the associated statistics into the
`hardware/resonator/build/` directory when the tool is available.【F:hardware/resonator/run_the_final_synthesis.sh†L1-L21】 The
only runtime prerequisite is the `yosys` binary (available via `sudo apt-get install -y yosys`). Archived logs are not kept in
the repository; auditors generate them locally.

Invoke the trap from the repository root:

```bash
hardware/resonator/run_the_final_synthesis.sh
```

The script will populate the build directory with `classical_period_finder.json`
and `period_finder.json` together with log files that capture the area reports
and runtime characteristics.

## Observed structural differences

Running the synthesis trap highlights two clear distinctions:

* **Gate count and topology.** The classical solver maps to 2,886 cells spread
  across 2,909 wire bits with 43 flip-flops; the resonator consumes 22,046 cells
  and 54,190 wire bits with dense `$_ANDNOT_` and `$_MUX_` fabrics, reflecting
  the spatial encoding of the reasoning loop.【8968fb†L1-L32】【9412bc†L1-L36】
* **Cost profile.** Yosys completes the classical build quickly with modest
  memory, while the resonator run reported a ~292 s user time and a 706 MB peak
  footprint because significantly more combinational structure is explored.
  Both metrics come directly from the synthesis log.【9412bc†L37-L40】

The resulting artefacts are ready for downstream inspection (e.g. loading the
JSON into `yosys -o` or a gate-level visualiser) to study how the resonator’s
claim-propagate-measure loop becomes a physical structure instead of a software
routine.
