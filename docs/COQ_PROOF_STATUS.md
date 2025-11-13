# Coq proof status – November 2025 snapshot

This note synchronises the textual dashboards with the live Coq inventories
after the halting-oracle refactor and roadmap scaffolding work.  It is intended
to be a quick reference for reviewers before they drill into
`coq/ADMIT_REPORT.txt` or the comprehensive report.

## Executive summary

- **Core build health:** `make -C coq core` succeeds with Coq 8.19.2 and
  requires no global axioms.
- **Outstanding admits:** 3
  1. `coq/thielemachine/coqproofs/Simulation.v:4323` –
     `utm_no_rule_preserves_tape_len`
  2. `coq/thielemachine/coqproofs/Simulation.v:4346` –
     `utm_no_rule_preserves_cpu_config`
  3. `coq/ThieleMap.v:66` – `thiele_simulates_by_tm` (planning stub, excluded
     from the default build)
- **Global axioms:** 0 (the hyper-halting experiment now wraps the oracle in a
  section hypothesis behind the optional `make -C coq oracle` target)
- **Halting experiments:** automated stress tests and enumerative surveys are
  wired into `tools/verify_end_to_end.py` to ensure the shipped VM does not leak
  a halting oracle.

## Directory overview

| Tier | Path                              | Status                                                       |
| ---- | --------------------------------- | ------------------------------------------------------------ |
| Core | `coq/kernel/`                     | Zero admits/axioms. Ledger, VM encoding, and kernel linkage proofs all pass. |
| Core | `coq/thielemachine/coqproofs/`    | Simulation stack mostly proven; only the two universal-interpreter helpers above remain admitted. |
| Core | `coq/modular_proofs/`             | Helper library for TM/Thiele encodings – zero admits/axioms. |
| Core | `coq/thieleuniversal/coqproofs/`  | Universal interpreter scaffolding; still failing symbolic execution obligations. |
| Bridge | `coq/ThieleMap.v`               | Planning wrapper for the subsumption statement (admitted); the new lemma `thiele_simulates_tm_prefix` records the proven finite-prefix simulation. |
| Optional | `coq/catnet/`, `coq/isomorphism/`, etc. | Self-contained studies; continue to build without admits. |

### Core highlights

- `Simulation.v` – proves the blind interpreter simulates any TM.  Fresh
  helpers (`cpu_state_to_tm_config_core_registers`,
  `cpu_state_to_tm_config_eq_components`,
  `find_rule_start_inv_implies_inv_core`,
  `inv_implies_inv_core`,
  `find_rule_start_inv_cpu_state_to_tm_config_core`,
  `find_rule_start_inv_pc`,
  `cpu_state_to_tm_config_tape_cell`,
  `tape_window_ok_cpu_state_to_tm_config_tape_prefix`,
  `tape_window_ok_cpu_state_to_tm_config_tape_extension`,
  `tape_window_ok_cpu_state_to_tm_config_tape_extension_bound`,
  `cpu_state_to_tm_config_tape_prefix`,
  `find_rule_start_inv_cpu_state_to_tm_config_tape_prefix`,
  `config_ok_tape_fits_window`,
  `config_ok_head_lt_shift_len`,
  `find_rule_start_inv_cpu_state_to_tm_config_components`,
  `find_rule_start_inv_cpu_state_to_tm_config_tape_extension`,
  `find_rule_start_inv_cpu_state_to_tm_config_tape_extension_bound`,
  `find_rule_start_inv_cpu_state_to_tm_config_eq`,
  `find_rule_loop_inv_cpu_state_to_tm_config_components`,
  `find_rule_loop_inv_cpu_state_to_tm_config_tape_extension_bound`,
  `find_rule_loop_inv_cpu_state_to_tm_config_tape_length`,
  `decode_state_cpu_state_to_thiele_state`, the helper
  `find_rule_none_forall`, the new `find_rule_none_skipn`, and
  `find_rule_loop_inv_rule_mismatch`) show that the find-rule invariants and loop
  guards preserve the control registers, fix the program counter at loop entry,
  recover both individual tape cells and (whenever the tape fits inside the
  100-cell window) the entire inspected tape prefix (now bundled with the q/head
  agreements in a single ready-to-use component lemma together with an explicit
  suffix decomposition plus a window-size inequality for the captured tape (now
  complemented by an explicit length identity for the loop states and a
  dedicated equality bridge once the observed tape length matches the
  specification), and with
  the new trio of lemmas lifting those arguments directly from the
  `tape_window_ok` predicate so the proof no longer depends on the full
  `inv` hypothesis for tape reasoning), automatically discharge the tape-window
  and head-position side conditions from `config_ok`, and provide the
  decode/encode round-trip needed once `config_ok` is established, all while
  linking both the `find_rule` guard and the loop invariant back to the core
  invariant and certifying via both the loop invariant and the static
  `find_rule` computation that a failed rule lookup disagrees with every
  scanned rule while the none-result persists across successive `skipn`
  offsets.  The outstanding gaps are the new helper
  `utm_no_rule_preserves_tape_len`, which must show that the ten-step sweep
  leaves the observed tape length unchanged, and the wrapper
  `utm_no_rule_preserves_cpu_config`, which then needs only the guard-restoration
  argument to reapply `find_rule_start_inv` before invoking
  `find_rule_start_inv_cpu_state_to_tm_config_eq`.  Once those two lemmas land,
  the existing component and decode/encode lemmas finish the argument and the
  wrapper `utm_no_rule_implies_halting_cfg` is already proved via
  `decode_state_cpu_state_to_thiele_state_eq`.
- `Separation.v` – constructive Tseitin lower bound used for the sighted vs
  blind separation.
- `Subsumption.v` – combines containment and separation.  Downstream theorems
  now mention the halting-oracle hypothesis explicitly when needed.
- `HardwareBridge.v` – refines the Verilog fetch/decode loop to the abstract
  semantics, enabling trace replay.

## Inventories of admits and hypotheses

The canonical machine-readable listings live in `coq/ADMIT_REPORT.txt` and the
repository-level `ADMIT_REPORT.txt`.  The current state is reproduced below for
quick reference.

### Active admits

| File | Lemma | Notes |
| ---- | ----- | ----- |
| `coq/thielemachine/coqproofs/Simulation.v:4323` | `utm_no_rule_preserves_tape_len` | Requires symbolically executing the ten-instruction no-match sweep and showing the tape window length is unchanged so the equality bridge can fire. |
| `coq/thielemachine/coqproofs/Simulation.v:4346` | `utm_no_rule_preserves_cpu_config` | Depends on the previous lemma plus the guard-restoration argument; once the post-state satisfies `find_rule_start_inv`, `find_rule_start_inv_cpu_state_to_tm_config_eq` finishes the equality. |
| `coq/ThieleMap.v:66` | `thiele_simulates_by_tm` | Roadmap stub capturing the intended subsumption wrapper; file is excluded from the automated build |

### Conditional sections / oracles

- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting
  oracle as a section hypothesis.  Any theorem in that module is conditional on
  `H_correct` and is no longer counted as part of the axiom-free core.

## Regression checks

- `tools/verify_end_to_end.py` now orchestrates pytest, the phase-three
  proofpack audit, the core Coq build, and the halting and Bell verification
  harnesses.  The command fails if the curated stress tests, enumerative survey,
  or receipt pipeline detects a regression.
- Bell artefacts are reproducible with `tools/verify_bell_workflow.py`, which
  regenerates the polytope scan and perturbation summaries and sanity-checks the
  CHSH values for classical, supra-quantum, and PR boxes.

## Next steps

1. Finish `utm_no_rule_preserves_tape_len` / `utm_no_rule_preserves_cpu_config`
   so the containment theorem is axiom/assumption free.
2. Once the universal interpreter is fully mechanised, discharge
   `ThieleMap.v` by wrapping the existing simulation theorem.
3. Continue keeping documentation, admit reports, and the comprehensive audit in
   sync after each proof change.
