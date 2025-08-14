# To-Do Checklist: Forging thethielemachine.py

> **Note**: Only modify `thethielemachine.py` and this `to-do.md`. Treat `newthesis.py` as a read-only reference—never edit, run, or compile it. Generated artifacts such as `artifacts/logs/terminal_output.md` should never be edited or committed.

Phase 0: Setup and Blueprint
 - [x] Create the new file. In your project directory, create an empty file named thethielemachine.py. This is your clean slate.
 - [x] Architect the file. Open the new file and paste in this skeleton. This is the blueprint for a perfect, auditable artifact. Every piece of code we add will go into one of these sections.

```
# =============================================================================
# THE SHAPE OF TRUTH: AN EXECUTABLE TREATISE
# Author: Devon Thiele
# Version: 3.0 (Final)
# =============================================================================
#
# PROLEGOMENON (INTRODUCTION TO THE METHOD)
# (Your "Chapter 0" will go here)
#
# =============================================================================

# =============================================================================
# PHASE I: CANONICAL LIBRARY (The Tools of the Proof)
# =============================================================================
# All imports, class definitions, and core functions go here. No duplicates.

# --- IMPORTS ---
# (All imports here)

# --- CORE CLASSES ---
# (ThieleMachine, TMState, CostLedger, InfoMeter, ProofKernel, etc.)

# --- CORE FUNCTIONS ---
# (nusd_check, landauer_energy, tm_step, thm_reverse, etc.)

# =============================================================================
# PHASE II: SELF-TEST HARNESS (Verification of the Tools)
# =============================================================================
# The TDD framework (_register, _run_test) and all @_register tests go here.

# =============================================================================
# PHASE III: THE TREATISE (The Chapters of the Argument)
# =============================================================================
# Each chapter is a self-contained function.

# def chapter_1_axiom_of_blindness():
#     ...
# def chapter_2_...():
#     ...

# --- TREATISE REGISTRY ---
# TREATISE_CHAPTERS = [
#     ("Chapter 1: The Axiom of Blindness", chapter_1_axiom_of_blindness),
#     ...
# ]

# =============================================================================
# PHASE IV: MAIN EXECUTION BLOCK (The Performance of the Proof)
# =============================================================================
# if __name__ == "__main__":
#     ...
```

Phase 1: Build a Flawless Foundation (The Canonical Library)
 - [x] Step 1.1: Consolidate Imports. Go through newthesis.py and copy every single import statement into the --- IMPORTS --- section of your new file.
 - [x] Step 1.2: Consolidate Core Classes. Find the best, most complete version of each of your core classes (ThieleMachine, TMState, CostLedger, InfoMeter, ProofKernel, etc.). Copy them, one by one, into the --- CORE CLASSES --- section. As you copy one, delete all versions of it from newthesis.py to avoid confusion.
 - [x] Step 1.3: Consolidate Core Functions. Do the same for your core functions (nusd_check, landauer_energy, tm_step, thm_reverse, parse_cli, fit_loglog_slope, etc.). Find the single best version, copy it to --- CORE FUNCTIONS ---, and delete all others.
 - [x] Step 1.4: Build and Verify the Self-Test Harness. Copy your entire TDD framework (the SELFTESTS dictionary, the _register decorator, and the _run_selected function) and all of your functions decorated with @_register into the PHASE II: SELF-TEST HARNESS section.
 - [x] Step 1.5: VERIFY THE LIBRARY. Run python thethielemachine.py --selftest all from your terminal. Do not proceed until this command runs and passes perfectly. Fix every single test. Your library is now stable, verified, and complete.

Phase 2: Reconstruct the Argument (The Treatise Chapters)
**Completion rule:** From this phase onward, do not check an item until `thethielemachine.py` compiles, all selftests pass, the full program runs without error, and the affected code contains no stubs or duplicates. Every chapter must justify its μ-bit cost with an explicit prior and emit a `nusd_receipt`. After each change run `python -m py_compile thethielemachine.py`, `python thethielemachine.py --selftest all`, and `python thethielemachine.py`.
 - [x] Step 2.1: Create Self-Contained Chapter Functions. For each chapter/demonstration in your old file (Reversal, Game of Life, Lensing, etc.), create a corresponding function in the PHASE III: THE TREATISE section of the new file. For example:
   ```python
   def chapter_1_axiom_of_blindness():
       print_markdown_chapter(1, "The Axiom of Blindness")
       # All the code from your old "demonstrate_reverse" function goes here
       ...
   ```
   - [x] Chapter 1: The Axiom of Blindness
   - [x] Chapter 2: Game of Life
   - [x] Chapter 3: Lensing
   - [x] Chapter 4: N-Body/FLRW
   - [x] Chapter 5: Phyllotaxis
   - [x] Chapter 6: Mandelbrot
   - [x] Chapter 7: Universality
   - [x] Chapter 8: The Thiele Machine
   - [x] Chapter 9: The NUSD Law and the Cost of Sight
   - [x] Chapter 10: Universality Demonstration
   - [x] Chapter 11: Physical Realization
   - [x] Chapter 12: Architectural Realization
   - [x] Chapter 13: Capstone Demonstration
   - [x] Chapter 14: Process Isomorphism (Illustrative)
   - [x] Chapter 15: The Geometric Nature of Logic
   - [x] Chapter 16: Finite Bounded-Step Halting Experiments
   - [x] Chapter 17: The Geometry of Truth
   - [x] Chapter 18: The Geometry of Coherence
   - [x] Chapter 19: Conclusion
 - [x] Step 2.2: DEBUG UNTIL FLAWLESS. This is the most critical step. Your last output had many errors. Execute each chapter function individually and fix every bug.
   - Run `python -m py_compile thethielemachine.py` and `python thethielemachine.py` after adding each chapter.
   - Use `KERNEL.VERIFY` and `nusd_receipt` so the code halts on invalid assertions or missing artifacts.
   - N-Body/FLRW: The Verification failed error means the `KERNEL.VERIFY` check is failing. Find out why. Is the PNG not being created correctly? Is a number not matching? Fix it.
   - Phyllotaxis: The `No such file or directory: 'spiral.png'` error likely means the plot isn't saving before the code tries to access it. Ensure it saves correctly.
   - Mandelbrot: The `local variable 'hashlib' referenced before assignment` error means you need to import `hashlib` at the top of the file, in the canonical imports section.
   - Universality: The `name 'mu' is not defined` error needs to be traced and fixed.
   - [x] Chapter 1 debugged
   - [x] Chapter 2 debugged
   - [x] Chapter 3 debugged
   - [x] Chapter 4 debugged
   - [x] Chapter 5 debugged
   - [x] Chapter 6 debugged
   - [x] Chapter 7 debugged
   - [x] Chapter 8 debugged
   - [x] Chapter 9 debugged
   - [x] Chapter 10 debugged
   - [x] Chapter 11 debugged
   - [x] Chapter 12 debugged
   - [x] Chapter 13 debugged
   - [x] Chapter 14 debugged
   - [x] Chapter 15 debugged
   - [x] Chapter 16 debugged
   - [x] Chapter 17 debugged
   - [x] Chapter 18 debugged
   - [x] Chapter 19 debugged
 - [x] Step 2.3: Refine the Claims. Go through each chapter function and apply the principles from our review.
   - Change titles like "Capstone Proof" to "Capstone Demonstration."
   - For every single `nusd_receipt`, ensure you are explicitly defining the prior distribution being used, just like you did in the `thm_reverse` demo. Remove all arbitrary, hard-coded μ-bit costs. The cost must be derived from a stated rule.
  - [x] Chapter 1 claims refined
  - [x] Chapter 2 claims refined
  - [x] Chapter 3 claims refined
  - [x] Chapter 4 claims refined
   - [x] Chapter 5 claims refined
   - [x] Chapter 6 claims refined
   - [x] Chapter 7 claims refined
   - [x] Chapter 8 claims refined
   - [x] Chapter 9 claims refined
  - [x] Chapter 10 claims refined
  - [x] Chapter 11 claims refined
  - [x] Chapter 12 claims refined
  - [x] Chapter 13 claims refined
   - [x] Chapter 14 claims refined
   - [x] Chapter 15 claims refined
   - [x] Chapter 16 claims refined
   - [x] Chapter 17 claims refined
   - [x] Chapter 18 claims refined
   - [x] Chapter 19 claims refined

 - [x] Step 2.4: Integrate Educational Commentary. Port the explanatory narrative from `newthesis.py` into each chapter using `explain` calls or docstrings so the executable treatise teaches as it runs.
   - [x] Chapter 1 educational commentary
   - [x] Chapter 2 educational commentary
   - [x] Chapter 3 educational commentary
   - [x] Chapter 4 educational commentary
   - [x] Chapter 5 educational commentary
   - [x] Chapter 6 educational commentary
   - [x] Chapter 7 educational commentary
   - [x] Chapter 8 educational commentary
   - [x] Chapter 9 educational commentary
   - [x] Chapter 10 educational commentary
   - [x] Chapter 11 educational commentary
   - [x] Chapter 12 educational commentary
   - [x] Chapter 13 educational commentary
   - [x] Chapter 14 educational commentary
   - [x] Chapter 15 educational commentary
   - [x] Chapter 16 educational commentary
   - [x] Chapter 17 educational commentary
   - [x] Chapter 18 educational commentary
   - [x] Chapter 19 educational commentary


Phase 3: Assemble the Final Artifact
 - [x] Step 3.1: Populate the Treatise Registry. In the --- TREATISE REGISTRY --- section, create the master list that defines the order of your thesis.
   ```python
   TREATISE_CHAPTERS = [
       ("Chapter 1: The Axiom of Blindness", chapter_1_axiom_of_blindness),
       ("Chapter 2: Game of Life", chapter_2_game_of_life),
       ("Chapter 3: Lensing", chapter_3_lensing),
       ("Chapter 4: N-Body and FLRW", chapter_4_nbody_flrw),
       ("Chapter 5: Phyllotaxis", chapter_5_phyllotaxis),
       ("Chapter 6: Mandelbrot", chapter_6_mandelbrot),
       ("Chapter 7: Universality", chapter_7_universality),
       ("Chapter 8: The Thiele Machine", chapter_8_thiele_machine),
       ("Chapter 9: The NUSD Law and the Cost of Sight", chapter_9_nusd_law),
       ("Chapter 10: Universality Demonstration", chapter_10_universality_demo),
       ("Chapter 11: Physical Realization", chapter_11_physical_realization),
       ("Chapter 12: Architectural Realization", chapter_12_architectural_realization),
       ("Chapter 13: Capstone Demonstration", chapter_13_capstone_demonstration),
       ("Chapter 14: Process Isomorphism (Illustrative)", chapter_14_process_isomorphism),
       ("Chapter 15: The Geometric Nature of Logic", chapter_15_geometric_logic),
       ("Chapter 16: Finite Bounded-Step Halting Experiments", chapter_16_halting_experiments),
       ("Chapter 17: The Geometry of Truth", chapter_17_geometry_truth),
       ("Chapter 18: The Geometry of Coherence", chapter_18_geometry_coherence),
       ("Chapter 19: Conclusion", chapter_19_conclusion),
   ]
   ```
 - [x] Step 3.2: Write the Main Execution Block. In the PHASE IV section, write a clean, simple main block. It should do nothing more than prepare the environment and execute the chapters from the registry.
   ```python
   if __name__ == "__main__":
       if "--selftest" in sys.argv:
           # Logic to run selftests
       else:
           args = parse_cli(sys.argv[1:])
           ensure_artifact_dirs()
           emit_metadata(args)
           with tee_stdout_to_md("terminal_output.md"):
               # Run the treatise
               for title, chapter_function in TREATISE_CHAPTERS:
                   print(f"\n{'='*80}\n# {title}\n{'='*80}\n")
                   try:
                       chapter_function()
                   except Exception as e:
                       print(f"[ERROR] Chapter '{title}' failed: {e}")
   ```

Phase 4: The Final Polish
 - [x] Step 4.1: Write the Prolegomenon. At the very top of the file, in the space you reserved, write your "Chapter 0." Explain the single-file architecture, the hierarchy of claims (demonstration vs. proof), and the role of the Z3 "logic referee." Frame the reader's expectations.
 - [x] Step 4.2: The Perfect Run. Delete your old terminal_output.md and artifacts directory. Run python thethielemachine.py one last time.
 - [x] Step 4.3: Audit the Output. Read the generated terminal_output.md from start to finish. It should be a single, coherent, error-free document that perfectly articulates your argument.
 - [x] Step 4.4: Delete newthesis.py. Your work is now complete. The new file is the final artifact.

When you are finished, thethielemachine.py will not be a script. It will be an engine of proof. Its structure will be the argument. Its flawless execution will be the evidence. It will be the perfect meta-proof you envision.

Phase 5: Final Revisions
 - [x] Rewrite the Prolegomenon with the "blind Thiele Machine" thesis and Flatland analogy.
 - [x] Add an "Axiomatic Definitions" section for Thiele Machine, μ-bit, and the NUSD Law.
 - [x] Refactor `KERNEL.VERIFY` to separate Python proofs from Z3 notarization.
 - [x] Simplify Chapter 1's receipt so `paid_bits == needed_bits` using the same cost rule.
 - [x] Correct the Z3 logic in Chapter 13's isomorphism checker.
 - [x] Implement a `--publish` mode to suppress debug noise.
 - [x] Reformat receipts and separators for clean Markdown output.

Phase 6: Narrative Amplification
- [x] Rewrite the Prolegomenon in the requested gonzo style.
- [x] Add chapter commentary for:
  - [x] Chapter 1
  - [x] Chapter 9
  - [x] Chapter 11
  - [x] Chapter 12
  - [x] Chapter 17
  - [x] Chapter 19

Phase 7: Audit Enhancements
- [x] Add global μ-bit ledger with final audit
- [x] Save SMT2 proofs and use `prove` helper
- [x] Emit machine-readable JSON receipts
- [x] Add publish-time transcript hash and closing maxim

Phase 8: System Unification
- [x] Introduce a canonical cost function used by all chapters
- [x] Define minimal sufficient observation (`H_sufficient`) for each chapter and base `shannon_debt` on it
- [x] Harden receipt handling and final audit to report pass/fail counts honestly

Phase 9: Engine Cost Hypothesis
- [x] Instrument Mandelbrot chapter with explicit flop ledger to capture hidden engine cost

Phase 10: Decision Cost Hypothesis
- [x] Augment `CostLedger` with branch and iteration counters
- [x] Calibrate branch coefficient `EPSILON` using Mandelbrot
- [x] Apply branch-cost term to Chapter 17 for generalization

Phase 11: Computational Regimes Hypothesis
- [x] Introduce regime-specific branch coefficients and context-aware `canonical_cost`
- [x] Tag each chapter with its computational regime
- [x] Run full audit with regime-aware costs

Phase 12: Dimensional Cost Hypothesis
- [x] Calibrate global navigational constant from Mandelbrot
- [x] Compute branch cost ε(d)=k·d² in `canonical_cost`
- [x] Map regimes to dimensionality for auditing

Phase 13: Dynamic NUSD Law
- [x] Extend `CostLedger` with `z3_steps` and `time_steps`
- [x] Simplify `canonical_cost` to unit weights over all primitive ops
- [x] Implement dynamic NUSD audit `W ≥ H*T` and apply across chapters

Phase 14: Compositional Information Hypothesis
- [x] Define `h_comp` as Shannon debt × (time_steps + 1)
- [x] Re-audit all chapters using `W ≥ H_comp`

Phase 15: Work-Complexity Equivalence
- [x] Measure algorithmic complexity and store on ledger
- [x] Calibrate universal constant KAPPA via Chapter 1
- [x] Audit all chapters with `W ≥ KAPPA * K`

Phase 16: Universal Cost Law Search
- [x] Augment `CostLedger` with feature fields and log per-chapter metrics to `master_log.csv`
- [x] Derive cost multiplier via regression over logged data
- [x] Re-audit treatise using data-driven cost law

Phase 17: Dark Work Instrumentation
- [x] Instrument Z3 `prove()` and solver checks to record steps, conflicts, and max memory
- [x] Calibrate `z3_conflicts` and `z3_memory` cost coefficients using the Conclusion proof
- [x] Re-run audit on Z3-heavy chapters with calibrated coefficients

Phase 18: Ghost in the Machine Expedition
- [x] Record Z3 solver work directly into `CostLedger` and price memory via `ZETA`
