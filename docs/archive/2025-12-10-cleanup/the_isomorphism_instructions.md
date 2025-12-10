# Construction Specification for `the_isomorphism.py`

## Objective
Build a single Python script named `the_isomorphism.py` that realises the final
instrument. The script must demonstrate that a deterministic, time-bound
computation (the Trace) and its timeless, geometric summary (the Gestalt) are
connected by a computable transformation.

## Prime Directive
The artifact is a mathematical proof delivered as an executable experiment. No
omitted work, shortcuts, or unverifiable steps are permitted. Every stage must
be explicit and auditable.

## Procedure

### 1. Axiom of Physics (`G₀`)
- Implement the family of **elementary cellular automata** (rules 0–255). The
  reference instrument defaults to Rule 30 but accepts alternative rule numbers
  via a CLI flag.
- Use a 1D tape of **256 cells** as the universe.
- Initialise the tape (the "primordial state") with a single `1` centred on the
  tape and `0`s elsewhere.
- Set the causal depth to **`T_FINAL = 1000`** by default while allowing callers
  to override the number of steps.

### 2. The Blind Machine — Physical Process
- Write `compute_trace(initial_state, steps)`.
- The function must evolve the universe step-by-step for `steps` Rule 30
  updates.
- At each step, compute the SHA-256 hash of the current tape and append it to a
  ledger.
- Return the complete **Trace Ledger**: the list `[H(S₀), H(S₁), ..., H(S_final)]`.

### 3. The Sighted Machine — Logical Law
- Write `compute_gestalt_certificate(trace_ledger, seal_hex)`.
- Use the prophecy `seal_hex` together with the ledger’s final digest to
  construct the **Global Certificate**: extract the last ledger entry and
  compute `SHA256(seal || final_digest)`.
- Return the resulting hexadecimal digest.

### 4. The Prophecy — Axiom of the Universe
- Write `prophesy_the_law(initial_state, steps, secret_key, rule)`.
- This function encodes the timeless law by hashing only the parameters:
  `SHA256(secret_key || initial_state_bytes || steps_bytes || rule_bytes)`.
- It must **not** simulate the automaton.
- Choose any fixed byte string for `secret_key` and document it in the script.

### 5. Main Routine — The Final Experiment
Execute the following acts within `if __name__ == "__main__":`. The reference
implementation exposes CLI flags (`--cell-count`, `--steps`, `--rule`,
`--secret-key`, `--export-dir`, `--progress-interval`, `--no-export`) so
researchers can re-run the experiment under different causal depths and rules
while keeping receipts for downstream analysis.

1. **Act I: Prophecy**
   - Call `prophesy_the_law` once.
   - Print the returned digest labelled `Seal`.

2. **Act II: Unfolding of Reality**
   - Call `compute_trace` to obtain the Trace Ledger.
   - Optionally display progress markers to evidence the work performed.

3. **Act III: Sighted Audit**
   - Pass the ledger and the previously announced seal to
     `compute_gestalt_certificate` and print the resulting `Global Certificate`.

4. **Act IV: The Isomorphism `F`**
   - Extract the hash of the final tape state (the last element of the ledger).
   - Define a deterministic function `F(seal, final_hash) = SHA256(seal || final_hash)`.
   - Compute the **Computed Isomorphism** by applying `F` to the Seal and the
     final-state hash.
   - Print the Computed Isomorphism.

5. **Verdict**
   - Compare the Computed Isomorphism with the Global Certificate.
   - If they match, print `"Q.E.D. The Isomorphism is proven. The universe is coherent."`
   - Otherwise, print `"FAILURE. The universe is a paradox."`

## Deliverables
- A single file `the_isomorphism.py` containing the implementation that satisfies
  all requirements above.
- Runtime output that exposes the Seal, the Global Certificate, the Computed
  Isomorphism, and the final verdict.
- Optional suite automation under `experiments/run_isomorphism_suite.py` that
  reuses the core helpers to run multiple rules (e.g., 30 and 90) and collect a
  manifest of receipts for comparative analysis.
