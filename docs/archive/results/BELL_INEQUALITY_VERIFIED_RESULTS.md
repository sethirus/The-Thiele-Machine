# Bell Inequality Demonstration — Sovereign Witness
A Thiele Machine thesis in six acts.

## Experimental Environment
Deterministic execution envelope and formal toolchain inventory.

Pinned environment variables for reproducibility:
- TZ=UTC
- LC_ALL=C
- LANG=C
- PYTHONHASHSEED=0
Formal toolchain versions detected:
- Python: Python 3.12.10
- Z3: Z3 version 4.15.1 - 64 bit
- Coq: The Coq Proof Assistant, version 8.18.0
- Repository commit: c5fdb206331c65198d293e0a345f12cffe34d3f2
- Host platform: Linux-6.12.13-x86_64-with-glibc2.39
Network isolation is enforced; passing --allow-network explicitly opts into live data fetching.
Decimal arithmetic uses 80 digits of precision; all rational witnesses are emitted exactly.
## Trusted Computing Base
Soundness assumptions that bound the verification perimeter.

- Coq kernel / coqchk validate mechanised receipts; correctness assumes the kernel is sound.
- Analytic certificates are evaluated using Python's exact Decimal and Fraction libraries.
- Recorded SHA-256 manifest binds inputs/outputs; auditors must trust the filesystem integrity.
## Act I — Deriving the Constants
We ground the Tsirelson bound by deriving π and √2 from first principles.

Deriving π from first principles using the Chudnovsky method…
- iteration 0: π ≈ 3.141592653590
- iteration 1: π ≈ 3.141592653590
- iteration 2: π ≈ 3.141592653590
- iteration 3: π ≈ 3.141592653590
Deriving √2 from first principles using the Babylonian method…
- iteration 1: √2 ≈ 1.500000000000
- iteration 2: √2 ≈ 1.416666666667
- iteration 3: √2 ≈ 1.414215686275
- iteration 4: √2 ≈ 1.414213562375
- iteration 5: √2 ≈ 1.414213562373
- iteration 6: √2 ≈ 1.414213562373
- iteration 7: √2 ≈ 1.414213562373
- iteration 8: √2 ≈ 1.414213562373
Calculating the Tsirelson bound 2·√2, the quantum ceiling for CHSH violations.
- Tsirelson bound ≈ 2.828427124746
## Act II — Classical Deterministic Bound
Every local-realist CHSH strategy is enumerated and verified with exact arithmetic.

Classical strategy definitions:
```python
strategies = [
    (Response(out0=0, out1=0), Response(out0=0, out1=0)),
    (Response(out0=0, out1=0), Response(out0=0, out1=1)),
    (Response(out0=0, out1=0), Response(out0=1, out1=0)),
    (Response(out0=0, out1=0), Response(out0=1, out1=1)),
    (Response(out0=0, out1=1), Response(out0=0, out1=0)),
    (Response(out0=0, out1=1), Response(out0=0, out1=1)),
    (Response(out0=0, out1=1), Response(out0=1, out1=0)),
    (Response(out0=0, out1=1), Response(out0=1, out1=1)),
    (Response(out0=1, out1=0), Response(out0=0, out1=0)),
    (Response(out0=1, out1=0), Response(out0=0, out1=1)),
    (Response(out0=1, out1=0), Response(out0=1, out1=0)),
    (Response(out0=1, out1=0), Response(out0=1, out1=1)),
    (Response(out0=1, out1=1), Response(out0=0, out1=0)),
    (Response(out0=1, out1=1), Response(out0=0, out1=1)),
    (Response(out0=1, out1=1), Response(out0=1, out1=0)),
    (Response(out0=1, out1=1), Response(out0=1, out1=1)),
)
```
Strategy 00: S = 2/1 (~2.000000)
```text
Strategy 00
  setting (0, 0) -> a=0, b=0, correlator=1
  setting (0, 1) -> a=0, b=0, correlator=1
  setting (1, 0) -> a=0, b=0, correlator=1
  setting (1, 1) -> a=0, b=0, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 01: S = -2/1 (~-2.000000)
```text
Strategy 01
  setting (0, 0) -> a=0, b=0, correlator=1
  setting (0, 1) -> a=0, b=1, correlator=-1
  setting (1, 0) -> a=0, b=0, correlator=1
  setting (1, 1) -> a=0, b=1, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 02: S = 2/1 (~2.000000)
```text
Strategy 02
  setting (0, 0) -> a=0, b=1, correlator=-1
  setting (0, 1) -> a=0, b=0, correlator=1
  setting (1, 0) -> a=0, b=1, correlator=-1
  setting (1, 1) -> a=0, b=0, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 03: S = -2/1 (~-2.000000)
```text
Strategy 03
  setting (0, 0) -> a=0, b=1, correlator=-1
  setting (0, 1) -> a=0, b=1, correlator=-1
  setting (1, 0) -> a=0, b=1, correlator=-1
  setting (1, 1) -> a=0, b=1, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 04: S = -2/1 (~-2.000000)
```text
Strategy 04
  setting (0, 0) -> a=0, b=0, correlator=1
  setting (0, 1) -> a=0, b=0, correlator=1
  setting (1, 0) -> a=1, b=0, correlator=-1
  setting (1, 1) -> a=1, b=0, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 05: S = -2/1 (~-2.000000)
```text
Strategy 05
  setting (0, 0) -> a=0, b=0, correlator=1
  setting (0, 1) -> a=0, b=1, correlator=-1
  setting (1, 0) -> a=1, b=0, correlator=-1
  setting (1, 1) -> a=1, b=1, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 06: S = 2/1 (~2.000000)
```text
Strategy 06
  setting (0, 0) -> a=0, b=1, correlator=-1
  setting (0, 1) -> a=0, b=0, correlator=1
  setting (1, 0) -> a=1, b=1, correlator=1
  setting (1, 1) -> a=1, b=0, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 07: S = 2/1 (~2.000000)
```text
Strategy 07
  setting (0, 0) -> a=0, b=1, correlator=-1
  setting (0, 1) -> a=0, b=1, correlator=-1
  setting (1, 0) -> a=1, b=1, correlator=1
  setting (1, 1) -> a=1, b=1, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 08: S = 2/1 (~2.000000)
```text
Strategy 08
  setting (0, 0) -> a=1, b=0, correlator=-1
  setting (0, 1) -> a=1, b=0, correlator=-1
  setting (1, 0) -> a=0, b=0, correlator=1
  setting (1, 1) -> a=0, b=0, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 09: S = 2/1 (~2.000000)
```text
Strategy 09
  setting (0, 0) -> a=1, b=0, correlator=-1
  setting (0, 1) -> a=1, b=1, correlator=1
  setting (1, 0) -> a=0, b=0, correlator=1
  setting (1, 1) -> a=0, b=1, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 10: S = -2/1 (~-2.000000)
```text
Strategy 10
  setting (0, 0) -> a=1, b=1, correlator=1
  setting (0, 1) -> a=1, b=0, correlator=-1
  setting (1, 0) -> a=0, b=1, correlator=-1
  setting (1, 1) -> a=0, b=0, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 11: S = -2/1 (~-2.000000)
```text
Strategy 11
  setting (0, 0) -> a=1, b=1, correlator=1
  setting (0, 1) -> a=1, b=1, correlator=1
  setting (1, 0) -> a=0, b=1, correlator=-1
  setting (1, 1) -> a=0, b=1, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 12: S = -2/1 (~-2.000000)
```text
Strategy 12
  setting (0, 0) -> a=1, b=0, correlator=-1
  setting (0, 1) -> a=1, b=0, correlator=-1
  setting (1, 0) -> a=1, b=0, correlator=-1
  setting (1, 1) -> a=1, b=0, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 13: S = 2/1 (~2.000000)
```text
Strategy 13
  setting (0, 0) -> a=1, b=0, correlator=-1
  setting (0, 1) -> a=1, b=1, correlator=1
  setting (1, 0) -> a=1, b=0, correlator=-1
  setting (1, 1) -> a=1, b=1, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 14: S = -2/1 (~-2.000000)
```text
Strategy 14
  setting (0, 0) -> a=1, b=1, correlator=1
  setting (0, 1) -> a=1, b=0, correlator=-1
  setting (1, 0) -> a=1, b=1, correlator=1
  setting (1, 1) -> a=1, b=0, correlator=-1
  S = (E_11 + E_10 + E_01 - E_00) = -2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Strategy 15: S = 2/1 (~2.000000)
```text
Strategy 15
  setting (0, 0) -> a=1, b=1, correlator=1
  setting (0, 1) -> a=1, b=1, correlator=1
  setting (1, 0) -> a=1, b=1, correlator=1
  setting (1, 1) -> a=1, b=1, correlator=1
  S = (E_11 + E_10 + E_01 - E_00) = 2/1
  |S| = 2/1 ≤ 2 established by direct integer arithmetic.
```
Aggregating the classical strategies into a convex combination and auditing it analytically:
```text
Convexity argument:
  min S = -2/1
  max S = 2/1
  Any convex mixture is Σ wᵢ·Sᵢ with wᵢ ≥ 0 and Σ wᵢ = 1.
  Therefore min S ≤ Σ wᵢ·Sᵢ ≤ max S, so every mixture stays within [-2, 2].
```
**Conclusion: Any classical system adhering to local realism is bounded by |S| ≤ 2.**
Mechanised coverage: the Coq lemma local_CHSH_bound lifts these pointwise checks to every convex mixture of deterministic boxes.
## Act III — Sighted Supra-Quantum Witness
A constructive Thiele witness straddles the Tsirelson boundary and the abstract Coq proof pushes through to S = 16/5.

Rational Tsirelson-approaching strategy (runtime witness):
```python
def shared_gamma():
            return 500000/707107  # derived approximation of 1/√2

        def alice(setting):
            return 1 if setting == 1 else 0

        def bob(setting):
            return 1 if setting in (0, 1) else 0

        def correlator(x, y):
            base = shared_gamma()
            return base if (x, y) != (0, 0) else -base

        def tsirelson_box(a, b, x, y):
            return Fraction(1, 4) + Fraction(1, 4) * (2 * a - 1) * (2 * b - 1) * correlator(x, y)
```
Computed CHSH value for the runtime Tsirelson approximation: 2000000/707107 (~2.828426)
Exact inequality certificate proving the runtime witness sits beneath 2√2:
```text
Tsirelson witness inequalities:
  γ = 500000/707107
  S = 4·γ = 2000000/707107
  S - 2 = 585786/707107 > 0 ⇒ S > 2.
  S² = 4000000000000/500000309449
  2√2 bound encoded as S² ≤ 8 (since S ≥ 0).
  8 - S² = 2475592/500000309449 ≥ 0 ⇒ S ≤ 2√2.
```
**This runtime measurement pins the classical/quantum boundary; every fraction is derived in integer arithmetic.**
Abstract proof excerpt (Coq sandbox) certifying the supra-quantum witness and the inequality sandwich between 2√2 and 4:
```coq
Definition pr_box_like_witness : SightedStrategy := {| e00 := q; e01 := q; e10 := q; e11 := - q |}.

Lemma pr_box_like_valid : valid_sighted pr_box_like_witness.
Proof.
  unfold valid_sighted, pr_box_like_witness; repeat split; auto using q_abs_le, q_abs_le_neg.
Qed.

Lemma chsh_pr_box_like : chsh_sighted pr_box_like_witness = 16 / 5.
Proof.
  unfold chsh_sighted, pr_box_like_witness, q; simpl; lra.
Qed.

Definition classical_limit : R := 2.
Definition tsirelson_bound : R := 2 * sqrt 2.
Definition pr_box_limit : R := 4.

Lemma tsirelson_bound_gt_classical_limit : tsirelson_bound > classical_limit.
Proof.
  unfold tsirelson_bound, classical_limit.
  apply Rmult_gt_reg_l with (r := / 2). { lra. }
  replace (2 * sqrt 2 * / 2) with (sqrt 2) by lra.
  replace (2 * / 2) with 1 by lra.
  assert (Hsq : Rsqr 1 < Rsqr (sqrt 2)).
  { replace (Rsqr 1) with 1 by (unfold Rsqr; simpl; lra).
    replace (Rsqr (sqrt 2)) with 2 by (rewrite Rsqr_sqrt; [lra | lra]).
    lra. }
  assert (Hpos1 : 0 <= 1) by lra.
  assert (Hpossqrt : 0 <= sqrt 2) by apply sqrt_pos.
  apply (Rsqr_incrst_0 1 (sqrt 2)) in Hsq; [| exact Hpos1 | exact Hpossqrt].
  lra.
Qed.

Lemma pr_box_like_value_is_supra_quantum : chsh_sighted pr_box_like_witness > tsirelson_bound.
Proof.
  rewrite chsh_pr_box_like.
  unfold tsirelson_bound.
  assert (Hsq : Rsqr (sqrt 2) < Rsqr (8 / 5)).
  { replace (Rsqr (sqrt 2)) with 2 by (rewrite Rsqr_sqrt; [lra | lra]).
    replace (Rsqr (8 / 5)) with (64 / 25) by (unfold Rsqr; simpl; lra).
    lra. }
  assert (Hpossqrt : 0 <= sqrt 2) by apply sqrt_pos.
  assert (Hpos85 : 0 <= 8 / 5) by lra.
  apply (Rsqr_incrst_0 (sqrt 2) (8 / 5)) in Hsq; [| exact Hpossqrt | exact Hpos85].
  lra.
Qed.

Theorem sighted_is_supra_quantum :
  exists s, valid_sighted s /\
            chsh_sighted s > tsirelson_bound /\
            chsh_sighted s <= pr_box_limit.
Proof.
  exists pr_box_like_witness.
  split.
  - apply pr_box_like_valid.
  - split.
    + apply pr_box_like_value_is_supra_quantum.
    + rewrite chsh_pr_box_like.
      unfold pr_box_limit.
      lra.
Qed.
```
**The machine-checked conclusion: a valid sighted strategy reaches S = 16/5, strictly greater than 2√2 yet bounded by the PR-box limit of 4.**
## Act IV — Consolidated Artifact
All evidence is collated into BELL_INEQUALITY_VERIFIED_RESULTS.md.

## Act V — Receipt Verification
Receipts are regenerated, summarised, and optionally sent to Coq for mechanised checking.

Receipt generation transcript:
```text
Wrote 5 receipts to /workspace/The-Thiele-Machine/examples/tsirelson_step_receipts.json
```
Receipt summary:
- count = 5
- instructions = PNEW, PYEXEC, PYEXEC, PYEXEC, EMIT
- signatures_verified = True
These receipts adhere to the canonical JSON schema (instruction, state, observation); Coq replay only accepts files respecting this structure.
Verification transcript:
```text
Coq proof obligations discharged (The Coq Proof Assistant, version 8.18.0).
```
**Q.E.D. — The runtime receipts coincide with the mechanised witness.**
Coq replay confirms the canonical program receipts; any alternative log must produce identical instruction/state triples to be accepted.
## Act VI — Operation Cosmic Witness
Cosmic microwave background data is converted into a formally proved prediction.

Correctness: the analytic certificate shows the induced rule outputs the logged CHSH setting for the recorded features (solvers remain optional corroboration).
Robustness: the same analytic reasoning demonstrates the prediction remains stable within the recorded noise model (ε-ball) derived from the offline dataset.
Operation Cosmic Witness mode=offline, data_source=offline, allow_network=False
Loading offline CMB sample from /workspace/The-Thiele-Machine/data/cmb_sample.csv
Extracted feature vector (mean, stdev, min, max, gradient): 2.7254761875, 6.79355163007e-06, 2.725466, 2.725489, -1.25000000004e-05
Data origin recorded as csv:cmb_sample.csv.
Induced rule: feature[2] > 2.72474 -> (1, 0), else -> (0, 1) (param_count=1)
Predicted CHSH trial: alice=1, bob=0
Analytic certificate confirms the prediction; robustness proved (eps=7.230e-05).
Persisted Operation Cosmic Witness receipts and proofs to disk.
Operation Cosmic Witness artifacts written to the artifacts/ directory for audit.
- Prediction receipt: /workspace/The-Thiele-Machine/artifacts/cosmic_witness_prediction_receipt.json
- Prediction proof: /workspace/The-Thiele-Machine/artifacts/cosmic_witness_prediction_proof.txt
- Robustness proof: /workspace/The-Thiele-Machine/artifacts/cosmic_witness_prediction_proof_robust.txt
- Prediction proved (analytic): True
## Conclusion — Verification Gates
The thesis run is accepted only when these audit checks succeed.

- All analytic certificates reproduce their recorded inequalities when re-evaluated.
- scripts/verify_truth.sh completes without error, replaying the canonical receipts inside Coq.
- artifacts/MANIFEST.sha256 matches recomputed SHA-256 hashes for ledger and receipts.
Artifact manifest persisted to artifacts/MANIFEST.sha256.
