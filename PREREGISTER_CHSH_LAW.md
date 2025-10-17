# CHSH ↔ µ-bits Physical Law: Pre-registration Protocol

**Pre-registration Date:** October 16, 2025  
**Protocol Version:** 1.0  
**Lead Researcher:** Devon Thiele  
**Repository:** https://github.com/sethirus/The-Thiele-Machine  

## Research Question

Does nonclassical correlation strength (measured by CHSH violation S > 2) impose a quantifiable computational information cost (µ-bits) to maintain local realism?

## Hypothesis

There exists a device-independent function μ*(S) that maps observed CHSH violation strength to the minimal µ-bits required to eliminate all local-realist partitions without contradiction.

## Experimental Design

### Independent Variable
- CHSH violation strength S, measured from Bell experiment datasets
- Range: S ∈ [1.8, 4.0] (classical bound to PR-box maximum)

### Dependent Variable
- μ*(S): Minimal µ-bits required to restore local consistency
- Measured using Thiele Machine partition-native computation

### Method
1. Generate/collect Bell experiment datasets with varying CHSH violations
2. For each dataset, use Thiele Machine to compute μ*(S) - the minimal information cost to eliminate local-realist explanations
3. Fit the μ*(S) curve and generate cryptographic receipts
4. Publish curve with device-independent verification protocol

### Success Criteria
- **Primary:** μ*(S) = 0 for S ≤ 2 (local realism holds), μ*(S) > 0 for S > 2 (nonclassical correlations have computational cost)
- **Secondary:** μ*(S) increases monotonically with violation strength
- **Tertiary:** Curve fits existing Bell datasets and predicts new experiments

### Analysis Plan
- Fit piecewise function: μ*(S) = 0 for S ≤ 2, μ*(S) = f(S) for S > 2
- Generate receipts for each data point with cryptographic verification
- Provide one-command verification: `python verify_chsh_law.py <dataset>`

### Data Collection
- Synthetic datasets using existing Bell boxes (PR-box, Tsirelson approximation)
- Real experimental datasets (when available from collaborating labs)
- All datasets timestamped and SHA-256 hashed in receipts

### Reproducibility
- Docker container: `thielephysics/chsh-mu-bits-law:v1.0`
- One-liner verification: `docker run --rm -v $(pwd):/data thielephysics/chsh-mu-bits-law:v1.0 verify /data/dataset.json`
- All code and data in public repository with frozen dependencies

### Statistical Power
- Minimum 8 data points spanning S ∈ [1.8, 4.0]
- Each data point computed with ≥1000 trials for statistical significance
- Receipts provide cryptographic proof of computation integrity

### Exclusion Criteria
- Datasets with S < 1.8 (below meaningful classical range)
- Datasets with insufficient trials (<1000) for statistical significance
- Computation failures (Thiele VM crashes, invalid receipts)

### Timeline
- **Phase 1 (Complete):** Core implementation and synthetic data validation
- **Phase 2 (Current):** Real dataset collection and curve fitting
- **Phase 3 (Next):** Lab verification and publication

### Verification by Third Parties
Any researcher can:
1. Clone the repository
2. Run `python demos/chsh_mu_bits_law.py` to reproduce synthetic results
3. Use their own Bell datasets with `python scripts/verify_chsh_law.py <dataset>`
4. Verify receipts with `python scripts/verify_receipt.py chsh_mu_bits_law_receipt.json`

### Ethical Considerations
- No human subjects involved
- Research advances fundamental physics understanding
- Open-source implementation ensures accessibility
- No dual-use concerns (pure physics research)

### Funding and Conflicts
- Self-funded research
- No conflicts of interest
- All code and data publicly available

### Protocol Amendments
Any changes to this protocol will be documented with justification and timestamped.

---

**Pre-registration Signature:**  
SHA-256: `5c7f61e7ec8abecd86c22f1b377fbcd1b7d0ef47a85fb292983e859b08b1b003`  
Timestamp: October 16, 2025 11:37 UTC  
Lead Researcher: Devon Thiele