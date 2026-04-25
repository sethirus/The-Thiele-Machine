## Structural Decomposition Certificate (THIELE-DECOMP)

When you propose a solution to any non-trivial algorithmic, search, or optimization problem
in this repository, append a `THIELE-DECOMP` block as a comment immediately after your code.

This block declares how you decomposed the problem into structurally independent parts.
A validator (`scripts/validate_copilot_cert.py`) will run your claimed decomposition through
the Thiele Machine and report whether you found the geodesic (mu-optimal) strategy or
over/under-certified.

**Format:**

```python
# THIELE-DECOMP: {
#   "problem": "brief description",
#   "dimensions": ["dim_name_1", "dim_name_2", ...],
#   "certified": ["dim_name_1", "dim_name_2"],
#   "search_size_per_dim": N,
#   "independence_claim": "why these dims are structurally independent"
# }
```

**Rules:**
- `dimensions`: all independent sub-problems you identified (2-5 is typical)
- `certified`: the subset you actually certify — certify ONLY the dims where certification
  saves steps. Do NOT certify a dimension if it saves zero steps (size = 1, or all paths
  through it are equally fast). Over-certifying is a mu waste.
- `search_size_per_dim`: the number of states you search per dimension (e.g., 4 for N=4 grid)
- `independence_claim`: your justification. The machine doesn't check this semantically —
  you own the claim. The machine checks the COST is consistent with what you claimed.

**Example — a factored search:**
```python
# THIELE-DECOMP: {
#   "problem": "find (target_x, target_y, target_z) in independent 3D grid",
#   "dimensions": ["x_axis", "y_axis", "z_axis"],
#   "certified": ["x_axis", "y_axis"],
#   "search_size_per_dim": 4,
#   "independence_claim": "x, y, z coordinates are orthogonal; finding x tells us nothing about y or z"
# }
```

**What the validator does:**
Runs your claimed decomposition and a blind baseline through the Thiele Machine, then
reports: (blind_steps, 0 mu) vs (your_steps, your_mu) vs (geodesic_steps, geodesic_mu).
If you over-certified, it says so. If you used the wrong structure, it says so.

Run after writing your THIELE-DECOMP block:
```
python3 scripts/validate_copilot_cert.py <your_file.py>
```

---

## Coq Voice Rules

When sweeping Coq comment blocks in this repository into Devon voice, preserve the full technical payload.

- Keep proof chains, algorithm steps, examples, physical interpretation, complexity notes, edge cases, caveats, and falsification hooks.
- Remove only bureaucratic scaffolding: banner walls, PART/SECTION dividers, repeated labels like WHY THIS MATTERS/THE CLAIM/THE PROOF, and duplicated helper-note spam.
- Compress scaffolding into direct prose; do not collapse substantive explanations into one-line summaries.
- Before sweeping a file, inspect existing staged sweeps such as coq/kernel/AbstractNoFI.v, coq/kernel/BornRule.v, coq/kernel/CertCheck.v, coq/kernel/Certification.v, coq/kernel/ClassicalBound.v, and coq/kernel/Closure.v, and match that pattern.
- If unsure whether text is substantive or scaffolding, keep it and rewrite it rather than deleting it.
