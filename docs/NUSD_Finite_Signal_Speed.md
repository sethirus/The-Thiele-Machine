# Finite invariant signal speed from NUSD

This note describes a toy 1+1D causal lattice used to demonstrate the “physics lock”.

## Model primitives

- **State.**  A trajectory is a sequence of events \((t_k, x_k)\) with unit time increments and real
  spatial positions.
- **μ-question.**  A model proposing a maximal propagation speed \(c\) commits to a cone of radius
  \(c\) per unit time.  Encoding that commitment costs
  \(\mu_{\mathrm{question}}(c) = \log_2(1 + c^2)\) bits.
- **μ-answer.**  Given an observed trajectory, any step where \(|x_{k+1} - x_k|\) exceeds the allowed
  distance \(c (t_{k+1} - t_k)\) incurs a quadratic penalty.  Aggregating those penalties yields
  \[
  \mu_{\mathrm{answer}}(c) = \log_2\!\left(1 + \sum_k \max(0, |x_{k+1} - x_k| - c)^2\right).
  \]

The total ledger is \(\mu_{\mathrm{total}}(c) = \mu_{\mathrm{question}}(c) + \mu_{\mathrm{answer}}(c)\).

## Result

Fix an actual signal speed \(c_\star = 1\) and synthesise 32 steps of motion.  Evaluating the μ ledger
in several comoving frames (drifts \(-0.4, 0.0, 0.4\)) yields the following minima:

- Each frame is minimised at \(c = c_\star\).
- Any attempt to explain the trajectory with \(c < c_\star\) drives the μ-answer term to grow without
  bound; letting \(c \rightarrow \infty\) grows the μ-question term logarithmically.

The script `tools/analyze_signal_speed.py` prints the full table and highlights the minimiser in each
frame.  The bound is therefore frame-independent in this toy setting: a single finite \(c\) minimises
\(\mu_{\mathrm{total}}\) for all inertial observers represented by the drifts.
