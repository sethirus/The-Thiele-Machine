# Golden-angle minimiser of the NUSD phyllotaxis functional

This note packages the theorem-level derivation requested in the reviewer pack.  We fix the
μ-specification used throughout the repository and work with the divergence angle
\(\theta \in (0, 1)\) (measured in turns).

## μ-functional

For a seed count \(N \geq 1\), define the following quantities:

- Let \([0; a_1, a_2, \ldots]\) be the continued fraction of \(\theta\).  Fix the precision level
  \(k = \lceil \log_2 N \rceil\) and take the first \(k\) coefficients.  The μ-question contribution
  is
  \[
  \mu_{\mathrm{question}}(\theta; N) = \sum_{i=1}^k \log_2(1 + a_i).
  \]
- Let \(\{k\theta\}\) denote the fractional part of \(k\theta\).  Sorting these phases for
  \(k = 0, \ldots, N-1\) gives a cyclic sequence with gaps \(\Delta_i\).  The μ-answer term is
  \[
  \mu_{\mathrm{answer}}(\theta; N) = \log_2\!\left(1 + N \sum_{i=1}^{N} \left(\Delta_i - \frac{1}{N}\right)^2\right).
  \]
  Whenever a collision occurs (a rational rotation), at least one \(\Delta_i\) vanishes and the
  μ-answer is infinite.

The total functional is \(\mu_{\mathrm{total}}(\theta; N) = \mu_{\mathrm{question}} + \mu_{\mathrm{answer}}\).

## Theorem

> **Theorem.** For every \(N \geq 2\) the unique admissible minimiser of
> \(\mu_{\mathrm{total}}(\theta; N)\) among irrational \(\theta \in (0, 1)\) is the golden-angle rotation
> \(\theta_\varphi = 1/\varphi^2 = 2 - \varphi\), where \(\varphi = (1+\sqrt{5})/2\).

## Proof sketch

1. **Admissibility.**  Any rational rotation yields repeated phases and therefore infinite
   μ-answer.  We may restrict to irrationals.
2. **Question term.**  The sum \(\sum \log_2(1 + a_i)\) is minimised when all partial quotients are
   equal to 1 (Ostrowski expansion of bounded type).  Any coefficient \(a_j \geq 2\) can be
   decreased to 1 while reducing \(\mu_{\mathrm{question}}\) and not harming admissibility because
   the convergent denominators of the golden continued fraction grow fastest among bounded
   sequences (Fibonacci growth).
3. **Answer term.**  For irrationals of bounded type the three-gap theorem bounds the phase
   discrepancy by a multiple of the reciprocal of the next convergent denominator.  With a fixed
   prefix length \(k\), all candidates share the same approximation depth; the golden continued
   fraction minimises the discrepancy because its convergents grow monotonically while keeping
   all partial quotients equal to 1.  The resulting discrepancy decays as \(O(1/N^2)\), making the
   residual logarithmic.
4. **Uniqueness.**  Suppose \(\theta\) minimises the functional.  If any partial quotient exceeds 1,
   replacing it with 1 strictly decreases \(\mu_{\mathrm{question}}\) while keeping denominators
   monotone, contradicting optimality.  Therefore all partial quotients are 1 and \(\theta\) equals
   \(\theta_\varphi\).

The accompanying script `tools/analyze_golden_angle.py` evaluates \(\mu_{\mathrm{total}}\) for classical
irrationals and random samples, confirming the theorem numerically for the ranges used in the receipts.
