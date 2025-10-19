# μ-spec v2.0

## Purpose

This specification defines the canonical measurement of μ-bit expenditure for any
reasoning step executed by the Thiele Machine tooling.  The μ-bit is treated as
an information-theoretic quantity derived from the description length of the
question being posed and the information gain delivered by the answer.  All
software components that account for μ-costs MUST implement this document.

## Definitions

### Canonical S-expression encoding

* Every question or claim is represented as an S-expression whose lexemes are
  parentheses or atoms separated by whitespace.
* The canonical form is obtained by tokenising the input expression into
  parentheses and atoms and re-serialising them with a single ASCII space (`0x20`)
  between tokens.
* The byte-length of the canonical encoding, multiplied by eight, is the bit
  length attributed to the description.  This is denoted `μ_question`.

Formally, for a question `q`:

```
μ_question(q) = 8 × |canon(q)|
```

where `canon(q)` is the canonical byte string.

### Possibility spaces

Let `Ω_before` be the finite set of outcomes consistent with the state of
knowledge immediately before a reasoning step, and let `Ω_after ⊆ Ω_before` be
those outcomes that remain consistent after the step concludes.

* `N = |Ω_before|` is the initial possibility count.
* `M = |Ω_after|` is the remaining possibility count.
* Both counts MUST be strictly positive integers with `M ≤ N`.

### Information gain

The information gain of a reasoning step is the Shannon information conveyed by
the answer:

```
μ_answer = log₂(N / M)
```

If `N = M`, the information gain is zero.  When a reasoning step splits into a
sequence of mutually exclusive questions (for example, testing each colour of a
node separately) the caller MUST aggregate the gains of each sub-question.

### Total μ-cost

For any reasoning step described by `(q, N, M)` the total μ-cost is

```
μ_total(q, N, M) = μ_question(q) + μ_answer(N, M)
```

μ-costs are additive: the μ-cost of a sequence of independent reasoning steps is
the sum of the component μ-costs.

### Numeric domain

* `μ_question` is an integer number of bits.
* `μ_answer` and `μ_total` MAY be non-integer real values.  Implementations that
  require exact arithmetic SHOULD represent the ratio `N/M` as a rational number
  and track the logarithm symbolically until a numeric approximation is needed.

## Implementation guidance

1. **Canonical encoding** – Tokenise the input string by splitting on
   parentheses and ASCII whitespace.  Re-emit tokens joined by single spaces to
   obtain the canonical encoding.
2. **Information gain** – Use the integer possibility counts that are natural to
   the domain.  For graph colouring, a query about a node that can take one of
   three colours before propagation and one colour afterwards has `N = 3` and
   `M = 1`.
3. **Aggregation** – When a reasoning routine makes several sub-queries in one
   logical action, compute the μ-cost of each sub-query separately and sum the
   results.  Reporting tooling SHOULD emit both the per-step breakdown and the
   accumulated total.

## Conformance requirements

* `scripts/calculate_mu_cost.py` SHALL be treated as the reference calculator
  for μ-spec v2.0.
* The Python VM (`thielecpu/vm.py`), the graph-colouring laboratory, and the
  Coq microcosms MUST delegate to the shared μ-cost logic so that all artefacts
  compute identical totals for a given reasoning transcript.
* Reports MUST state whether numbers are exact or rounded.  Rounding SHOULD only
  occur for presentation purposes.

## Change management

This specification supersedes all prior μ-bit definitions.  Any future revisions
MUST update the version number and document deltas relative to μ-spec v2.0.
