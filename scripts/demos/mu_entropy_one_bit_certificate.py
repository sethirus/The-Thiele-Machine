"""μ/entropy tight 1-bit certificate.

This demo emits a concrete certificate for the smallest nontrivial instance:
reducing hypotheses 2 → 1 removes exactly 1 Shannon bit.

We make it *tight* by choosing an empty query string, so description_bits = 0.
Then total μ = entropy_bits = 1.

Falsifiable conditions:
- entropy_bits must equal 1
- description_bits must equal 0
- total μ must equal 1
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass

from thielecpu.mu import MuCost, calculate_mu_cost_breakdown


@dataclass(frozen=True)
class Certificate:
    ok: bool
    expr: str
    before: int
    after: int
    breakdown: dict


def main() -> None:
    print("INIT → choose instance")
    expr = ""
    before = 2
    after = 1

    print("DISCOVER → compute μ breakdown")
    breakdown: MuCost = calculate_mu_cost_breakdown(expr, before, after)

    print("CLASSIFY → check tightness")
    ok = (
        breakdown.description_bits == 0.0
        and breakdown.entropy_bits == 1.0
        and breakdown.total == 1.0
    )

    print("DECOMPOSE → description vs entropy")
    print("EXECUTE → certificate assembly")
    print("MERGE → serialize")
    print("VERIFY → emit")

    cert = Certificate(
        ok=ok,
        expr=expr,
        before=before,
        after=after,
        breakdown=asdict(breakdown),
    )

    print("SUCCESS" if cert.ok else "FAIL")
    print(json.dumps(asdict(cert), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
