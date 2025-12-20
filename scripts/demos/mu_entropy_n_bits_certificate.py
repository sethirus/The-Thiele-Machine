"""μ/entropy tight N-bit certificate table.

For n=1..N:
  before = 2^n, after = 1
  entropy_bits must equal n
  choosing empty expr makes description_bits = 0 so total μ = n (tight).

This is the executable-side companion to the Coq table deliverable.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass

from thielecpu.mu import calculate_mu_cost_breakdown


@dataclass(frozen=True)
class Row:
    n: int
    before: int
    after: int
    ok: bool
    description_bits: float
    entropy_bits: float
    total: float


def main() -> None:
    print("INIT → choose table")
    max_n = 16
    expr = ""

    print("DISCOVER → compute μ table")
    rows: list[Row] = []
    for n in range(1, max_n + 1):
        before = 1 << n
        after = 1
        bd = calculate_mu_cost_breakdown(expr, before, after)
        ok = bd.description_bits == 0.0 and bd.entropy_bits == float(n) and bd.total == float(n)
        rows.append(
            Row(
                n=n,
                before=before,
                after=after,
                ok=ok,
                description_bits=bd.description_bits,
                entropy_bits=bd.entropy_bits,
                total=bd.total,
            )
        )

    print("VERIFY → summarize")
    all_ok = all(r.ok for r in rows)

    print("SUCCESS" if all_ok else "FAIL")
    payload = {
        "expr": expr,
        "max_n": max_n,
        "ok": all_ok,
        "rows": [asdict(r) for r in rows],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
