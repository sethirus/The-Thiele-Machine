#!/usr/bin/env python3
"""Post-process Coq-extracted OCaml to replace Peano-recursive Nat module.

Coq's extraction generates a ``module Nat`` whose ``add``, ``mul``, ``pow``
etc. use Peano recursion under the hood (even though ``nat`` is mapped to
``int``).  For constants such as ``2^31`` (used by ReceiptIntegrity.mu_max)
this causes a stack overflow at runtime.

This script rewrites the module body with semantically-equivalent native-int
implementations that run in O(1) or O(log n) time.

Invoked automatically by ``forge_artifact.sh`` after ``coqc Extraction.v``.
"""

import re
import sys
from pathlib import Path

EFFICIENT_NAT = r'''module Nat =
 struct
  (** val pred : int -> int **)

  let pred n = Stdlib.max 0 (n - 1)

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val sub : int -> int -> int **)

  let rec sub n m = Stdlib.max 0 (n - m)

  (** val ltb : int -> int -> bool **)

  let ltb n m = n < m

  (** val pow : int -> int -> int **)

  let rec pow b e =
    if e <= 0 then 1 else b * pow b (e - 1)

  (** val divmod : int -> int -> int -> int -> int*int **)

  let rec divmod x y q u =
    if x = 0 then (q, u)
    else if u = 0 then divmod (x - 1) y (q + 1) y
    else divmod (x - 1) y q (u - 1)

  (** val modulo : int -> int -> int **)

  let modulo x y =
    if y = 0 then x else x mod y

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r =
    if k = 0 then p
    else if r = 0 then log2_iter (k - 1) (p + 1) (q + 1) q
    else log2_iter (k - 1) p (q + 1) (r - 1)

  (** val log2 : int -> int **)

  let log2 n = log2_iter (pred n) 0 1 0
 end'''

# Pattern: module Nat = struct ... end (followed by module Pos)
NAT_MODULE_RE = re.compile(
    r'module Nat =\n struct\n.*? end\n(?=\nmodule Pos)',
    re.DOTALL,
)


def patch(path: Path) -> bool:
    text = path.read_text()
    new_text, count = NAT_MODULE_RE.subn(EFFICIENT_NAT + '\n', text)
    if count == 0:
        print(f"warning: Nat module not found in {path}", file=sys.stderr)
        return False
    path.write_text(new_text)
    print(f"patched Nat module in {path} ({count} replacement(s))")
    return True


if __name__ == "__main__":
    target = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("build/thiele_core.ml")
    if not target.exists():
        print(f"error: {target} does not exist", file=sys.stderr)
        sys.exit(1)
    ok = patch(target)
    sys.exit(0 if ok else 1)
