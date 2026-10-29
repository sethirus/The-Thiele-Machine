# SPDX-FileCopyrightText: 2026 Devon Thiele
# SPDX-License-Identifier: CC-BY-SA-4.0
"""The counted runs of U: the three stepped benchmarks to the step, the
certifying guest's exact count, and the loop closed forms against stepping."""
import importlib.util
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("count_universal_run", REPO / "scripts" / "count_universal_run.py")
cur = importlib.util.module_from_spec(spec)
sys.modules["count_universal_run"] = cur
spec.loader.exec_module(cur)

Z = ("PZero",)
CHAIN = [("CHECK", Z, 0), ("COMMIT", Z, 0), ("CERTIFY",)]


def _count(P, x, y):
    n, fin, heads, problems = cur.count(P, x, y)
    assert problems == [], problems
    return n, fin


def test_benchmarks_to_the_step():
    n, fin = _count([("DEC", 0, 1), ("HALT",)], 2, 0)
    assert n == 25_953_317 and fin["ledger"] == 0 and not fin["cert"] and not fin["trap"]
    n, fin = _count([("CHECK", Z, 0)], 0, 0)
    assert n == 402_654_059 and fin["ledger"] == 1 and not fin["trap"]
    n, fin = _count([("CHECK", Z, 0)], 1, 0)
    assert n == 201_327_155 and fin["ledger"] == 1 and fin["trap"]


def test_certifying_guest_counted():
    n, fin = _count(CHAIN, 0, 0)
    assert n == 3_894_222_629_847_358_066_688_933_266_198_944
    assert fin["pc"] == 108 and fin["ledger"] == 3 and fin["cert"] and not fin["trap"] and fin["facts"] == 1
    n, fin = _count(CHAIN, 5, 0)
    assert n == 973_555_646_581_507_138_873_939_791_446_643
    assert fin["pc"] == 508 and fin["ledger"] == 1 and not fin["cert"] and fin["trap"]


def test_closed_forms_match_stepping():
    assert cur.check_loops(vmax=12) == 981


def test_plain_and_counted_agree_on_small_guests():
    for P, x, y in [([("HALT",)], 3, 4), ([("INC", 0), ("HALT",)], 0, 0), ([("INC", 0), ("INC", 1), ("HALT",)], 1, 2)]:
        a = cur.universal.hload(P, x, y)
        b = cur.universal.hload(P, x, y)
        assert cur.run_plain(a) == cur.run_counted(b)
        assert cur.full_state(a) == cur.full_state(b)
