"""A Python realisation of the small Thiele machine, its multi-register host
and the universal program U, written directly from the Coq definitions.

Every function's docstring names the Coq definition it mirrors. The Coq
files are minimal/EarnedCore.v, minimal/EarnedGeneric.v,
minimal/EarnedMulti.v, minimal/EarnedMultiPriced.v,
minimal/EarnedPriced.v, minimal/UniversalCodes.v and the Universal*.v files
of coq/kernel/foundation/.

Natural numbers are Python integers and are never truncated: the Coq
definitions use unbounded nat, so the codes of the universal program (which
are powers of two) must not wrap.

Programs and states are plain data. A program is a list of instruction
tuples (see small.py and multi.py). Nothing here is copied from the Coq
source by hand except the definitions themselves; the program U and the
register layout are printed by Coq (scripts/realize_tables.py) into
thiele_small/data/ and checked against the Python constants by
tests/test_realize.py.
"""
