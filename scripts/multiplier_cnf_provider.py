"""Lazy CNF provider for multiplier circuits.

This module refactors the previous CNF generator into a provider that
generates clauses on demand.  Rather than emitting a DIMACS file, the
``CnfProvider`` exposes an interface for retrieving the clauses that
define any variable of the multiplier circuit.  This allows a solver to
explore the circuit structure incrementally without ever materialising
the full CNF in memory or on disk.

The implementation still uses simple ripple-carry reduction built from
half and full adders.  Columns of the partial-product matrix are
generated lazily as individual output bits are requested.

The provider indexes clauses by the variables that appear in them so a
solver can fetch all clauses relevant to a particular variable using
``clauses_for_var``.
"""

from collections import defaultdict
from typing import Dict, List, Tuple

# The target composite (example-250)
TARGET_COMPOSITE_250_N = int(
    "214032465024074496126442307283933356300861471514475501779775492088141802344714013664334551909580467961099285187247091458768"
    "7396261921557363047454770520805119056493106687691590019759405693457452230589325976697471681738069364894699871578494975937497937"
)


Clause = List[int]


class CnfProvider:
    """Provide CNF clauses for a multiplier circuit on demand."""

    def __init__(self, bit_width: int = 415, N: int = TARGET_COMPOSITE_250_N) -> None:
        self.bit_width = bit_width
        self.N = N
        self.var_counter = 0

        # Index of clauses by variable
        self._clauses: Dict[int, List[Clause]] = defaultdict(list)

        # Bit variables for the two factors
        self.p_bits = [self.new_var() for _ in range(bit_width)]
        self.q_bits = [self.new_var() for _ in range(bit_width)]

        # Lazily generated structures
        self._partial_products: Dict[Tuple[int, int], int] = {}
        self._carry: List[int] = []
        self._product_bits: List[int] = []

        # Binary string of target number for output constraints
        self._n_bin = bin(self.N)[2:]

    # ------------------------------------------------------------------
    # Basic helpers
    def new_var(self) -> int:
        self.var_counter += 1
        return self.var_counter

    def add_clause(self, clause: Clause) -> None:
        for lit in clause:
            self._clauses[abs(lit)].append(clause)

    # Gate encodings ----------------------------------------------------
    def add_and_gate(self, a: int, b: int, out: int) -> None:
        self.add_clause([-a, -b, out])
        self.add_clause([a, -out])
        self.add_clause([b, -out])

    def add_xor_gate(self, a: int, b: int, out: int) -> None:
        self.add_clause([-a, -b, -out])
        self.add_clause([a, b, -out])
        self.add_clause([a, -b, out])
        self.add_clause([-a, b, out])

    def add_half_adder(self, a: int, b: int) -> Tuple[int, int]:
        s = self.new_var()
        cout = self.new_var()
        self.add_xor_gate(a, b, s)
        self.add_and_gate(a, b, cout)
        return s, cout

    def add_full_adder(self, a: int, b: int, cin: int) -> Tuple[int, int]:
        axb = self.new_var()
        self.add_xor_gate(a, b, axb)
        s = self.new_var()
        self.add_xor_gate(axb, cin, s)

        a_and_b = self.new_var()
        self.add_and_gate(a, b, a_and_b)
        cin_and_axb = self.new_var()
        self.add_and_gate(cin, axb, cin_and_axb)
        cout = self.new_var()
        self.add_clause([-a_and_b, cout])
        self.add_clause([-cin_and_axb, cout])
        self.add_clause([a_and_b, cin_and_axb, -cout])
        return s, cout

    # Column reduction --------------------------------------------------
    def _reduce_column(self, bits: List[int]) -> Tuple[int, List[int]]:
        carries: List[int] = []
        while len(bits) > 1:
            if len(bits) >= 3:
                a = bits.pop()
                b = bits.pop()
                c = bits.pop()
                s, cout = self.add_full_adder(a, b, c)
                bits.append(s)
                carries.append(cout)
            else:
                a = bits.pop()
                b = bits.pop()
                s, cout = self.add_half_adder(a, b)
                bits.append(s)
                carries.append(cout)
        return bits[0], carries

    # Partial products --------------------------------------------------
    def _pp(self, i: int, j: int) -> int:
        key = (i, j)
        if key not in self._partial_products:
            var = self.new_var()
            self.add_and_gate(self.p_bits[i], self.q_bits[j], var)
            self._partial_products[key] = var
        return self._partial_products[key]

    # Output bit management --------------------------------------------
    def _ensure_column(self, k: int) -> None:
        while len(self._product_bits) <= k:
            idx = len(self._product_bits)
            column_bits: List[int] = []
            if idx < 2 * self.bit_width - 1:
                for i in range(self.bit_width):
                    j = idx - i
                    if 0 <= j < self.bit_width:
                        column_bits.append(self._pp(i, j))
            column_bits.extend(self._carry)
            if not column_bits:
                # No bits remain; output is constant 0
                v = self.new_var()
                self.add_clause([-v])
                self._product_bits.append(v)
                continue
            sum_bit, self._carry = self._reduce_column(column_bits)
            self._product_bits.append(sum_bit)

            # Apply output constraint for bit idx
            bit = self._n_bit(idx)
            if bit == '1':
                self.add_clause([sum_bit])
            else:
                self.add_clause([-sum_bit])

    def _n_bit(self, idx: int) -> str:
        n_len = len(self._n_bin)
        if idx < n_len:
            return self._n_bin[n_len - 1 - idx]
        return '0'

    # Public API --------------------------------------------------------
    def output_var(self, idx: int) -> int:
        self._ensure_column(idx)
        return self._product_bits[idx]

    def output_count(self) -> int:
        # Maximum possible product bits for multiplication
        return 2 * self.bit_width

    def clauses_for_var(self, var: int) -> List[Clause]:
        return list(self._clauses.get(var, []))

    # Utility -----------------------------------------------------------
    @staticmethod
    def decode_bits(bits: List[int], model: List[int]) -> int:
        pos = {v for v in model if v > 0}
        out = 0
        for i, v in enumerate(bits):
            if v in pos:
                out |= (1 << i)
        return out


__all__ = ["CnfProvider", "TARGET_COMPOSITE_250_N"]

