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

# The target number (RSA-250)
RSA_250_N = int(
    "214032465024074496126442307283933356300861471514475501779775492088141802344714013664334551909580467961099285187247091458768"
    "7396261921557363047454770520805119056493106687691590019759405693457452230589325976697471681738069364894699871578494975937497937"
)


Clause = List[int]


class CnfProvider:
    """Provide CNF clauses for a multiplier circuit on demand."""

    def __init__(self, bit_width: int = 415, N: int = RSA_250_N) -> None:
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
        # Track which partial products have been fully defined with clauses
        self._pp_defined: Dict[Tuple[int, int], bool] = {}
        # Carries entering each column (index -> list of vars)
        self._carry_map: Dict[int, List[int]] = defaultdict(list)
        # Output bits (column index -> var)
        self._product_bits: Dict[int, int] = {}

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
            # Create placeholder; definition added when first requested again
            self._partial_products[key] = var
            self._pp_defined[key] = False
        if not self._pp_defined[key]:
            self.add_and_gate(self.p_bits[i], self.q_bits[j], self._partial_products[key])
            self._pp_defined[key] = True
        return self._partial_products[key]

    # Output bit management --------------------------------------------
    def _link_vars(self, a: int, b: int) -> None:
        """Assert a <=> b."""
        self.add_clause([-a, b])
        self.add_clause([a, -b])

    def _define_output_var(self, idx: int) -> None:
        if idx in self._product_bits:
            return

        column_bits: List[int] = []
        if idx < 2 * self.bit_width - 1:
            for i in range(self.bit_width):
                j = idx - i
                if 0 <= j < self.bit_width:
                    column_bits.append(self._pp(i, j))

        carries_in = self._carry_map.get(idx)
        if carries_in:
            column_bits.extend(carries_in)
        elif idx > 0:
            # create placeholder carry if requested from top without source
            placeholder = self.new_var()
            self._carry_map[idx] = [placeholder]
            column_bits.append(placeholder)

        if not column_bits:
            v = self.new_var()
            self.add_clause([-v])
            self._product_bits[idx] = v
            self._carry_map[idx + 1] = []
        else:
            sum_bit, carries = self._reduce_column(column_bits)

            existing = self._carry_map.get(idx + 1)
            if existing:
                for produced, old in zip(carries, existing):
                    self._link_vars(produced, old)
                if len(carries) > len(existing):
                    self._carry_map[idx + 1] = existing + carries[len(existing):]
            else:
                self._carry_map[idx + 1] = carries

            self._product_bits[idx] = sum_bit

        # Apply output constraint for bit idx
        bit = self._n_bit(idx)
        if bit == '1':
            self.add_clause([self._product_bits[idx]])
        else:
            self.add_clause([-self._product_bits[idx]])

    def _n_bit(self, idx: int) -> str:
        n_len = len(self._n_bin)
        if idx < n_len:
            return self._n_bin[n_len - 1 - idx]
        return '0'

    # Public API --------------------------------------------------------
    def output_var(self, idx: int) -> int:
        self._define_output_var(idx)
        return self._product_bits[idx]

    def output_count(self) -> int:
        # Use the actual bit length of N, not the maximum possible
        return len(self._n_bin)

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


__all__ = ["CnfProvider", "RSA_250_N"]

