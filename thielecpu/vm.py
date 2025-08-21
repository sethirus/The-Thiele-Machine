"""Virtual machine execution loop."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
from typing import List

from .assemble import Instruction
from .logic import lassert
from .mdl import mdlacc
from .state import State
from .isa import CSR
from ._types import LedgerEntry


@dataclass
class VM:
    state: State

    def run(self, program: List[Instruction], outdir: Path) -> None:
        outdir.mkdir(parents=True, exist_ok=True)
        trace_lines: List[str] = []
        ledger: List[LedgerEntry] = []
        cert_dir = outdir / "certs"
        module = self.state.pnew({1})
        step = 0
        for op, arg in program:
            step += 1
            if op == "LASSERT":
                formula = Path(arg).read_text()
                digest = lassert(self.state, module, formula, cert_dir)
                trace_lines.append(f"{step}: LASSERT {arg} -> {digest}")
            else:
                raise ValueError(f"unknown opcode {op}")
        mdlacc(self.state, module, consistent=self.state.csr[CSR.ERR] == 0)
        ledger.append(
            {
                "step": step + 1,
                "delta_mu": 0,
                "total_mu": self.state.mu,
                "reason": "final",
            }
        )
        (outdir / "trace.log").write_text("\n".join(trace_lines))
        (outdir / "mu_ledger.json").write_text(json.dumps(ledger))
        summary = {"mu": self.state.mu, "cert": self.state.csr[CSR.CERT_ADDR]}
        (outdir / "summary.json").write_text(json.dumps(summary))


__all__ = ["VM"]
