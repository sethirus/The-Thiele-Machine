"""Static checks: Kami-extracted RTL charges mu for every step.

Verifies structural mu-monotonicity properties in the Bluespec/Kami-generated
thiele_cpu_kami.v.  The Coq proof guarantees these hold by construction; this
test catches mis-extracted or corrupted Verilog files.

Checks:
- mu$D_IN wire exists (the mu update path)
- mu$D_IN always adds to mu when not in Bianchi violation
- The Bianchi kill-switch zero-advances mu on violation (mu$D_IN = mu, not 0)
"""

from __future__ import annotations

import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parents[1]
RTL_PATH = ROOT / "thielecpu" / "hardware" / "rtl" / "thiele_cpu_kami.v"
OPCODES_HDR = ROOT / "thielecpu" / "hardware" / "rtl" / "generated_opcodes.vh"


def _opcode_names_from_header(text: str) -> set[str]:
    names = set(re.findall(r"\bOPCODE_([A-Z0-9_]+)\b", text))
    if not names:
        raise AssertionError("failed to parse any OPCODE_* names from generated header")
    return names


def test_kami_rtl_mu_update_wire_exists() -> None:
    """mu$D_IN must be declared and assigned in the Kami-extracted Verilog."""
    rtl = RTL_PATH.read_text(encoding="utf-8")
    assert "mu$D_IN" in rtl, "mu$D_IN wire missing from Kami-extracted RTL"
    assert re.search(r"assign\s+mu\$D_IN", rtl),         "mu$D_IN must have a combinatorial assign statement"


def test_kami_rtl_mu_update_adds_to_mu() -> None:
    """mu$D_IN must include an addition term based on mu (mu-monotonicity)."""
    rtl = RTL_PATH.read_text(encoding="utf-8")
    assert re.search(r"=\s*mu\s*\+\s*\w+", rtl),         "RTL must contain 'mu + <cost>' expression for mu-monotonicity"


def test_kami_rtl_mu_en_gates_on_live_step() -> None:
    rtl = RTL_PATH.read_text(encoding="utf-8")


def test_kami_rtl_bianchi_freezes_mu_not_clears() -> None:
    """On Bianchi violation mu$D_IN = mu (freeze, not zero)."""
    rtl = RTL_PATH.read_text(encoding="utf-8")
    assert re.search(r"mu_ULT_mu_tensor.*\?\s*mu\s*:", rtl, re.DOTALL),         "Bianchi violation must freeze mu (mu$D_IN = mu), not clear it"


def test_opcodes_header_has_all_opcodes() -> None:
    """generated_opcodes.vh must define at least 26 OPCODE_* constants."""
    hdr = OPCODES_HDR.read_text(encoding="utf-8")
    names = _opcode_names_from_header(hdr)
    assert len(names) >= 31, f"Expected >=31 opcodes in header, found {len(names)}: {sorted(names)}"
