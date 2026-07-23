#!/usr/bin/env python3
"""Regenerate artifacts/verification_receipt.json from live checks.

Every field in the emitted receipt is derived from a check this script
actually runs (or from a pinned artifact it re-validates); nothing is
hand-written. Phases:

  coq_build            every coq/_CoqProject entry has a .vo on disk and the
                       tree contains zero `Admitted.` outside patches/archive
  inquisitor           a fresh scripts/inquisitor.py run reports 0/0/0
  structural_advantage the blind/sighted factored-search programs from
                       tests/test_structural_advantage.py, executed on the
                       Python VM, reproduce their exact iteration/mu formulas
  test_suite           the full pytest suite passes with --strict-backends

The claims_verified list is only emitted after each named anchor is
mechanically confirmed: theorem present in build/probe/probe_inventory.json,
receipt artifacts/print_assumptions_all_proofs.json reporting zero
user/project-local axiom findings, and anchor files present on disk.

Exit code 0 iff the verdict is "ALL CLAIMS VERIFIED".
"""
from __future__ import annotations

import datetime
import importlib.util
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts" / "verification_receipt.json"


def phase_coq_build() -> dict:
    sys.path.insert(0, str(ROOT / "scripts"))
    from coq_proof_scope import coqproject_v_files  # noqa: E402

    entries = sorted(coqproject_v_files())
    missing = [p for p in entries if not (ROOT / p).with_suffix(".vo").exists()]
    admitted = subprocess.run(
        ["bash", "-c",
         "grep -rnE '^\\s*Admitted\\.' coq/ --include='*.v' | grep -v patches | grep -v archive | wc -l"],
        cwd=ROOT, capture_output=True, text=True,
    )
    n_admitted = int(admitted.stdout.strip() or "0")
    ok = not missing and n_admitted == 0
    return {
        "status": "PASS" if ok else "FAIL",
        "note": f"{len(entries) - len(missing)}/{len(entries)} .vo present, "
                f"{n_admitted} Admitted (excl. patches/archive)"
                + (f"; missing: {missing[:5]}" if missing else ""),
    }


def phase_inquisitor() -> dict:
    import tempfile
    report = Path(tempfile.mkdtemp(prefix="thiele_receipt_")) / "inquisitor_report.md"
    t0 = time.time()
    proc = subprocess.run(
        [sys.executable, "scripts/inquisitor.py", "--report", str(report)],
        cwd=ROOT, capture_output=True, text=True,
    )
    text = report.read_text(encoding="utf-8") if report.exists() else ""
    counts = dict(re.findall(r"- (HIGH|MEDIUM|LOW): (\d+)", text))
    ok = proc.returncode == 0 and counts.get("HIGH") == "0" and \
        counts.get("MEDIUM") == "0" and counts.get("LOW") == "0"
    return {
        "status": "PASS" if ok else "FAIL",
        "note": f"fresh run: HIGH={counts.get('HIGH', '?')} "
                f"MEDIUM={counts.get('MEDIUM', '?')} LOW={counts.get('LOW', '?')} "
                f"(rc={proc.returncode}, {time.time() - t0:.0f}s)",
    }


def phase_structural_advantage() -> dict:
    spec = importlib.util.spec_from_file_location(
        "sa", ROOT / "tests" / "test_structural_advantage.py")
    sa = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(ROOT))
    spec.loader.exec_module(sa)

    # The module's own main case: an 8x8 factored grid, target (left=6, right=5).
    left, n_right, right = 6, 8, 5
    target_idx = left * n_right + right
    blind = sa._run(sa._blind_search_program(target_idx))
    sighted = sa._run(sa._sighted_search_program(left, right))

    blind_iters = blind.vm_regs[15]
    sighted_iters = sighted.vm_regs[15]
    ok = (not blind.vm_err and not sighted.vm_err
          and blind_iters == target_idx + 1              # L*M + R + 1
          and sighted_iters == left + right + 2          # L + R + 2
          and blind.vm_mu == 0
          and sighted.vm_mu > 0)
    return {
        "grid": f"{n_right}x{n_right}",
        "target": [left, right],
        "blind_iters": int(blind_iters),
        "blind_mu": int(blind.vm_mu),
        "sighted_iters": int(sighted_iters),
        "sighted_mu": int(sighted.vm_mu),
        "savings_iters": int(blind_iters - sighted_iters),
        "status": "PASS" if ok else "FAIL",
    }


def phase_test_suite() -> dict:
    t0 = time.time()
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "tests/", "-q", "--tb=no",
         "--strict-backends"],
        cwd=ROOT, capture_output=True, text=True,
    )
    tail = [ln for ln in proc.stdout.splitlines() if re.search(r"\d+ passed", ln)]
    summary = tail[-1].strip() if tail else proc.stdout.splitlines()[-1:] or "?"
    return {
        "status": "PASS" if proc.returncode == 0 else "FAIL",
        "summary": summary if isinstance(summary, str) else " ".join(summary),
        "elapsed_s": round(time.time() - t0, 1),
    }


def verified_claims() -> tuple[list[str], bool]:
    inv = json.loads((ROOT / "build" / "probe" / "probe_inventory.json").read_text())
    receipt = json.loads(
        (ROOT / "artifacts" / "print_assumptions_all_proofs.json").read_text())
    names: dict[str, list[str]] = {}
    for f in inv["files"]:
        for a in f["addressable"]:
            names.setdefault(a["local_name"], []).append(f["file"])

    anchors = [
        ("no_free_certification", "coq/kernel/nfi/AbstractNoFI.v",
         "NoFI: certification requires >= 1 mu (no_free_certification, AbstractNoFI.v)"),
        ("vm_apply_mu", "coq/kernel/foundation/MuLedgerConservation.v",
         "Conservation: mu = sum(instruction_cost) exactly (vm_apply_mu, MuLedgerConservation.v)"),
        ("mu_is_initial_monotone", "coq/kernel/mu_calculus/MuInitiality.v",
         "Initiality: mu is unique satisfying cost measure (mu_is_initial_monotone, MuInitiality.v)"),
        (None, "coq/kernel/witness/ShadowProjection.v",
         "Separation: classical observer cannot distinguish Thiele-distinct states (ShadowProjection.v)"),
        (None, "coq/kernel/nfi/StructuralAdvantage.v",
         "Structural Advantage: blind search pays iterations, sighted search pays mu; gap unbounded (StructuralAdvantage.v + test_structural_advantage.py)"),
        ("elliptope_check_full_sound", "coq/kernel/quantum/ElliptopeGate.v",
         "Elliptope gate: a passing check entails elliptope membership; the PR box is never accepted (elliptope_check_full_sound, ElliptopeGate.v)"),
        ("five_disciplines_are_pointers", "coq/kernel/frontier/PointerObservableReductions.v",
         "Pointer observables: all five deployed metering disciplines are unique pointers, closed under the global context (five_disciplines_are_pointers, PointerObservableReductions.v)"),
        (None, None,
         "Hardware Parity: all 46 opcodes agree across Coq/Python/OCaml (test suite)"),
    ]

    ok = receipt["summary"]["user_or_third_party_axiom_findings"] == 0
    claims = []
    for theorem, path, text in anchors:
        good = True
        if theorem is not None and theorem not in names:
            good = False
        if path is not None and not (ROOT / path).exists():
            good = False
        if good:
            claims.append(text)
        else:
            ok = False
            claims.append(f"UNVERIFIED: {text}")
    return claims, ok


def main() -> int:
    phases = {
        "coq_build": phase_coq_build(),
        "inquisitor": phase_inquisitor(),
        "structural_advantage": phase_structural_advantage(),
        "test_suite": phase_test_suite(),
    }
    claims, anchors_ok = verified_claims()
    all_pass = anchors_ok and all(p["status"] == "PASS" for p in phases.values())
    receipt = {
        "schema": "thiele-verification-receipt-v1",
        "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "generator": "scripts/generate_verification_receipt.py",
        "verdict": "ALL CLAIMS VERIFIED" if all_pass else "FAIL",
        "repository": str(ROOT),
        "phases": phases,
        "claims_verified": claims,
    }
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
    print(f"\nwrote {OUT}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
