#!/usr/bin/env python3
"""Enhanced Inquisitor: Comprehensive Coq proof audit with advanced analytics.

This wrapper integrates the base Inquisitor with advanced analysis modules:
- All original Inquisitor checks (vacuity, assumptions, etc.)
- Proof complexity metrics
- Dead code detection
- Tactic anti-patterns
- Import/dependency analysis
- Naming conventions
- Proof obligation tracking

Usage:
    python scripts/inquisitor_enhanced.py --strict
    python scripts/inquisitor_enhanced.py --report ENHANCED_REPORT.md
"""

import argparse
import sys
from pathlib import Path

# Import base inquisitor functions
from inquisitor import (
    Finding,
    iter_all_coq_files,
    iter_v_files,
    scan_file,
    scan_trivial_equalities,
    scan_exists_const_q,
    scan_clamps,
    scan_comment_smells,
    scan_unused_hypotheses,
    scan_definitional_invariance,
    scan_z_to_nat_boundaries,
    scan_physics_analogy_contract,
    write_report,
    _file_vacuity_summary,
    _assumption_audit,
    _paper_symbol_map,
    _scan_symmetry_contracts,
    _parse_optional_v_files,
    ALLOWLIST_EXACT_FILES,
)

# Import advanced analysis functions
from inquisitor_advanced import (
    scan_proof_complexity,
    scan_dead_definitions,
    scan_tactic_antipatterns,
    scan_import_analysis,
    scan_naming_conventions,
    scan_proof_obligations,
)


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description="Enhanced Inquisitor with advanced analytics")
    ap.add_argument("--coq-root", action="append", default=["coq"], help="Root directory to scan")
    ap.add_argument("--report", default="ENHANCED_INQUISITOR_REPORT.md", help="Markdown report path")
    ap.add_argument(
        "--strict",
        action="store_true",
        default=False,
        help="Fail on any HIGH finding outside allowlisted paths.",
    )
    ap.add_argument(
        "--all-proofs",
        action="store_true",
        default=True,
        help="Scan every Coq proof file in the repo (default: enabled).",
    )
    ap.add_argument(
        "--only-coq-roots",
        dest="all_proofs",
        action="store_false",
        help="Restrict scanning to --coq-root entries only.",
    )
    ap.add_argument(
        "--enable-advanced",
        action="store_true",
        default=True,
        help="Enable advanced analysis (complexity, dead code, etc.). Default: enabled.",
    )
    ap.add_argument(
        "--max-proof-lines",
        type=int,
        default=100,
        help="Maximum proof length before flagging (default: 100).",
    )
    ap.add_argument(
        "--max-tactics",
        type=int,
        default=50,
        help="Maximum tactic count before flagging (default: 50).",
    )
    args = ap.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[1]
    coq_roots = [(repo_root / root).resolve() for root in args.coq_root]
    report_path = (repo_root / args.report).resolve()

    print("=" * 80)
    print("ENHANCED INQUISITOR - Comprehensive Coq Proof Audit")
    print("=" * 80)
    print(f"Scanning: {', '.join(str(r) for r in coq_roots)}")
    print(f"Advanced analysis: {'ENABLED' if args.enable_advanced else 'DISABLED'}")
    print(f"Report output: {report_path}")
    print("=" * 80)
    print()

    all_findings: list[Finding] = []
    vacuity_index: list[tuple[int, Path, tuple[str, ...]]] = []
    scanned = 0

    if args.all_proofs:
        v_files = list(iter_all_coq_files(repo_root))
        scanned_scope = "repo"
    else:
        v_files = [vf for root in coq_roots for vf in iter_v_files(root)]
        scanned_scope = ", ".join(root.as_posix() for root in coq_roots)

    print(f"Found {len(v_files)} Coq files to scan")
    print()

    for idx, vf in enumerate(v_files, 1):
        if idx % 10 == 0:
            print(f"Progress: {idx}/{len(v_files)} files scanned...")

        scanned += 1
        try:
            # Base Inquisitor scans
            all_findings.extend(scan_file(vf))
            all_findings.extend(scan_trivial_equalities(vf))
            all_findings.extend(scan_exists_const_q(vf))
            all_findings.extend(scan_clamps(vf))
            all_findings.extend(scan_comment_smells(vf))
            all_findings.extend(scan_unused_hypotheses(vf))
            all_findings.extend(scan_definitional_invariance(vf))
            all_findings.extend(scan_z_to_nat_boundaries(vf))
            all_findings.extend(scan_physics_analogy_contract(vf))

            # Advanced scans
            if args.enable_advanced:
                all_findings.extend(scan_proof_complexity(
                    vf,
                    max_proof_lines=args.max_proof_lines,
                    max_tactics=args.max_tactics
                ))
                all_findings.extend(scan_tactic_antipatterns(vf))
                all_findings.extend(scan_import_analysis(vf))
                all_findings.extend(scan_naming_conventions(vf))
                all_findings.extend(scan_proof_obligations(vf))

                # Dead code detection (expensive, so run selectively)
                if idx % 5 == 0 or len(v_files) < 50:
                    all_findings.extend(scan_dead_definitions(vf, repo_root))

            # Vacuity scoring
            score, tags = _file_vacuity_summary(vf)
            if score > 0:
                vacuity_index.append((score, vf, tags))

        except Exception as e:
            all_findings.append(
                Finding(
                    rule_id="INTERNAL_ERROR",
                    severity="HIGH",
                    file=vf,
                    line=1,
                    snippet="",
                    message=f"Enhanced Inquisitor crashed scanning this file: {e}",
                )
            )

    print()
    print(f"Scan complete: {scanned} files analyzed")
    print()

    # Generate report
    write_report(
        report_path,
        repo_root,
        all_findings,
        scanned,
        vacuity_index,
        scanned_scope=scanned_scope,
    )

    # Summary stats
    by_severity = {"HIGH": 0, "MEDIUM": 0, "LOW": 0}
    for f in all_findings:
        by_severity[f.severity] = by_severity.get(f.severity, 0) + 1

    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total findings: {len(all_findings)}")
    print(f"  HIGH:   {by_severity['HIGH']}")
    print(f"  MEDIUM: {by_severity['MEDIUM']}")
    print(f"  LOW:    {by_severity['LOW']}")
    print()
    print(f"Files with vacuity indicators: {len(vacuity_index)}")
    print()

    if vacuity_index:
        print("Top 10 most vacuous files:")
        for score, path, tags in sorted(vacuity_index, key=lambda t: -t[0])[:10]:
            try:
                rel = path.relative_to(repo_root)
            except:
                rel = path
            print(f"  {score:3d} | {', '.join(tags):30s} | {rel}")
        print()

    # Fail policy
    if args.strict:
        high_findings = [f for f in all_findings if f.severity == "HIGH"]
        if high_findings:
            print("=" * 80)
            print(f"FAIL (--strict): {len(high_findings)} HIGH findings detected")
            print("=" * 80)
            print(f"Report: {report_path}")
            return 1

    print("=" * 80)
    print("ENHANCED INQUISITOR: PASS")
    print(f"Report: {report_path}")
    print("=" * 80)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
