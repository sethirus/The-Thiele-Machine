#!/usr/bin/env python3
"""Master Comprehensive Capability Runner.

This is imported by the pytest suite and expected to return a dict with:
- `categories`: list of dicts, each including `name`, `all_match`, and totals
- `aggregate`: includes `total_tests`, `pass_rate`, `total_mu_cost`
- `derived_conclusions`: includes `STRUCTURAL_ISOMORPHISM` and `MU_COST_TRACKING`

Implementation mirrors the archived demo runner but avoids writing output files.
"""

from __future__ import annotations

import time
from dataclasses import asdict, dataclass
from datetime import datetime
from typing import Any, Dict, List


@dataclass
class CategoryResult:
    name: str
    tests_run: int
    tests_passed: int
    all_match: bool
    total_operations_std: int
    total_operations_vm: int
    total_mu_cost: float
    execution_time: float


def run_all_capabilities() -> Dict[str, Any]:
    results: Dict[str, Any] = {
        "timestamp": datetime.now().isoformat(),
        "categories": [],
        "aggregate": {},
        "derived_conclusions": [],
    }

    categories: List[tuple[str, Dict[str, Any], float]] = []

    for name, importer in [
        ("String Manipulation", lambda: __import__("demos.comprehensive_capabilities.string_edge_cases", fromlist=["compare_and_report"]).compare_and_report()),
        ("Recursion Patterns", lambda: __import__("demos.comprehensive_capabilities.recursion_patterns", fromlist=["compare_and_report"]).compare_and_report()),
        ("Graph Algorithms", lambda: __import__("demos.comprehensive_capabilities.graph_algorithms", fromlist=["compare_and_report"]).compare_and_report()),
        ("Mathematical Edge Cases", lambda: __import__("demos.comprehensive_capabilities.mathematical_edge_cases", fromlist=["compare_and_report"]).compare_and_report()),
        ("Backtracking", lambda: __import__("demos.comprehensive_capabilities.backtracking", fromlist=["compare_and_report"]).compare_and_report()),
    ]:
        start = time.time()
        payload = importer()
        elapsed = time.time() - start
        categories.append((name, payload, elapsed))

    for name, payload, elapsed in categories:
        comparisons = payload.get("comparisons", [])
        tests_passed = sum(1 for c in comparisons if c.get("match", False))
        total_std_ops = sum(int(c.get("std_ops", 0)) for c in comparisons)
        total_vm_ops = sum(int(c.get("vm_ops", 0)) for c in comparisons)
        total_mu = float(sum(float(c.get("mu_cost", 0)) for c in comparisons))

        cat = CategoryResult(
            name=name,
            tests_run=len(comparisons),
            tests_passed=tests_passed,
            all_match=bool(payload.get("all_match", False)),
            total_operations_std=total_std_ops,
            total_operations_vm=total_vm_ops,
            total_mu_cost=total_mu,
            execution_time=elapsed,
        )
        results["categories"].append(asdict(cat))

    total_tests = sum(c["tests_run"] for c in results["categories"]) or 0
    total_passed = sum(c["tests_passed"] for c in results["categories"]) or 0
    total_std_ops = sum(c["total_operations_std"] for c in results["categories"]) or 0
    total_vm_ops = sum(c["total_operations_vm"] for c in results["categories"]) or 0
    total_mu = sum(c["total_mu_cost"] for c in results["categories"]) or 0.0
    all_categories_pass = all(c["all_match"] for c in results["categories"]) if results["categories"] else False

    results["aggregate"] = {
        "total_categories": len(results["categories"]),
        "total_tests": total_tests,
        "total_passed": total_passed,
        "pass_rate": (total_passed / total_tests) if total_tests else 0.0,
        "total_operations_std": total_std_ops,
        "total_operations_vm": total_vm_ops,
        "operations_match": total_std_ops == total_vm_ops,
        "total_mu_cost": float(total_mu),
        "all_categories_pass": all_categories_pass,
    }

    conclusions = []
    if results["aggregate"]["pass_rate"] == 1.0:
        conclusions.append(
            {
                "type": "STRUCTURAL_ISOMORPHISM",
                "statement": "Standard Python and Thiele VM produce identical results for all test cases",
                "evidence": f"{total_passed}/{total_tests} tests passed (100%)",
                "falsifiable": True,
                "supported": True,
            }
        )
    else:
        conclusions.append(
            {
                "type": "STRUCTURAL_ISOMORPHISM",
                "statement": "Isomorphism failures detected",
                "evidence": f"{total_passed}/{total_tests} tests passed ({100*results['aggregate']['pass_rate']:.1f}%)",
                "falsifiable": True,
                "supported": False,
            }
        )

    if results["aggregate"]["total_mu_cost"] > 0:
        conclusions.append(
            {
                "type": "MU_COST_TRACKING",
                "statement": "Thiele VM successfully tracks μ-cost for all operations",
                "evidence": f"Total μ-cost tracked: {results['aggregate']['total_mu_cost']:.2f} bits across {total_tests} tests",
                "falsifiable": True,
                "supported": True,
            }
        )

    results["derived_conclusions"] = conclusions
    return results


if __name__ == "__main__":
    # For manual execution
    _ = run_all_capabilities()
