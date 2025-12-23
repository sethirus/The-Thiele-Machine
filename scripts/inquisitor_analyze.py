#!/usr/bin/env python3
"""Inquisitor Analysis: Generate comprehensive insights from Inquisitor reports.

This script analyzes existing Inquisitor reports and generates:
- Executive summary with key metrics
- Trend analysis across categories
- Prioritized remediation recommendations
- File-level quality scores
- Category breakdowns
"""

import argparse
import json
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple


@dataclass
class AnalysisInsight:
    category: str
    severity: str
    count: int
    description: str
    recommendation: str


def parse_inquisitor_report(report_path: Path) -> Dict:
    """Parse an Inquisitor markdown report and extract structured data."""
    text = report_path.read_text(encoding="utf-8")

    # Extract summary stats
    summary_match = re.search(r"## Summary\n- HIGH: (\d+)\n- MEDIUM: (\d+)\n- LOW: (\d+)", text)
    if not summary_match:
        return {}

    high_count = int(summary_match.group(1))
    medium_count = int(summary_match.group(2))
    low_count = int(summary_match.group(3))

    # Extract scanned files count
    scanned_match = re.search(r"Scanned: (\d+) Coq files", text)
    scanned_count = int(scanned_match.group(1)) if scanned_match else 0

    # Parse findings by rule
    findings_by_rule: Dict[str, List[str]] = defaultdict(list)
    findings_by_file: Dict[str, List[str]] = defaultdict(list)

    # Find all findings
    finding_pattern = re.compile(r"^- L(\d+): \*\*([A-Z_]+)\*\* — (.+)$", re.MULTILINE)
    current_file = None

    for line in text.splitlines():
        # Track current file
        file_match = re.match(r"^#### `(.+)`$", line)
        if file_match:
            current_file = file_match.group(1)
            continue

        # Parse finding
        finding_match = finding_pattern.match(line)
        if finding_match and current_file:
            line_num = finding_match.group(1)
            rule_id = finding_match.group(2)
            message = finding_match.group(3)

            findings_by_rule[rule_id].append(current_file)
            findings_by_file[current_file].append(rule_id)

    # Parse vacuity ranking
    vacuity_files = []
    in_vacuity = False
    for line in text.splitlines():
        if "## Vacuity Ranking" in line:
            in_vacuity = True
            continue
        if in_vacuity and line.startswith("|") and not line.startswith("| score"):
            parts = line.split("|")
            if len(parts) >= 4:
                try:
                    score = int(parts[1].strip())
                    tags = parts[2].strip()
                    file_path = parts[3].strip().strip("`")
                    vacuity_files.append((score, tags, file_path))
                except:
                    pass

    return {
        "high_count": high_count,
        "medium_count": medium_count,
        "low_count": low_count,
        "total_count": high_count + medium_count + low_count,
        "scanned_count": scanned_count,
        "findings_by_rule": dict(findings_by_rule),
        "findings_by_file": dict(findings_by_file),
        "vacuity_files": vacuity_files,
    }


def generate_insights(data: Dict) -> List[AnalysisInsight]:
    """Generate actionable insights from parsed data."""
    insights = []

    findings_by_rule = data.get("findings_by_rule", {})

    # Insight 1: Unused hypotheses
    if "UNUSED_HYPOTHESIS" in findings_by_rule:
        count = len(findings_by_rule["UNUSED_HYPOTHESIS"])
        insights.append(
            AnalysisInsight(
                category="Proof Quality",
                severity="MEDIUM",
                count=count,
                description=f"{count} unused hypotheses detected across proofs",
                recommendation="Review proof structure. Unused hypotheses may indicate: (1) over-general statements, (2) missing proof steps, or (3) opportunities to simplify theorem statements.",
            )
        )

    # Insight 2: Comment smells
    if "COMMENT_SMELL" in findings_by_rule:
        count = len(findings_by_rule["COMMENT_SMELL"])
        insights.append(
            AnalysisInsight(
                category="Code Hygiene",
                severity="MEDIUM",
                count=count,
                description=f"{count} TODO/FIXME markers found in comments",
                recommendation="Track these as explicit proof obligations. Consider creating GitHub issues for unresolved TODOs.",
            )
        )

    # Insight 3: Vacuous statements
    vacuous_rules = ["PROP_TAUTOLOGY", "IMPLIES_TRUE_STMT", "LET_IN_TRUE_STMT", "EXISTS_TRUE_STMT"]
    vacuous_count = sum(len(findings_by_rule.get(r, [])) for r in vacuous_rules)
    if vacuous_count > 0:
        insights.append(
            AnalysisInsight(
                category="Proof Correctness",
                severity="HIGH",
                count=vacuous_count,
                description=f"{vacuous_count} potentially vacuous theorems/lemmas",
                recommendation="CRITICAL: These statements may prove nothing. Review each for mathematical content. If legitimately trivial, add explicit comments explaining why.",
            )
        )

    # Insight 4: Axioms and parameters
    if "AXIOM_OR_PARAMETER" in findings_by_rule:
        count = len(findings_by_rule["AXIOM_OR_PARAMETER"])
        insights.append(
            AnalysisInsight(
                category="Assumptions",
                severity="HIGH",
                count=count,
                description=f"{count} axioms/parameters declared",
                recommendation="Document each axiom's necessity. Consider: (1) Can it be proven? (2) Is it a standard library axiom? (3) Should it be a module parameter instead?",
            )
        )

    # Insight 5: Clamps and truncations
    if "CLAMP_OR_TRUNCATION" in findings_by_rule or "Z_TO_NAT_BOUNDARY" in findings_by_rule:
        count = len(findings_by_rule.get("CLAMP_OR_TRUNCATION", [])) + len(findings_by_rule.get("Z_TO_NAT_BOUNDARY", []))
        insights.append(
            AnalysisInsight(
                category="Numeric Safety",
                severity="MEDIUM",
                count=count,
                description=f"{count} uses of clamps/truncations (Z.to_nat, Z.abs, etc.)",
                recommendation="Verify domain constraints are explicit. Clamps can hide overflow/underflow bugs. Consider using refinement types or explicit guards.",
            )
        )

    # Insight 6: Admitted proofs
    if "ADMITTED" in findings_by_rule:
        count = len(findings_by_rule["ADMITTED"])
        insights.append(
            AnalysisInsight(
                category="Proof Obligations",
                severity="HIGH",
                count=count,
                description=f"{count} admitted (incomplete) proofs",
                recommendation="CRITICAL: Track these as blocking issues. Create a proof obligation tracker. Prioritize by dependency depth.",
            )
        )

    # Insight 7: Physics analogy contracts
    if "PHYSICS_ANALOGY_CONTRACT" in findings_by_rule:
        count = len(findings_by_rule["PHYSICS_ANALOGY_CONTRACT"])
        insights.append(
            AnalysisInsight(
                category="Physics Correspondence",
                severity="HIGH",
                count=count,
                description=f"{count} physics-analogy theorems lack invariance lemmas",
                recommendation="For each physics claim, prove the corresponding equivariance lemma (e.g., Noether symmetry). Mark definitional identities explicitly.",
            )
        )

    return insights


def generate_analysis_report(data: Dict, insights: List[AnalysisInsight], output_path: Path) -> None:
    """Generate a comprehensive analysis report."""
    lines = []

    lines.append("# INQUISITOR ANALYSIS REPORT\n")
    lines.append("**Comprehensive Proof Quality Assessment**\n")
    lines.append("\n---\n\n")

    # Executive Summary
    lines.append("## Executive Summary\n\n")
    total = data["total_count"]
    scanned = data["scanned_count"]
    avg_findings = total / scanned if scanned > 0 else 0

    lines.append(f"**Scanned:** {scanned} Coq files  \n")
    lines.append(f"**Total Findings:** {total}  \n")
    lines.append(f"**Average:** {avg_findings:.1f} findings per file  \n")
    lines.append("\n")

    lines.append("**Severity Breakdown:**\n\n")
    lines.append(f"- 🔴 **HIGH:** {data['high_count']} ({100*data['high_count']/total if total > 0 else 0:.1f}%)\n")
    lines.append(f"- 🟡 **MEDIUM:** {data['medium_count']} ({100*data['medium_count']/total if total > 0 else 0:.1f}%)\n")
    lines.append(f"- 🟢 **LOW:** {data['low_count']} ({100*data['low_count']/total if total > 0 else 0:.1f}%)\n")
    lines.append("\n")

    # Quality Score
    quality_score = 100 - min(100, (data['high_count'] * 2 + data['medium_count']) / scanned if scanned > 0 else 0)
    lines.append(f"**Quality Score:** {quality_score:.1f}/100\n\n")

    if quality_score >= 90:
        grade = "A (Excellent)"
    elif quality_score >= 80:
        grade = "B (Good)"
    elif quality_score >= 70:
        grade = "C (Fair)"
    elif quality_score >= 60:
        grade = "D (Needs Improvement)"
    else:
        grade = "F (Critical Issues)"

    lines.append(f"**Grade:** {grade}\n\n")
    lines.append("\n---\n\n")

    # Key Insights
    lines.append("## Key Insights\n\n")

    if insights:
        for i, insight in enumerate(sorted(insights, key=lambda x: (x.severity != "HIGH", -x.count)), 1):
            severity_emoji = {"HIGH": "🔴", "MEDIUM": "🟡", "LOW": "🟢"}[insight.severity]
            lines.append(f"### {i}. {insight.category} {severity_emoji}\n\n")
            lines.append(f"**Finding:** {insight.description}\n\n")
            lines.append(f"**Recommendation:** {insight.recommendation}\n\n")
    else:
        lines.append("No specific insights generated.\n\n")

    lines.append("\n---\n\n")

    # Top Issues by Category
    lines.append("## Top Issues by Category\n\n")

    findings_by_rule = data.get("findings_by_rule", {})
    if findings_by_rule:
        sorted_rules = sorted(findings_by_rule.items(), key=lambda x: -len(x[1]))[:15]

        lines.append("| Rank | Rule | Count | Files Affected |\n")
        lines.append("|---:|---|---:|---:|\n")

        for rank, (rule, files) in enumerate(sorted_rules, 1):
            unique_files = len(set(files))
            lines.append(f"| {rank} | `{rule}` | {len(files)} | {unique_files} |\n")

        lines.append("\n")

    lines.append("\n---\n\n")

    # Highest Impact Files
    lines.append("## Highest Impact Files\n\n")
    lines.append("*Files with the most findings (potential refactor candidates)*\n\n")

    findings_by_file = data.get("findings_by_file", {})
    if findings_by_file:
        sorted_files = sorted(findings_by_file.items(), key=lambda x: -len(x[1]))[:20]

        lines.append("| Rank | File | Finding Count |\n")
        lines.append("|---:|---|---:|\n")

        for rank, (file_path, finding_list) in enumerate(sorted_files, 1):
            lines.append(f"| {rank} | `{file_path}` | {len(finding_list)} |\n")

        lines.append("\n")

    lines.append("\n---\n\n")

    # Vacuity Analysis
    if data.get("vacuity_files"):
        lines.append("## Vacuity Analysis\n\n")
        lines.append("*Files with indicators of incomplete/placeholder proofs*\n\n")

        lines.append("| Score | Tags | File |\n")
        lines.append("|---:|---|---|\n")

        for score, tags, file_path in sorted(data["vacuity_files"], key=lambda x: -x[0])[:15]:
            lines.append(f"| {score} | {tags} | `{file_path}` |\n")

        lines.append("\n")

    lines.append("\n---\n\n")

    # Recommendations
    lines.append("## Prioritized Remediation Plan\n\n")

    lines.append("### Phase 1: Critical Issues (HIGH Priority)\n\n")
    lines.append("1. **Resolve all `ADMITTED` proofs** - Complete or remove admitted lemmas\n")
    lines.append("2. **Eliminate vacuous statements** - Fix `PROP_TAUTOLOGY`, `IMPLIES_TRUE_STMT`, etc.\n")
    lines.append("3. **Document axioms** - Justify each `AXIOM_OR_PARAMETER` or prove them\n")
    lines.append("4. **Address physics contracts** - Add required invariance lemmas\n\n")

    lines.append("### Phase 2: Code Quality (MEDIUM Priority)\n\n")
    lines.append("1. **Clean up TODO/FIXME markers** - Create tracking issues\n")
    lines.append("2. **Review clamps/truncations** - Add domain guards\n")
    lines.append("3. **Refactor complex proofs** - Break down long/complex proofs\n")
    lines.append("4. **Remove unused hypotheses** - Simplify proof statements\n\n")

    lines.append("### Phase 3: Maintenance (LOW Priority)\n\n")
    lines.append("1. **Standardize naming conventions**\n")
    lines.append("2. **Remove duplicate imports**\n")
    lines.append("3. **Optimize proof tactics**\n\n")

    lines.append("\n---\n\n")

    # Footer
    lines.append("## Next Steps\n\n")
    lines.append("1. Review this analysis with the development team\n")
    lines.append("2. Create GitHub issues for HIGH severity findings\n")
    lines.append("3. Establish proof obligation tracking system\n")
    lines.append("4. Set up continuous Inquisitor runs in CI\n")
    lines.append("5. Schedule regular proof quality reviews\n\n")

    output_path.write_text("".join(lines), encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description="Analyze Inquisitor reports and generate insights")
    parser.add_argument(
        "--report",
        default="INQUISITOR_REPORT.md",
        help="Path to Inquisitor report to analyze",
    )
    parser.add_argument(
        "--output",
        default="INQUISITOR_ANALYSIS.md",
        help="Output path for analysis report",
    )

    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    report_path = repo_root / args.report
    output_path = repo_root / args.output

    if not report_path.exists():
        print(f"Error: Report not found at {report_path}")
        return 1

    print("=" * 80)
    print("INQUISITOR ANALYSIS")
    print("=" * 80)
    print(f"Analyzing: {report_path}")
    print(f"Output: {output_path}")
    print()

    # Parse report
    data = parse_inquisitor_report(report_path)

    if not data:
        print("Error: Failed to parse report")
        return 1

    print(f"Parsed {data['total_count']} findings from {data['scanned_count']} files")
    print()

    # Generate insights
    insights = generate_insights(data)
    print(f"Generated {len(insights)} actionable insights")
    print()

    # Generate report
    generate_analysis_report(data, insights, output_path)

    print("=" * 80)
    print("ANALYSIS COMPLETE")
    print(f"Report written to: {output_path}")
    print("=" * 80)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
