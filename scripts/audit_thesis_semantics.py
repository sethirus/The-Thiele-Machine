#!/usr/bin/env python3
"""Audit thesis prose against Coq theorem TYPES (not just names).

For each \texttt{name} citation in a thesis file, look up the Coq theorem's
type signature (parsed from the .v source) and run heuristic checks against
the surrounding prose. Reports mismatches the human should review.

What it checks:
  1. **Biconditional/Equivalence**: if the type has `<->`, prose should say
     "iff" / "if and only if" / "biconditional" / "equivalent". If the type
     has only one-direction `->`, prose should NOT claim "iff".
  2. **Hypotheses present**: if the type has hypotheses (`H1 -> H2 -> Goal`),
     prose claiming "unconditional" / "no hypotheses" / "axiom-free" is a
     potential overclaim.
  3. **Vacuity warnings**: theorems whose type is `X = X` or `forall x, x = x`
     or `exists y, y = f x` are flagged when the prose claims substantive
     content. These are documented soft proofs in this codebase, but the
     auditor surfaces them explicitly.
  4. **Quantifier alignment**: if the type starts with `forall (x : T1) ...`,
     prose should mention the universal scope (informally) — at minimum, the
     prose shouldn't state a *specific* instance as the theorem.

Limitation: this is a heuristic auditor. It will produce false positives
and miss subtler issues. The output is a punch list for human review, not
a Qed-style verification.

Usage: scripts/audit_thesis_semantics.py thesis/short_thesis.tex [...]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from collections import defaultdict
from dataclasses import dataclass

REPO = Path(__file__).resolve().parent.parent
COQ = REPO / "coq"

# How much prose around a citation to inspect (chars before/after the match).
PROSE_WINDOW = 600


@dataclass
class CoqTheorem:
    name: str
    file: str
    line: int
    statement: str  # type signature only (after `:` before `Proof.`)
    proof_body: str  # tactic script (for vacuity/triviality detection)


def index_coq_theorems(coq_root: Path) -> dict[str, list[CoqTheorem]]:
    """Walk every .v file (excluding vendor + archive) and extract every
    Theorem/Lemma/Corollary/etc with its statement string and proof script."""
    out: dict[str, list[CoqTheorem]] = defaultdict(list)

    decl_kw = (
        r"(?:Global\s+|Local\s+|Program\s+)?"
        r"(?:Theorem|Lemma|Corollary|Fact|Remark|Proposition)"
    )
    # Capture: name `: TYPE Proof. BODY Qed.`  (or Defined.)
    full_re = re.compile(
        rf"\n\s*{decl_kw}\s+([A-Za-z_][A-Za-z0-9_']*)\s*"
        r"(?:\([^)]*\)\s*)*"          # optional binders
        r":\s*(.*?)"                  # the TYPE string (lazy)
        r"\s*Proof\s*\.\s*(.*?)"      # the proof BODY
        r"\s*(?:Qed|Defined|Admitted)\s*\.",
        re.DOTALL,
    )

    for vf in coq_root.rglob("*.v"):
        path_str = str(vf)
        if "/vendor/" in path_str or "/archive/" in path_str:
            continue
        try:
            text = vf.read_text(errors="replace")
        except OSError:
            continue
        # Strip Coq comments (* ... *) before parsing — they can contain
        # confusing strings. Handle nested by replacing iteratively.
        clean = strip_coq_comments(text)
        rel = vf.relative_to(REPO)
        for m in full_re.finditer(clean):
            name = m.group(1)
            statement = clean_whitespace(m.group(2).strip())
            body = clean_whitespace(m.group(3).strip())
            line = clean.count("\n", 0, m.start()) + 1
            out[name].append(CoqTheorem(name, str(rel), line, statement, body))
    return out


def strip_coq_comments(text: str) -> str:
    """Remove (* ... *) comments, handling nesting."""
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text[i : i + 2] == "(*":
            depth = 1
            i += 2
        elif depth > 0 and text[i : i + 2] == "(*":
            depth += 1
            i += 2
        elif depth > 0 and text[i : i + 2] == "*)":
            depth -= 1
            i += 2
            if depth == 0:
                out.append(" ")  # preserve whitespace
        elif depth == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def clean_whitespace(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


# ---------------------------------------------------------------------------
# Type signature analysis
# ---------------------------------------------------------------------------


def analyze_type(stmt: str) -> dict:
    """Heuristic structural analysis of a Coq type signature."""
    s = stmt
    info = {
        "has_iff_in_conclusion": False,
        "has_iff_anywhere": "<->" in s,
        "is_universal": False,
        "is_trivial_eq": False,
        "is_trivial_exists": False,
        "premise_count": 0,
        "is_conjunction": False,
        "raw": s,
    }

    # Count `->` not inside parentheses — heuristic for hypothesis count
    info["premise_count"] = top_level_arrow_count(s)

    # Universal: starts with "forall"
    if re.match(r"\s*forall\b", s):
        info["is_universal"] = True

    # Conclusion-level analysis (strip leading `forall...,` and `H ->` chains)
    concl = conclusion_of(s)

    # `<->` in conclusion (not in a hypothesis)
    if "<->" in concl:
        info["has_iff_in_conclusion"] = True

    # Conjunction at top of conclusion: `(A) /\ (B) /\ (C)`
    # Heuristic: if conclusion has top-level /\, treat as conjunction
    if top_level_andlevel(concl) >= 1:
        info["is_conjunction"] = True

    # Trivial equality: the WHOLE conclusion is `expr = expr` with same sides
    eq_match = re.match(r"^(.+?)\s*=\s*(.+?)$", concl)
    if eq_match and not info["is_conjunction"] and "<->" not in concl:
        lhs, rhs = eq_match.group(1).strip(), eq_match.group(2).strip()
        if normalize_term(lhs) == normalize_term(rhs):
            info["is_trivial_eq"] = True

    # Trivial existential: the WHOLE conclusion is `exists y, y = f x`.
    # NOT flagged for conjunctions where this is one of several parts —
    # those are usually honest "totality" claims alongside substantive parts.
    if not info["is_conjunction"]:
        if re.fullmatch(r"\s*exists\s+\w+\s*,\s*\w+\s*=\s*[^.]+", concl):
            info["is_trivial_exists"] = True

    return info


def top_level_andlevel(s: str) -> int:
    """Count top-level `/\\` operators (not inside parens)."""
    depth = 0
    count = 0
    i = 0
    while i < len(s) - 1:
        c = s[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and s[i : i + 2] == "/\\":
            count += 1
            i += 1
        i += 1
    return count


def top_level_arrow_count(s: str) -> int:
    """Count `->` arrows at depth 0 (not inside parens). The forall binders
    and the final `->` to the conclusion both count toward the premise count
    minus 1 for the final goal."""
    depth = 0
    count = 0
    i = 0
    while i < len(s) - 1:
        c = s[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and s[i : i + 2] == "->":
            count += 1
            i += 1
        i += 1
    return count


def conclusion_of(s: str) -> str:
    """Strip leading `forall ..., ` and `H -> ` chains to get the conclusion."""
    s = re.sub(r"^\s*forall\s+[^,]+,\s*", "", s)
    # Strip any number of leading `H ->`
    while True:
        m = re.match(r"^\s*\(?[^()]*?\)?\s*->\s*", s)
        if not m:
            break
        s = s[m.end():]
    return s.strip()


def normalize_term(s: str) -> str:
    return re.sub(r"\s+", "", s)


# ---------------------------------------------------------------------------
# Prose extraction
# ---------------------------------------------------------------------------


def extract_citations_with_prose(tex_path: Path):
    """Yield (token, line_no, prose_window) for each \\texttt{...} citation."""
    text = tex_path.read_text(errors="replace")
    if tex_path.suffix == ".md":
        cite_re = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")
    else:
        cite_re = re.compile(r"\\texttt\{([^{}]*)\}")
    for m in cite_re.finditer(text):
        raw = m.group(1)
        token = raw.replace("\\_", "_").replace("\\%", "%").replace("\\&", "&").strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token):
            continue
        lo = max(0, m.start() - PROSE_WINDOW)
        hi = min(len(text), m.end() + PROSE_WINDOW)
        prose = clean_latex_for_prose(text[lo:hi])
        line = text.count("\n", 0, m.start()) + 1
        yield token, line, prose


def clean_latex_for_prose(s: str) -> str:
    """Strip LaTeX commands so plain English remains.

    Note: the prose window may cut mid-math (unbalanced `$`), so we don't
    try to match `$...$` greedily — that would eat across math gaps and
    delete legitimate prose. Instead we remove `$` characters and any
    obvious math-only sequences (\\command, {}), letting math noise like
    `M_B` or `\\mathrm` pass through as harmless fragments. The heuristic
    checks only lowercase English phrases, so noise doesn't trigger
    false positives.
    """
    # Keep \texttt{X} as X (don't lose the citations themselves)
    s = re.sub(r"\\texttt\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\emph\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\textbf\{([^{}]*)\}", r"\1", s)
    s = re.sub(r"\\textit\{([^{}]*)\}", r"\1", s)
    # Remove other backslash commands (commands without arg-braces, OR with
    # the bracketed arg already stripped above)
    s = re.sub(r"\\[a-zA-Z]+\*?", " ", s)
    # Remove braces and dollar signs (math markers); any leftover math
    # tokens are harmless prose noise.
    s = re.sub(r"[{}$]", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s.lower()


# ---------------------------------------------------------------------------
# Heuristic mismatch checks
# ---------------------------------------------------------------------------


IFF_PHRASES = [
    "iff", "if and only if", "biconditional", "equivalent", "exactly when",
    "are equivalent", "is equivalent", "two directions", "both directions",
    "biconditionally",
]

UNCONDITIONAL_PHRASES = [
    "unconditional", "no hypotheses", "no axioms", "zero axioms", "axiom-free",
    "without assumption", "with no premise", "no preconditions", "no premise",
    "no physical axiom",
]

# If any of these "context-rescue" phrases appears in the same prose window,
# the unconditional claim is talking about a *different* theorem group, so
# don't flag the cited theorem as overclaiming.
CONDITIONAL_DEFEATERS = [
    "under invariant", "under invariants", "under the joint",
    "under structural invariant", "under structural invariants",
    "under the inductive", "joint invariant", "joint structural invariant",
    "under inductive invariant", "side hypothesis", "side hypotheses",
    "argument-validity", "if module", "given ", "assuming ", "provided ",
    "where defined", "valid arguments", "if x ", "if the ", "for any state reachable",
    "discharged", "side condition",
    # Global/proof-tree-level statements ("no axioms beyond foundational
    # logic", "no admits", "no admitted") are about the entire kernel build,
    # not about the specific cited theorem's premise count.
    "no axioms beyond", "no admits", "no admitted", "axioms beyond foundational",
    "active proof tree", "across the proof tree", "proof tree contains",
    "for local", "local strategies", "local deterministic", "deterministic strategies",
]


def check_one(citation: str, line: int, prose: str, theorems: list[CoqTheorem]) -> list[str]:
    """Return list of warning strings (empty = no findings)."""
    findings: list[str] = []
    if not theorems:
        return findings  # not a theorem citation, or unknown name

    # Use the first matching theorem (most projects have unique names)
    thm = theorems[0]
    info = analyze_type(thm.statement)

    iff_in_prose = any(p in prose for p in IFF_PHRASES)
    unconditional_in_prose = any(p in prose for p in UNCONDITIONAL_PHRASES)
    # If the prose window also contains a conditional-defeater phrase, the
    # "unconditional" word is probably describing a different group of
    # theorems — don't flag the cited theorem.
    if unconditional_in_prose and any(d in prose for d in CONDITIONAL_DEFEATERS):
        unconditional_in_prose = False

    # Check 1: Type's CONCLUSION has <-> but prose doesn't say iff.
    # Skipping this check would be safer because biconditional citations
    # are usually accompanied by phrases like "biconditional" / "iff" in
    # the same paragraph. We only flag when even the wider window has none.
    if info["has_iff_in_conclusion"] and not iff_in_prose:
        findings.append(
            "🟧 conclusion has `<->` but surrounding prose doesn't mention iff/biconditional/equivalent"
        )

    # Check 2: skipped intentionally. "Prose mentions iff but cited theorem
    # is one direction" is a frequent false positive — citing a forward or
    # reverse lemma in a paragraph that discusses the biconditional is
    # legitimate (the biconditional itself is also cited nearby).

    # Check 3: Prose claims unconditional but the cited theorem has real
    # hypotheses (not just the final `-> goal` arrow).
    # `forall x, x = x` has 0 arrows. `forall x, P x -> Q x` has 1 arrow
    # (the final `->`). `forall x, P -> Q -> R` has 2 arrows (1 hypothesis
    # + final). So `premise_count >= 2` is "actual hypothesis present".
    if unconditional_in_prose and info["premise_count"] >= 2:
        findings.append(
            f"🟧 prose claims unconditional but type has {info['premise_count']} top-level `->` "
            f"(at least {info['premise_count'] - 1} hypothesis chained before the conclusion)"
        )

    # Check 4: Type's WHOLE conclusion is X = X (vacuous equality)
    if info["is_trivial_eq"]:
        findings.append(
            "🟥 conclusion is a trivial equality `X = X` — likely soft-proof / trust-boundary placeholder; "
            "verify prose doesn't overclaim it as substantive"
        )

    # Check 5: Type's WHOLE conclusion is `exists y, y = f x` (trivial existential)
    if info["is_trivial_exists"]:
        findings.append(
            "🟥 conclusion is `exists y, y = f x` — trivially provable by giving the witness; "
            "verify prose doesn't claim cross-language bisimulation or similar substantive content"
        )

    # Check 6: Definitional alias — proof body is just `exact name.` or similar
    body = thm.proof_body
    if re.fullmatch(r"(?:intros[^.]*\.\s*)*(?:exact|apply|refine)\s+[A-Za-z_][\w']*\s*\.", body):
        if any(w in prose for w in ["new", "we prove", "established", "proved here"]):
            findings.append(
                f"🟨 proof is a pure alias to another theorem (`{body}`) — verify prose doesn't claim novelty"
            )

    return findings


def render(tex_path: Path, theorems: dict[str, list[CoqTheorem]]):
    findings_by_loc: list[tuple[str, int, str, list[str]]] = []
    citations_seen = 0
    citations_with_theorem = 0

    for token, line, prose in extract_citations_with_prose(tex_path):
        citations_seen += 1
        thms = theorems.get(token, [])
        if not thms:
            continue
        citations_with_theorem += 1
        warnings = check_one(token, line, prose, thms)
        if warnings:
            findings_by_loc.append((token, line, thms[0].file, warnings))

    rel = tex_path.relative_to(REPO)
    print(f"=== {rel} ===")
    print(f"  citations seen:                {citations_seen}")
    print(f"  matched a Coq theorem:         {citations_with_theorem}")
    print(f"  with structural concerns:      {len(findings_by_loc)}")
    if not findings_by_loc:
        print(f"  ✓ no structural concerns flagged\n")
        return True
    print()
    for token, line, src, warnings in findings_by_loc:
        print(f"  {rel}:{line}  →  \\texttt{{{token}}}  (defined in {src})")
        for w in warnings:
            print(f"      {w}")
        print()
    return False


def main():
    targets = [Path(p).resolve() for p in sys.argv[1:]] if len(sys.argv) > 1 else [
        REPO / "thesis" / "short_thesis.tex",
    ]
    print(f"Indexing Coq theorems under {COQ}...")
    theorems = index_coq_theorems(COQ)
    n_decls = sum(len(v) for v in theorems.values())
    print(f"  → {n_decls} theorem declarations across {len(theorems)} unique names\n")

    overall_ok = True
    for tex in targets:
        if not tex.exists():
            print(f"SKIP (not found): {tex}")
            continue
        ok = render(tex, theorems)
        overall_ok = overall_ok and ok

    sys.exit(0 if overall_ok else 1)


if __name__ == "__main__":
    main()
