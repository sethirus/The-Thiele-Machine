#!/usr/bin/env python3
"""Audit every \texttt{...} citation in the LaTeX monograph against the live Coq tree.

For each \texttt{...}:
  - if it looks like a path ending in .v: the file must exist on disk
  - if it looks like a Coq identifier (snake_case, alpha[\w]*): there must be at
    least one top-level Coq declaration with that exact name in coq/ (Theorem,
    Lemma, Corollary, Definition, Inductive, Notation, Section Variable, Record,
    Fixpoint, Axiom, Parameter)

Exit code: 0 if every citation resolves, 1 otherwise.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from collections import defaultdict

REPO = Path(__file__).resolve().parent.parent
COQ_ROOTS = [REPO / "coq"]

# Citations we should *not* try to resolve as Coq identifiers — language
# keywords, tactics, English words, punctuation that LaTeX wraps in \texttt{}.
NON_COQ_TOKENS = {
    # tactics / keywords
    "Admitted", "admit", "give_up", "lra", "nra", "tauto", "trivial", "reflexivity",
    "psatz", "lia", "nia", "omega", "ring", "field", "auto", "intuition",
    "destruct", "induction", "rewrite", "apply", "exact", "assumption",
    "Qed", "Proof", "Theorem", "Lemma", "Corollary", "Definition", "Inductive",
    "Axiom", "Parameter", "Hypothesis", "Variable", "Section", "Module", "Context",
    "Record", "Class", "Instance", "Notation", "Fixpoint",
    "True", "False", "true", "false", "Type", "Prop", "Set", "exists", "forall",
    "fun", "let", "match", "with", "end", "if", "then", "else",
    # State-component abbreviations used in tuple notation like (mem, regs, pc, mu, certified)
    "mem", "regs", "pc", "mu", "certified", "halted", "err",
    # Pattern variables / placeholders
    "wc_same", "wc_diff", "wc_same_AB", "wc_diff_AB", "wc_same_xy", "wc_diff_xy",
    # Coq tactics not yet listed
    "discriminate", "inversion", "constructor", "split", "left", "right",
    "specialize", "pose", "assert", "subst", "simpl", "cbn", "fold", "unfold",
    # Python prose tokens that show up wrapped in `code` in markdown / chapter docs
    "None", "True", "False", "dict", "list", "set", "tuple", "int", "str", "bool",
    "axioms", "axiom", "theorem", "lemma",
    # Generic short variable names appearing in code-block prose
    "mid", "instr", "prog", "trace", "state", "step",
    "ax", "m", "p", "r15", "new_state", "new_region", "new_axioms",
    "obs",
    # Coq stdlib types / functions (lowercase or capitalized) referenced in prose
    "nodup", "option", "In", "Some", "string",
    "nodup_fixed_point",  # Coq.Lists.List
    # Bluespec / Verilog signal names referenced in prose ("Mirrors the RTL X register")
    "logic_acc",
    # Interpretive labels for the kinetic/potential μ decomposition (chapter 3
    # explicitly tags these "a.k.a." — they are not Coq identifiers, the
    # kernel records a single counter vm_mu).
    "mu_execution", "mu_discovery",
    # Illustrative ReceiptPredicate examples mentioned in chapter 3 / 5 prose
    # AND in NoFreeInsight.v COMMENTS (not as actual Coq definitions). The
    # chapters explicitly introduce them with "for example".
    "chsh_compatible", "chsh_quantum", "chsh_supra",
    "P_classical", "P_quantum", "P_specific", "P_any", "P_strong", "P_weak",
    "P1", "P2",
    # TRS-1.0 receipt JSON field names / kind values (not Coq identifiers)
    "fileset", "global_digest",
    # JSON output field names (Python harness output, not Coq identifiers)
    "error", "graph",
    # Python helper functions in tests/ (not Coq identifiers)
    "_run_both",
    # Identifiers explicitly described as NON-existent fields/opcodes in the monograph
    # (the monograph discusses these to clarify they are NOT in the Coq kernel).
    # The monograph is correct that they don't exist; the audit shouldn't flag them.
    "vm_heap", "vm_output", "vm_imem",  # explicitly disclaimed at line 581
    "INIT_PT", "INIT_ACTIVE_MODULE",     # explicitly described as harness commands, not VM ops
    "ThieleVM",                          # explicitly disclaimed in chapter 13: "There is no ThieleVM class"
    "decode_instruction",                # explicitly clarified in chapter 4: kernel does not bit-decode
    # CLI / tools / non-Coq filenames
    "cosim", "yosys", "iverilog", "verilator", "make", "pytest",
    "coqtop", "vvp", "Makefile", "nextpnr-xilinx", "xc7frames2bit",
    "fasm2frames", "openFPGALoader",
    # External library / language modules referenced in prose (not Coq identifiers)
    "json", "Yojson", "Int64",
    # Coq stdlib types / library modules referenced in prose
    "nat", "Option", "R", "Classical", "Decidable", "ProofIrrelevance", "KamiHW",
    # Coq operators / arithmetic functions referenced in prose
    "sub", "eqb",
    # Verilog / Bluespec keywords and generated module / port / wire names
    # (these come from the Kami-generated RTL, not from Coq identifiers).
    "wire", "reg", "case",
    "mkModule1", "loadInstr", "WILL_FIRE_RL_step", "RST_N",
    "getMuTensor0", "getMuTensor3", "getWcSame00", "getWcDiff11",
    # Verilog wire / signal names referenced from RTL code listings
    "overflow",
    # Python class / field / constant names from thielecpu/vm.py and
    # related runtime modules (not Coq identifiers).
    "RegionGraph", "partition_masks", "WORD64_MASK", "partitionGraph",
    # Pseudocode parameter / JSON field names from experiment-protocol prose
    # (defined in the algorithm listings or emitted by the experiment harness,
    # not in the Coq kernel)
    "coarse_levels", "problem_sizes", "mu_lower_bounds_log2_ratio",
    "mu_slack_in",   # appears as `mu_slack_in_[0,1)` — `_[0,1)` is stripped by tokenizer
    # Inquisitor heuristic-rule labels (Python string constants in
    # scripts/inquisitor.py — categories of static-analysis findings, not
    # Coq identifiers or VM opcodes).
    "ADMITTED", "ADMIT_TACTIC", "GIVE_UP_TACTIC",
    "AXIOM_OR_PARAMETER", "HYPOTHESIS_ASSUME", "CONTEXT_ASSUMPTION",
    "PROP_TAUTOLOGY",
    "IMPLIES_TRUE_STMT", "LET_IN_TRUE_STMT", "EXISTS_TRUE_STMT",
    "CONST_Q_FUN", "EXISTS_CONST_Q",
    "COMPILATION_ERROR", "ASSUMPTION_AUDIT",
    "COST_IS_LENGTH", "ZERO_CONST", "EMPTY_LIST", "CLAMP_OR_TRUNCATION",
    "COMMENT_SMELL", "TODO", "FIXME", "WIP",
    "SUSPICIOUS_SHORT_PROOF", "MU_COST_ZERO",
    "PHYSICS_ANALOGY_CONTRACT", "PROBLEMATIC_IMPORT",
    "TRIVIAL_EQUALITY", "CIRCULAR_INTROS_ASSUMPTION", "AXIOM_DOCUMENTED",
    # numeric literals / English wrapped in texttt
    "0", "1", "0xF00", "n", "k", "i", "j", "s",
}


def find_top_level_decls(coq_roots):
    """Walk every .v under each root (excluding vendor/) and return a dict
    {identifier: [file:line, ...]} of top-level declarations PLUS Record
    fields PLUS Inductive constructors."""
    decl_re = re.compile(
        r"^\s*(?:Global\s+|Local\s+|Program\s+)?"
        r"(?:Theorem|Lemma|Corollary|Fact|Remark|Proposition|"
        r"Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|"
        r"Record|Class|Instance|Notation|Variable|Variables|Hypothesis|Hypotheses|"
        r"Axiom|Parameter|Conjecture|Module(?:\s+Type)?)"
        r"\s+(?:\{[^}]*\}\s*)?(?:\(\*[^*]*\*\)\s*)?"
        r"([A-Za-z_][A-Za-z0-9_']*)",
        re.MULTILINE,
    )
    # Inductive constructor: lines starting with `| name (...)` inside an
    # Inductive block.
    constructor_re = re.compile(r"^\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)", re.MULTILINE)
    # Record field: lines like `field_name : type;` between `Record X := { ... }`
    record_block_re = re.compile(
        r"Record\s+\w+(?:\s*\([^)]*\))?\s*(?::=\s*(?:\w+)?\s*\{|:\s*\w*\s*:=\s*\{)([^}]*)\}",
        re.DOTALL,
    )
    # Catch every `field_name :` even when multiple fields share a line:
    # `wc_same_00 : nat; wc_diff_00 : nat;` should yield both names.
    # Strip Coq comments first, then split on `;` and look at the first ident
    # of each fragment.
    record_comment_re = re.compile(r"\(\*.*?\*\)", re.DOTALL)
    record_field_re = re.compile(r"^\s*([a-z_][A-Za-z0-9_']*)\s*:")
    # Inductive header (starts a block whose body we scan linearly until the
    # next top-level keyword). The previous regex tried `[^.]+?\.` to bound
    # the body, but real Inductive bodies routinely contain dots inside
    # subterms like `s.(vm_graph)`, so it terminated early and missed most
    # constructors of large inductive types like `vm_step`.
    inductive_header_re = re.compile(
        r"^\s*(?:CoInductive|Inductive)\s+([A-Za-z_][A-Za-z0-9_']*)",
        re.MULTILINE,
    )
    # Top-level Coq keyword that signals the end of the current block.
    # Anything starting at column 0 with one of these followed by whitespace
    # ends the inductive scan.
    top_level_terminator_re = re.compile(
        r"^(?:Section|End|Module|Theorem|Lemma|Corollary|Fact|Remark|Proposition|"
        r"Definition|Fixpoint|CoFixpoint|Inductive|CoInductive|Record|Class|"
        r"Instance|Notation|Axiom|Parameter|Conjecture|Hypothesis|Hypotheses|"
        r"Variable|Variables|Context|Print|Check|Eval|Compute|Goal|Proof|"
        r"Hint|Require|Import|Export|Open|Close|Reserved|Tactic|Ltac|"
        r"Arguments|Set|Unset|From)\b",
        re.MULTILINE,
    )

    table = defaultdict(list)
    for root in coq_roots:
        for vf in root.rglob("*.v"):
            if "/vendor/" in str(vf) or "/archive/" in str(vf):
                continue
            try:
                text = vf.read_text(errors="replace")
            except OSError:
                continue
            rel = vf.relative_to(REPO)

            # Top-level declarations
            for m in decl_re.finditer(text):
                ident = m.group(1)
                line = text.count("\n", 0, m.start()) + 1
                table[ident].append(f"{rel}:{line}")

            # Context (...) and Context {...} — Coq Section parameters
            for m in re.finditer(r"^\s*Context\s+([{(])", text, re.MULTILINE):
                # Find matching close brace from this position
                start = m.end() - 1  # at the opening bracket
                depth = 0
                close = start
                opener = m.group(1)
                closer = ")" if opener == "(" else "}"
                for j in range(start, len(text)):
                    if text[j] == opener:
                        depth += 1
                    elif text[j] == closer:
                        depth -= 1
                        if depth == 0:
                            close = j
                            break
                body = text[start + 1 : close]
                # First whitespace-separated identifier(s) before the colon are
                # the parameter name(s)
                if ":" in body:
                    head = body.split(":", 1)[0]
                    for name in head.split():
                        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
                            line = text.count("\n", 0, m.start()) + 1
                            table[name].append(f"{rel}:{line}")

            # Record fields — strip comments, split on `;`, take first
            # identifier of each fragment.
            for rm in record_block_re.finditer(text):
                body = rm.group(1)
                base_offset = rm.start(1)
                clean = record_comment_re.sub(" ", body)
                # Split on `;` to get one field per fragment
                cursor = 0
                for fragment in clean.split(";"):
                    fm = record_field_re.match(fragment.lstrip())
                    if fm:
                        field = fm.group(1)
                        # Approximate line — just use the Record block's start
                        line = text.count("\n", 0, base_offset) + 1
                        table[field].append(f"{rel}:{line}")

            # Inductive constructors AND their parameter names. We scan the
            # file linearly: at each Inductive header, walk forward through
            # the body and collect every `^| ident` line until we hit a
            # top-level Coq keyword that signals the next declaration.
            inductive_headers = list(inductive_header_re.finditer(text))
            for idx, im in enumerate(inductive_headers):
                body_start = im.end()
                # The body ends at the next top-level terminator after this
                # header — including the next Inductive header itself, which
                # the terminator regex catches via `Inductive`.
                next_terminator = top_level_terminator_re.search(text, body_start)
                body_end = next_terminator.start() if next_terminator else len(text)
                body = text[body_start:body_end]

                for cm in constructor_re.finditer(body):
                    ctor = cm.group(1)
                    line = text.count("\n", 0, body_start + cm.start()) + 1
                    table[ctor].append(f"{rel}:{line}")
                # Constructor parameters: `(name1 name2 : type)` groups
                for pm in re.finditer(r"\(([^():]+):", body):
                    for name in pm.group(1).split():
                        if re.fullmatch(r"[a-z_][A-Za-z0-9_']*", name):
                            line = text.count("\n", 0, body_start + pm.start()) + 1
                            table[name].append(f"{rel}:{line}")
    return table


def find_files_by_basename(coq_roots):
    """Return dict {basename: [path, ...]} for every .v file the monograph can
    cite — both Coq sources under coq/ AND Verilog sources under
    thielecpu/hardware/rtl/ and rtl_harness/. Vendor and archive trees are
    excluded."""
    table = defaultdict(list)
    extra_roots = [
        REPO / "thielecpu" / "hardware" / "rtl",
        REPO / "rtl_harness",
    ]
    for root in list(coq_roots) + extra_roots:
        if not root.exists():
            continue
        for vf in root.rglob("*.v"):
            sp = str(vf)
            if "/vendor/" in sp or "/archive/" in sp:
                continue
            table[vf.name].append(str(vf.relative_to(REPO)))
    return table


def extract_texttt_citations(tex_text):
    """Pull every LaTeX citation token: \\texttt{...}, \\path{...}, and any
    bare `Foo.v` / `bar/Foo.v` filename appearing in plain text.

    Bare-filename catch is needed because the monograph sometimes places file
    names inside \\normalfont (e.g. inside a theorem title) where they are
    not wrapped in \\texttt{}. Without this, the auditor missed citations
    like \\begin{theorem}[X {\\normalfont (Foo.v --- reference-only)}].

    LaTeX comments (`%` to end of line, when not escaped as `\\%`) are
    stripped before scanning so file/identifier names mentioned only in
    comments are not flagged. Line numbers are preserved by replacing
    comment text with spaces rather than removing it."""
    # Strip LaTeX line comments — replace each `%...` (when % is not escaped
    # by a backslash) with spaces so column/line offsets are preserved.
    def _strip_comment(match):
        return " " * len(match.group(0))
    tex_text = re.sub(r"(?<!\\)%[^\n]*", _strip_comment, tex_text)

    cites = []
    seen: set[tuple[str, int]] = set()

    # \texttt{...} (LaTeX-escaped underscores)
    for m in re.finditer(r"\\texttt\{([^{}]*)\}", tex_text):
        raw = m.group(1)
        unescaped = raw.replace("\\_", "_").replace("\\%", "%").replace("\\&", "&").strip()
        if not unescaped:
            continue
        line = tex_text.count("\n", 0, m.start()) + 1
        if (unescaped, line) not in seen:
            seen.add((unescaped, line))
            cites.append((unescaped, line))

    # \path{...} (\texttt-equivalent)
    for m in re.finditer(r"\\path\{([^{}]*)\}", tex_text):
        unescaped = m.group(1).replace("\\_", "_").strip()
        if not unescaped:
            continue
        line = tex_text.count("\n", 0, m.start()) + 1
        if (unescaped, line) not in seen:
            seen.add((unescaped, line))
            cites.append((unescaped, line))

    # Bare `Foo.v` or `path/Foo.v` filenames in plain prose. We strip
    # LaTeX-escaped underscores so `Foo\_Bar.v` is captured as `Foo_Bar.v`.
    plain = tex_text.replace("\\_", "_")
    for m in re.finditer(
        r"(?:(?<=\s)|(?<=\()|(?<=\[)|(?<=^))((?:[A-Za-z][\w/]*?/)?[A-Z][\w]*\.v)\b",
        plain,
    ):
        token = m.group(1)
        # Skip glob patterns and LaTeX-command artifacts
        if "*" in token or "\\" in token or "textbackslash" in token:
            continue
        line = plain.count("\n", 0, m.start()) + 1
        if (token, line) not in seen:
            seen.add((token, line))
            cites.append((token, line))

    return cites


def extract_markdown_citations(md_text):
    """Pull every `code` span payload from markdown."""
    cites = []
    # Single backtick code spans
    for m in re.finditer(r"`([^`\n]+)`", md_text):
        token = m.group(1).strip()
        # Skip math/CLI-flag-looking stuff
        if not token or len(token) > 80:
            continue
        line = md_text.count("\n", 0, m.start()) + 1
        cites.append((token, line))
    return cites


def extract_citations(path: Path):
    """Dispatch on file extension. Skips auto-generated reports (detected by
    a `Generated:` timestamp in the first 5 lines) — these enumerate Python
    rule constants and Coq filenames, not human-authored prose."""
    text = path.read_text(errors="replace")
    head = "\n".join(text.splitlines()[:5])
    if re.search(r"^\s*Generated\s*:\s*\d{4}-\d{2}-\d{2}", head, re.MULTILINE):
        return []  # auto-generated — citations are mechanically produced
    if path.suffix == ".tex":
        return extract_texttt_citations(text)
    if path.suffix == ".md":
        return extract_markdown_citations(text)
    return extract_texttt_citations(text)  # default to LaTeX


def classify(token: str) -> str:
    """Return 'file', 'ident', 'opcode', or 'skip' for a citation token."""
    # Skip glob patterns and LaTeX command artifacts
    if "*" in token or "\\" in token or "textbackslash" in token:
        return "skip"
    # File path — anything ending in .v with optional leading path
    if re.fullmatch(r"(?:[\w./-]+/)?[A-Za-z_][\w.-]*\.v", token):
        return "file"
    # Skip CLI commands and prose with spaces
    if " " in token:
        return "skip"
    # Directory-only references (e.g. "theory/", "kernel/") — these are
    # explicitly used in prose to point at *paths*, not specific files;
    # treat as prose (skip).
    if token.endswith("/"):
        return "skip"
    # File path heuristic: contains slash and looks like a path
    if "/" in token and not token.startswith("$"):
        return "file"
    # ALL_CAPS opcode mnemonic (e.g. PNEW, LOAD_IMM, CHSH_TRIAL) — these
    # correspond to Coq constructors named instr_<lowercase>. We exclude
    # ALL_CAPS tokens that already exist as a top-level Coq identifier
    # (e.g. A_QM is a Context parameter, not an opcode); the caller checks
    # both forms.
    # ALL_CAPS-with-underscore (LOAD_IMM, CHSH_TRIAL, A_QM) — could be opcode
    # mnemonic OR a real Coq identifier; the caller tries both.
    if re.fullmatch(r"[A-Z][A-Z0-9_]*", token) and "_" in token:
        return "opcode_or_ident"
    # Short ALL_CAPS without underscore (OR, AND, ADD, SUB, MUL, SHL, SHR, LUI,
    # PNEW, REVEAL, HALT) — also opcode_or_ident; the caller maps to instr_<lower>.
    if re.fullmatch(r"[A-Z][A-Z0-9]*", token) and len(token) >= 2:
        return "opcode_or_ident"
    # Pattern variable suffixes like wc_same_ab or wc_same_xy — placeholders
    # for index pairs. Skip if last component is a 2-letter pattern name.
    if re.fullmatch(r"[a-z_]+_(?:ab|xy|AB|XY)", token):
        return "skip"
    # Coq-style primed proof variables (s', g', graph', regs') — these are
    # local quantifier variables copied verbatim from inductive constructor
    # signatures into the monograph prose; they are not standalone declarations.
    if token.endswith("'") and re.fullmatch(r"[a-z_][A-Za-z0-9_]*'+", token):
        return "skip"
    # Python pytest test function references (e.g. test_all_46_opcodes_in_cosim)
    if token.startswith("test_"):
        return "skip"
    # Identifier — snake_case-ish, no spaces, no operators
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", token):
        return "ident"
    return "skip"


def opcode_to_constructor(token: str) -> str:
    """Map opcode mnemonic PNEW → instr_pnew."""
    return "instr_" + token.lower()


def audit(tex_path: Path, decls, files_by_name):
    cites = extract_citations(tex_path)

    missing_files: list[tuple[str, int]] = []
    missing_idents: list[tuple[str, int]] = []
    missing_opcodes: list[tuple[str, int]] = []
    skipped: dict[str, int] = defaultdict(int)
    file_hits = 0
    ident_hits = 0
    opcode_hits = 0

    for token, line in cites:
        kind = classify(token)
        if kind == "skip":
            skipped[token] += 1
            continue
        if kind == "file":
            # Could be a path like coq/kernel/Foo.v or just Foo.v
            full_path = REPO / token
            if full_path.exists():
                file_hits += 1
                continue
            # Try basename lookup — accepted as legitimate prose citation
            basename = Path(token).name
            if basename in files_by_name:
                file_hits += 1
                continue
            missing_files.append((token, line))
        elif kind == "opcode_or_ident":
            # Try as a direct identifier first (e.g. A_QM is a Context
            # parameter). Then try opcode-mnemonic-style mapping.
            if token in decls or token in NON_COQ_TOKENS:
                ident_hits += 1
                continue
            ctor = opcode_to_constructor(token)
            if ctor in decls:
                opcode_hits += 1
                continue
            missing_opcodes.append((token, line))
        else:  # ident
            if token in NON_COQ_TOKENS:
                continue
            if token in decls:
                ident_hits += 1
                continue
            missing_idents.append((token, line))

    return {
        "tex": str(tex_path.relative_to(REPO)),
        "total_citations": len(cites),
        "file_hits": file_hits,
        "ident_hits": ident_hits,
        "opcode_hits": opcode_hits,
        "missing_files": missing_files,
        "missing_idents": missing_idents,
        "missing_opcodes": missing_opcodes,
        "skipped_count": sum(skipped.values()),
    }


def main():
    targets = [Path(p).resolve() for p in sys.argv[1:]] if len(sys.argv) > 1 else [
        REPO / "monograph" / "monograph.tex",
    ]

    print(f"Indexing Coq declarations under {[str(r) for r in COQ_ROOTS]}...")
    decls = find_top_level_decls(COQ_ROOTS)
    files_by_name = find_files_by_basename(COQ_ROOTS)
    print(f"  → {len(decls)} top-level identifiers, {len(files_by_name)} .v files\n")

    overall_ok = True
    for tex in targets:
        if not tex.exists():
            print(f"SKIP (not found): {tex}")
            continue
        report = audit(tex, decls, files_by_name)
        print(f"=== {report['tex']} ===")
        print(f"  total \\texttt{{}} citations:    {report['total_citations']}")
        print(f"  resolved as files:           {report['file_hits']}")
        print(f"  resolved as Coq identifiers: {report['ident_hits']}")
        print(f"  resolved as opcode mnemonics:{report['opcode_hits']}")
        print(f"  skipped (non-Coq tokens):    {report['skipped_count']}")

        if report["missing_files"]:
            overall_ok = False
            print(f"\n  ❌ MISSING FILES ({len(report['missing_files'])}):")
            for token, line in report["missing_files"]:
                print(f"     {report['tex']}:{line}: {token}")

        if report["missing_idents"]:
            overall_ok = False
            print(f"\n  ❌ MISSING IDENTIFIERS ({len(report['missing_idents'])}):")
            for token, line in report["missing_idents"]:
                print(f"     {report['tex']}:{line}: {token}")

        if report["missing_opcodes"]:
            overall_ok = False
            print(f"\n  ❌ MISSING OPCODES ({len(report['missing_opcodes'])}):")
            for token, line in report["missing_opcodes"]:
                print(f"     {report['tex']}:{line}: {token} (looked for instr_{token.lower()})")

        if not (report["missing_files"] or report["missing_idents"] or report["missing_opcodes"]):
            print(f"\n  ✓ all citations resolve")
        print()

    sys.exit(0 if overall_ok else 1)


if __name__ == "__main__":
    main()
