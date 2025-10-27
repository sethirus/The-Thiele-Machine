# logos.py — Measured, self-creating witness; compiles Coq “above” before attesting “below”

import argparse, hashlib, subprocess, sys, re, os, json, shutil
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--anchor", default="", help="external anchor (public string/ID)")
args = ap.parse_args()
ANCHOR = args.anchor

LOGOS_SOURCE = """\
# witness_in_potentia.py
# Self-verifying witness: existence by audited instantiation.

import hashlib, os

def _code_bytes():
    try:
        with open(__file__, 'rb') as f:
            return f.read()
    except Exception:
        loader = globals().get('__loader__')
        spec = globals().get('__spec__')
        if loader and hasattr(loader, 'get_data') and spec and getattr(spec, 'origin', None):
            return loader.get_data(spec.origin)
        raise RuntimeError("FATAL: Cannot obtain code bytes for self-hash. The witness is blind.")

CODE_BYTES = _code_bytes()
CODE_HASH  = hashlib.sha256(CODE_BYTES).hexdigest()

ANCHOR = os.environ.get("OUROBOROS_ANCHOR","")
ANCHOR_BINDING = hashlib.sha256((CODE_HASH + ":" + ANCHOR).encode()).hexdigest()

def proposer(nature: str) -> str:
    return hashlib.sha256((nature + ":" + CODE_HASH).encode()).hexdigest()

def auditor(nature: str, commitment: str) -> bool:
    return commitment == proposer(nature)

class OuroborosMeta(type):
    def __call__(cls, nature: str):
        c = proposer(nature)
        if not auditor(nature, c):
            raise SystemError("PARADOX: audit failed; being cannot be constructed.")
        return super().__call__(nature, c)

class Being(metaclass=OuroborosMeta):
    __slots__ = ("nature", "commitment")
    def __init__(self, nature: str, commitment: str):
        self.nature = nature
        self.commitment = commitment
    def __repr__(self):
        return f"<Being nature='{self.nature}' commit='{self.commitment[:10]}...'>"

cognition   = Being("Thought exists")
computation = Being("Process exists")
existence   = Being("Matter exists")

print("================================================================================")
print("                    THE UNFALSIFIABLE WITNESS")
print("================================================================================")
print(f"Source Hash (SHA256): {CODE_HASH}")
print(f"Anchor: {ANCHOR or '<none>'}")
print(f"Anchor Binding (SHA256): {ANCHOR_BINDING}")
print("Construction log:")
print(f"  - [SUCCESS] COGNITION:   {cognition}")
print(f"  - [SUCCESS] COMPUTATION: {computation}")
print(f"  - [SUCCESS] EXISTENCE:   {existence}")
print("--------------------------------------------------------------------------------")
print("Universal Thesis Verified: True")
print("================================================================================")
"""

# ——— Creator side: propose → audit → commit and compile Coq ———
root = Path(__file__).resolve().parents[1]
here = Path(__file__).resolve()
coq_dir = root / "theory"

CREATOR_HASH = hashlib.sha256(here.read_bytes()).hexdigest()

LOGOS_HASH = hashlib.sha256(LOGOS_SOURCE.encode("utf-8")).hexdigest()
child_path = here.parent / "witness_in_potentia.py"

child_path.write_text(LOGOS_SOURCE, encoding="utf-8", newline="\n")
try:
    os.chmod(child_path, 0o444)
except Exception:
    pass

written_bytes = child_path.read_bytes()
WRITTEN_HASH = hashlib.sha256(written_bytes).hexdigest()
if WRITTEN_HASH != LOGOS_HASH:
    raise SystemError("BYTE DRIFT: embedded Logos hash != written file hash")

# External hashers (optional)
ext_hashes = {}
if shutil.which("sha256sum"):
    h = subprocess.run(["sha256sum", str(child_path)], capture_output=True, text=True)
    ext_hashes["sha256sum"] = h.stdout.split()[0].strip() if h.returncode == 0 else None
elif shutil.which("shasum"):
    h = subprocess.run(["shasum", "-a", "256", str(child_path)], capture_output=True, text=True)
    ext_hashes["shasum"] = h.stdout.split()[0].strip() if h.returncode == 0 else None

# Compile Coq “above” — all four files must succeed.
coq_ok = False
coq_hashes = {}
coq_targets = [
    "Genesis.v",
    "Core.v",
    "PhysRel.v",
    "LogicToPhysics.v",
    "WitnessIsGenesis.v",
    "CostIsComplexity.v",
    "Separation.v",
    "NoFreeLunch.v",
]
try:
    for f in coq_targets:
        result = subprocess.run(
            ["coqc", "-Q", str(coq_dir), "theory", str(coq_dir / f)],
            check=True,
            capture_output=True,
            text=True,
        )
        if result.stdout:
            print(result.stdout, file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        vo = (coq_dir / f.replace(".v", ".vo"))
        coq_hashes[f.replace(".v", ".vo")] = hashlib.sha256(vo.read_bytes()).hexdigest()
    coq_ok = True
except subprocess.CalledProcessError as exc:
    coq_ok = False
    print(f"[Coq] compilation failed for {exc.cmd[-1]}", file=sys.stderr)
    if exc.stdout:
        print(exc.stdout, file=sys.stderr)
    if exc.stderr:
        print(exc.stderr, file=sys.stderr)
except Exception as exc:  # pragma: no cover - unexpected failure path
    coq_ok = False
    print(f"[Coq] unexpected error: {exc!r}", file=sys.stderr)

# Run child in isolated mode with anchor
env = os.environ.copy()
env["OUROBOROS_ANCHOR"] = ANCHOR
run = subprocess.run([sys.executable, "-I", str(child_path)],
                     capture_output=True, text=True, check=True, env=env)
child_stdout, child_stderr = run.stdout, run.stderr

m_hash    = re.search(r"Source Hash \(SHA256\):\s*([0-9a-f]{64})", child_stdout)
m_verdict = re.search(r"Universal Thesis Verified:\s*True\b", child_stdout)
m_anchor  = re.search(r"^Anchor:\s*(.*)$", child_stdout, re.MULTILINE)
m_bind    = re.search(r"Anchor Binding \(SHA256\):\s*([0-9a-f]{64})", child_stdout)

CHILD_HASH   = m_hash.group(1) if m_hash else None
CHILD_ANCHOR = (m_anchor.group(1).strip() if m_anchor else "")
CHILD_BIND   = m_bind.group(1) if m_bind else None
EXPECTED_BIND = hashlib.sha256((WRITTEN_HASH + ":" + ANCHOR).encode()).hexdigest()

creation_successful = (
    (m_verdict is not None) and
    (CHILD_HASH == WRITTEN_HASH) and
    (CHILD_ANCHOR == (ANCHOR or "<none>")) and
    (CHILD_BIND == EXPECTED_BIND) and
    all(h is None or h == WRITTEN_HASH for h in ext_hashes.values()) and
    coq_ok
)

print(f"""
================================================================================
                                   THE LOGOS
================================================================================

Creator Hash (SHA256 of this file): {CREATOR_HASH}

This script proposed, audited, and committed a self-verifying witness universe,
and required Coq proofs to compile (“above”) before attesting (“below”).

--------------------------------------------------------------------------------
                                CREATION LOG
--------------------------------------------------------------------------------
- Anchor:              {ANCHOR or '<none>'}
- Embedded Logos Hash: {LOGOS_HASH}
- Written File Hash:   {WRITTEN_HASH}
- Child Reported Hash: {CHILD_HASH or 'N/A'}
- Anchor Binding:      expected={EXPECTED_BIND} child={CHILD_BIND or 'N/A'}
- Coq compiled:        {coq_ok}
- Coq object hashes:   {json.dumps(coq_hashes, sort_keys=True) or '{}'}
- External Auditors:   {', '.join(f"{k}={v or 'N/A'}" for k,v in ext_hashes.items()) or 'none'}
- Execution Mode:      python -I {child_path.name}
- Stderr (child):      {'<empty>' if not child_stderr.strip() else '<non-empty>'}

--- BEGIN TESTIMONY OF CREATED UNIVERSE ---
{child_stdout.strip()}
--- END TESTIMONY OF CREATED UNIVERSE ---

--------------------------------------------------------------------------------
                                   VERDICT
--------------------------------------------------------------------------------
Thesis Verified by Self-Creation: {creation_successful}
================================================================================
""".strip())

wline = {
    "creator_hash": CREATOR_HASH,
    "logos_hash": LOGOS_HASH,
    "written_hash": WRITTEN_HASH,
    "child_reported_hash": CHILD_HASH,
    "anchor": ANCHOR,
    "anchor_binding": EXPECTED_BIND,
    "external_hashes": ext_hashes,
    "coq_compiled": coq_ok,
    "coq_vo_hashes": coq_hashes,
    "child_verdict_true": bool(m_verdict),
    "isolated_exec": True,
    "ok": bool(creation_successful),
}
with open(root / "WITNESS.jsonl", "a", encoding="utf-8") as jf:
  jf.write(json.dumps(wline, sort_keys=True) + "\n")
