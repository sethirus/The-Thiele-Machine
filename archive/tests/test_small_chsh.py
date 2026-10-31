"""CHSH as an earned check on the small machine compiles, with exactly the
assumptions it should have.

coq/kernel/quantum/SmallChshCheck.v (the integer check and its meaning) and
SmallChshMachine.v (the check as the CHECK of an earned chain on the machine
of minimal/EarnedMulti.v) are compiled with plain coqc together with the
quantum files they import. The meaning is stated over the real numbers, so
every theorem except the tally round trip prints the three real-number
axioms of the Coq standard library (and nothing else); the round trip is
closed. The exact counts below fail if a theorem gains an assumption, loses
its receipt, or is added without one.
"""

import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
QUANTUM = REPO_ROOT / "coq" / "kernel" / "quantum"
MINIMAL = REPO_ROOT / "minimal"

KERNEL_FILES = (
    "ConstructivePSD.v",
    "NPAMomentMatrix.v",
    "TsirelsonFromAlgebra.v",
    "SmallChshCheck.v",
    "SmallChshMachine.v",
)
MINIMAL_FILES = ("EarnedGeneric.v", "EarnedMulti.v")

# (closed receipts, receipts that list axioms) printed by each new file.
EXPECTED = {
    "SmallChshCheck.v": (0, 5),
    "SmallChshMachine.v": (1, 12),
}
ALLOWED_AXIOMS = {
    "ClassicalDedekindReals.sig_not_dec",
    "ClassicalDedekindReals.sig_forall_dec",
    "FunctionalExtensionality.functional_extensionality_dep",
}


def axiom_names(output: str) -> tuple[int, set[str]]:
    """Number of Axioms: blocks and the set of axiom names they list."""
    blocks = 0
    names: set[str] = set()
    inside = False
    for line in output.splitlines():
        if line.startswith("Axioms:"):
            blocks += 1
            inside = True
        elif line.startswith("Closed under the global context"):
            inside = False
        elif inside and line and not line[0].isspace():
            names.add(line.split()[0])
    return blocks, names


@pytest.mark.coq
def test_small_chsh_compiles_with_only_the_real_number_axioms(tmp_path):
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    (tmp_path / "kernel").mkdir()
    (tmp_path / "minimal").mkdir()
    for name in KERNEL_FILES:
        (tmp_path / "kernel" / name).write_text((QUANTUM / name).read_text())
    for name in MINIMAL_FILES:
        (tmp_path / "minimal" / name).write_text((MINIMAL / name).read_text())
    outputs: dict[str, str] = {}
    steps = [("minimal", n) for n in MINIMAL_FILES] + [("kernel", n) for n in KERNEL_FILES]
    for directory, name in steps:
        proc = subprocess.run(
            ["coqc", "-Q", "kernel", "Kernel", "-Q", "minimal", "Minimal",
             f"{directory}/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=1800,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        outputs[name] = proc.stdout
    for name, (closed, with_axioms) in EXPECTED.items():
        out = outputs[name]
        assert out.count("Closed under the global context") == closed, out
        blocks, names = axiom_names(out)
        assert blocks == with_axioms, out
        assert names <= ALLOWED_AXIOMS, f"{name} uses {sorted(names - ALLOWED_AXIOMS)}"
