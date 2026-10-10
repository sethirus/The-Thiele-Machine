"""Keep the front-door artifact honest: minimal/MuCore.v has to stay minimal,
green, and axiom-free, because it's the first thing I ask anyone to compile
before reading a word of prose.

If it ever stops building from a clean checkout, or any theorem quietly stops
being closed under the global context, the whole "don't take my word, run it"
pitch breaks and nobody notices. So this test notices. Same job for
minimal/nofi_demo.py, the clean-room measurement that re-derives the floor
with no Thiele code in the room.
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
MUCORE = REPO_ROOT / "minimal" / "MuCore.v"
EARNED = REPO_ROOT / "minimal" / "EarnedCore.v"
UNIVERSAL = REPO_ROOT / "minimal" / "UniversalThiele.v"
GENERIC = REPO_ROOT / "minimal" / "EarnedGeneric.v"
COMPLETE = REPO_ROOT / "minimal" / "ThieleComplete.v"
WINDOW = REPO_ROOT / "minimal" / "ThieleCompleteWindow.v"
MULTI = REPO_ROOT / "minimal" / "EarnedMulti.v"
CODES = REPO_ROOT / "minimal" / "UniversalCodes.v"
NOCOPY = REPO_ROOT / "minimal" / "UniversalNoCopy.v"
DEMO = REPO_ROOT / "minimal" / "nofi_demo.py"
EXPECTED_CLOSED = 10
EARNED_EXPECTED_CLOSED = 33
UNIVERSAL_EXPECTED_CLOSED = 22
GENERIC_EXPECTED_CLOSED = 31
COMPLETE_EXPECTED_CLOSED = 35
WINDOW_EXPECTED_CLOSED = 10
MULTI_EXPECTED_CLOSED = 37
CODES_EXPECTED_CLOSED = 27
NOCOPY_EXPECTED_CLOSED = 6


def test_nofi_demo_self_checks():
    proc = subprocess.run(
        [sys.executable, str(DEMO)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "all 9 checks passed" in proc.stdout
    # The three claims the demo's sections make, visible in its own output:
    # the exhaustive sweep found nothing, the conservation identity held
    # everywhere, and the under-floor strategy paid in errors.
    assert "zero counterexamples" in proc.stdout
    assert "on every instance" in proc.stdout
    assert "discount is paid in errors" in proc.stdout


@pytest.mark.coq
def test_minimal_core_compiles_axiom_free(tmp_path):
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "MuCore.v"
    work.write_text(MUCORE.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == EXPECTED_CLOSED, (
        f"expected {EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_earned_core_compiles_axiom_free(tmp_path):
    """minimal/EarnedCore.v, the smallest machine that earns its commitments,
    compiles with plain coqc against the standard library alone, and every
    theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "EarnedCore.v"
    work.write_text(EARNED.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == EARNED_EXPECTED_CLOSED, (
        f"expected {EARNED_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_universal_thiele_compiles_axiom_free(tmp_path):
    """minimal/UniversalThiele.v, the host that runs any small-machine program
    as a guest and enforces the guest's record and toll in its own step,
    compiles with plain coqc against EarnedCore.v and the standard library,
    and every theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "UniversalThiele.v").write_text(UNIVERSAL.read_text())
    for name in ("EarnedCore.v", "UniversalThiele.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == UNIVERSAL_EXPECTED_CLOSED, (
        f"expected {UNIVERSAL_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_earned_generic_compiles_axiom_free(tmp_path):
    """minimal/EarnedGeneric.v, the small machine over any property language
    with a checker proved equal to its meaning, including a "sorted" check on
    a list encoded in a counter, compiles with plain coqc against the
    standard library alone, and every theorem it prints assumptions for is
    closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    work = tmp_path / "EarnedGeneric.v"
    work.write_text(GENERIC.read_text())
    proc = subprocess.run(
        ["coqc", str(work)],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == GENERIC_EXPECTED_CLOSED, (
        f"expected {GENERIC_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_thiele_complete_compiles_axiom_free(tmp_path):
    """minimal/ThieleComplete.v, the strong definition of a Thiele-complete
    machine (universal base, earned record, exact toll, a check that can
    fail), with the small machine proved to meet it and every clock machine
    proved to fail it, compiles with plain coqc against EarnedCore.v,
    EarnedGeneric.v and the standard library, and every theorem it prints
    assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "EarnedGeneric.v").write_text(GENERIC.read_text())
    (lib / "ThieleComplete.v").write_text(COMPLETE.read_text())
    for name in ("EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == COMPLETE_EXPECTED_CLOSED, (
        f"expected {COMPLETE_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout



@pytest.mark.coq
def test_thiele_complete_window_compiles_axiom_free(tmp_path):
    """minimal/ThieleCompleteWindow.v, the proof that every Thiele-complete
    machine keeps its record and its ledger out of its base window (two runs
    from one clean start end in the same window, one certified and one
    not, with ledgers at least 3 apart, so no function of the window gives
    either), compiles with plain coqc against EarnedCore.v,
    EarnedGeneric.v, ThieleComplete.v and the standard library, and every
    theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "EarnedGeneric.v").write_text(GENERIC.read_text())
    (lib / "ThieleComplete.v").write_text(COMPLETE.read_text())
    (lib / "ThieleCompleteWindow.v").write_text(WINDOW.read_text())
    for name in (
        "EarnedCore.v",
        "EarnedGeneric.v",
        "ThieleComplete.v",
        "ThieleCompleteWindow.v",
    ):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == WINDOW_EXPECTED_CLOSED, (
        f"expected {WINDOW_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}"
        + chr(10)
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout

@pytest.mark.coq
def test_earned_multi_compiles_axiom_free(tmp_path):
    """minimal/EarnedMulti.v, the small machine of EarnedGeneric.v with a
    counter for every natural number, the host the universal program U runs
    on, compiles with plain coqc against the standard library alone, and
    every theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedMulti.v").write_text(MULTI.read_text())
    for name in ("EarnedMulti.v",):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == MULTI_EXPECTED_CLOSED, (
        f"expected {MULTI_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_universal_codes_compiles_axiom_free(tmp_path):
    """minimal/UniversalCodes.v, the numbers that write a guest program, its
    properties and its claims into host counters, and the one host property
    PSlot, compiles with plain coqc against EarnedCore.v, EarnedGeneric.v,
    EarnedMulti.v and the standard library, and every theorem it prints
    assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "EarnedGeneric.v").write_text(GENERIC.read_text())
    (lib / "EarnedMulti.v").write_text(MULTI.read_text())
    (lib / "UniversalCodes.v").write_text(CODES.read_text())
    for name in ("EarnedCore.v", "EarnedGeneric.v", "EarnedMulti.v", "UniversalCodes.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == CODES_EXPECTED_CLOSED, (
        f"expected {CODES_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_universal_no_copy_compiles_axiom_free(tmp_path):
    """minimal/UniversalNoCopy.v, the pigeonhole lemma that rules out keeping
    host facts on an exact copy of the guest counter, compiles with plain
    coqc against EarnedCore.v, EarnedMulti.v and the standard library, and
    every theorem it prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    (lib / "EarnedCore.v").write_text(EARNED.read_text())
    (lib / "EarnedMulti.v").write_text(MULTI.read_text())
    (lib / "UniversalNoCopy.v").write_text(NOCOPY.read_text())
    for name in ("EarnedCore.v", "EarnedMulti.v", "UniversalNoCopy.v"):
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=600,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == NOCOPY_EXPECTED_CLOSED, (
        f"expected {NOCOPY_EXPECTED_CLOSED} closed-assumption receipts, saw {closed}\n"
        + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


MINIMAL_DIR = REPO_ROOT / "minimal"
PRICED_EXPECTED_CLOSED = 48
PRICED_COMPLETE_EXPECTED_CLOSED = 7
PRESENTED_EXPECTED_CLOSED = 23
MULTI_PRICED_EXPECTED_CLOSED = 40


def _compile_chain_expect_closed(tmp_path, names, expected):
    """Compile minimal/<names> in order with plain coqc and require that the
    last file prints exactly `expected` closed-assumption receipts and no
    axiom list."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in names:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    proc = None
    for name in names:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
    closed = proc.stdout.count("Closed under the global context")
    assert closed == expected, (
        f"expected {expected} closed-assumption receipts, saw {closed}\n" + proc.stdout
    )
    assert "Axioms:" not in proc.stdout


@pytest.mark.coq
def test_earned_priced_compiles_axiom_free(tmp_path):
    """minimal/EarnedPriced.v, the generic small machine with the paid move
    PAY, compiles with plain coqc against EarnedGeneric.v and the standard
    library, and every theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, ("EarnedGeneric.v", "EarnedPriced.v"), PRICED_EXPECTED_CLOSED
    )


@pytest.mark.coq
def test_priced_complete_compiles_axiom_free(tmp_path):
    """minimal/PricedComplete.v, the priced machine as a Thiele-complete
    machine, compiles with plain coqc against EarnedCore.v, EarnedGeneric.v,
    ThieleComplete.v, EarnedPriced.v and the standard library, and every
    theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path,
        ("EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "EarnedPriced.v",
         "PricedComplete.v"),
        PRICED_COMPLETE_EXPECTED_CLOSED,
    )


@pytest.mark.coq
def test_presented_compiles_axiom_free(tmp_path):
    """minimal/Presented.v, a computably presented Thiele machine and the
    surcharge of the priced host that runs it, compiles with plain coqc
    against the files it imports and the standard library, and every theorem
    it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path,
        ("EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "EarnedPriced.v",
         "Presented.v"),
        PRESENTED_EXPECTED_CLOSED,
    )


@pytest.mark.coq
def test_earned_multi_priced_compiles_axiom_free(tmp_path):
    """minimal/EarnedMultiPriced.v, the machine with a counter for every
    number and the paid move PAY, the host of the priced universal program,
    compiles with plain coqc against the standard library alone, and every
    theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, ("EarnedMultiPriced.v",), MULTI_PRICED_EXPECTED_CLOSED
    )


ENTITLEMENT_EXPECTED_CLOSED = 32
FRAGMENT_EXPECTED_CLOSED = 23
VERIFIER_EXPECTED_CLOSED = 17
SMALL_MACHINE_BASE = ("EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v")


@pytest.mark.coq
def test_entitlement_small_compiles_axiom_free(tmp_path):
    """minimal/EntitlementSmall.v, structural entitlement stated on the model
    and run on the small machine, compiles with plain coqc against
    ThieleComplete.v and the files it needs, and every theorem it prints
    assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, SMALL_MACHINE_BASE + ("EntitlementSmall.v",), ENTITLEMENT_EXPECTED_CLOSED
    )


@pytest.mark.coq
def test_fragment_small_compiles_axiom_free(tmp_path):
    """minimal/FragmentSmall.v, the finite fragment that pays for its merges,
    run by the small machine, compiles with plain coqc against
    ThieleComplete.v and the files it needs, and every theorem it prints
    assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, SMALL_MACHINE_BASE + ("FragmentSmall.v",), FRAGMENT_EXPECTED_CLOSED
    )


@pytest.mark.coq
def test_verifier_small_compiles_axiom_free(tmp_path):
    """minimal/VerifierSmall.v, the verifier corollary for every
    Thiele-complete machine, compiles with plain coqc against
    ThieleComplete.v, ThieleCompleteWindow.v, EntitlementSmall.v and the
    files they need, and every theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path,
        SMALL_MACHINE_BASE
        + ("ThieleCompleteWindow.v", "EntitlementSmall.v", "VerifierSmall.v"),
        VERIFIER_EXPECTED_CLOSED,
    )


HOST_BLOCKS_EXPECTED_CLOSED = 7
SM_CODES_EXPECTED_CLOSED = 2
SM_INTERP_EXPECTED_CLOSED = 3
HOST_BASE = ("EarnedCore.v", "EarnedGeneric.v", "EarnedMulti.v", "UniversalCodes.v")


@pytest.mark.coq
def test_sm_host_blocks_compiles_axiom_free(tmp_path):
    """minimal/SmHostBlocks.v, host semantics on one input and the relocated
    blocks that Rice's and Kleene's theorems on the host are built from,
    compiles with plain coqc against EarnedMulti.v and the standard library,
    and every theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, ("EarnedMulti.v", "SmHostBlocks.v"), HOST_BLOCKS_EXPECTED_CLOSED
    )


@pytest.mark.coq
def test_sm_codes_compiles_axiom_free(tmp_path):
    """minimal/SmCodes.v, numbers for the programs of the host machine,
    compiles with plain coqc against the host files and the standard
    library, and every theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path, HOST_BASE + ("SmHostBlocks.v", "SmCodes.v"), SM_CODES_EXPECTED_CLOSED
    )


@pytest.mark.coq
def test_sm_interp_compiles_axiom_free(tmp_path):
    """minimal/SmInterp.v, the host interpreter on plain data and its two
    evaluators, compiles with plain coqc against the host files and the
    standard library, and every theorem it prints assumptions for is
    closed."""
    _compile_chain_expect_closed(
        tmp_path,
        HOST_BASE + ("SmHostBlocks.v", "SmCodes.v", "SmInterp.v"),
        SM_INTERP_EXPECTED_CLOSED,
    )


SM_TALLY_EXPECTED_CLOSED = 5
SM_LOOPS_CHAIN = HOST_BASE + ("SmHostBlocks.v", "SmLoops.v", "SmLoops2.v", "SmLoops3.v")
SM_LOOPS_EXPECTED_CLOSED = {"SmLoops.v": 2, "SmLoops2.v": 2, "SmLoops3.v": 4}


@pytest.mark.coq
def test_sm_tally_compiles_axiom_free(tmp_path):
    """minimal/SmTally.v, the record of a stopped host program as five numbers
    and the evaluator that reports one of them, compiles with plain coqc
    against the host files and the standard library, and every theorem it
    prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path,
        HOST_BASE + ("SmHostBlocks.v", "SmCodes.v", "SmInterp.v", "SmTally.v"),
        SM_TALLY_EXPECTED_CLOSED,
    )


@pytest.mark.coq
def test_sm_loops_compile_axiom_free(tmp_path):
    """minimal/SmLoops.v, SmLoops2.v and SmLoops3.v, counting loops on the
    host machine with instructions in their bodies (the fan, check, commit and
    certify loops), compile with plain coqc against the host files and the
    standard library, and every theorem each one prints assumptions for is
    closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in SM_LOOPS_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in SM_LOOPS_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in SM_LOOPS_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == SM_LOOPS_EXPECTED_CLOSED[name], (
                f"{name}: expected {SM_LOOPS_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout


# Entitlement leftovers on the small machine: the eight ent2_ files, in
# dependency order, with the closed-assumption receipts each one prints.
ENT2_CHAIN = (
    "EarnedCore.v", "EarnedGeneric.v", "EarnedMulti.v", "ThieleComplete.v",
    "EntitlementSmall.v", "FragmentSmall.v", "MultiThiele2.v", "BitSearch2.v",
    "EntitlementMore2.v", "BitSearchMember2.v", "BitSearchObserved2.v",
    "CompressionSmall2.v", "TimeTax2.v", "CoveringNeeded2.v",
)
ENT2_EXPECTED_CLOSED = {
    "MultiThiele2.v": 6,
    "BitSearch2.v": 8,
    "EntitlementMore2.v": 20,
    "BitSearchMember2.v": 15,
    "BitSearchObserved2.v": 4,
    "CompressionSmall2.v": 18,
    "TimeTax2.v": 18,
    "CoveringNeeded2.v": 3,
}


@pytest.mark.coq
def test_entitlement_leftovers_compile_axiom_free(tmp_path):
    """The eight minimal/*2.v files (the multi-register host as a
    Thiele-complete machine, the n-bit search, the weighted, partition and
    observational forms of entitlement, the compression route, the time tax
    and the covering counterexample) compile with plain coqc against the
    standard library and the small-machine files, and every theorem each one
    prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in ENT2_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in ENT2_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in ENT2_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == ENT2_EXPECTED_CLOSED[name], (
                f"{name}: expected {ENT2_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout


# The merge on the small machine itself, record-layer merge pricing, and the
# independence of the four Thiele-complete clauses.
BRIDGE_CHAIN = (
    "EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "FragmentSmall.v",
    "RecordMerge.v", "ThieleCompleteIndependent.v",
)
BRIDGE_EXPECTED_CLOSED = {
    "RecordMerge.v": 12,
    "ThieleCompleteIndependent.v": 13,
}


@pytest.mark.coq
def test_record_merge_and_clause_independence_compile_axiom_free(tmp_path):
    """RecordMerge.v (CERTIFY and COMMIT merge on the small machine, and the
    toll from record-layer merge pricing with no finiteness premise) and
    ThieleCompleteIndependent.v (each Thiele-complete clause fails on a
    machine meeting the other three) compile with plain coqc, and every
    theorem they print assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in BRIDGE_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in BRIDGE_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in BRIDGE_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == BRIDGE_EXPECTED_CLOSED[name], (
                f"{name}: expected {BRIDGE_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout


NEC_CHAIN = (
    "EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "EntitlementSmall.v",
    "EntitlementMore2.v", "NecEEnt.v", "EarnedMulti.v", "MultiThiele2.v",
    "BitSearch2.v", "BitSearchMember2.v", "TimeTax2.v", "NecESearch.v",
    "NecSClean.v", "NecSChain.v", "UniversalThiele.v", "NecSHost.v",
    "UniversalNoCopy.v", "NecSNoCopy.v", "NecSWindow.v", "NecTEarned.v",
    "NecTGeneric.v", "NecTLoop.v", "NecTLoose.v", "NecTPartition.v",
    "NecTToll.v", "NecTUnclean.v", "ThieleCompleteWindow.v", "VerifierSmall.v",
    "NecTVerifier.v",
)
NEC_EXPECTED_CLOSED = {
    "NecEEnt.v": 27,
    "NecESearch.v": 4,
    "NecSClean.v": 21,
    "NecSChain.v": 2,
    "NecSHost.v": 13,
    "NecSNoCopy.v": 4,
    "NecSWindow.v": 16,
    "NecTEarned.v": 2,
    "NecTGeneric.v": 6,
    "NecTLoop.v": 2,
    "NecTLoose.v": 4,
    "NecTPartition.v": 7,
    "NecTToll.v": 4,
    "NecTUnclean.v": 1,
    "NecTVerifier.v": 3,
}


@pytest.mark.coq
def test_necessity_files_in_minimal_compile_axiom_free(tmp_path):
    """The fifteen necessity files that stand on the small machine alone
    (counterexamples that drop one premise of a small-machine theorem, the
    exact toll and floor, the window oracle, the n-bit search) compile with
    plain coqc against the standard library and the small-machine files, and
    every theorem each one prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in NEC_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in NEC_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in NEC_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == NEC_EXPECTED_CLOSED[name], (
                f"{name}: expected {NEC_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout
    assert set(NEC_EXPECTED_CLOSED) == {
        p.name for p in MINIMAL_DIR.glob("Nec*.v")
    }, "every minimal/Nec*.v file needs an expected count"


AXIS_DG_BLOCK_EXPECTED_CLOSED = 4


@pytest.mark.coq
def test_axis_diagonal_blocks_compile_axiom_free(tmp_path):
    """minimal/AxDgBlock.v, the block lemmas of the content diagonal (a block
    runs the same when the versions of the registers are shifted by a fixed
    amount), compiles with plain coqc against the host files and the standard
    library, and every theorem it prints assumptions for is closed."""
    _compile_chain_expect_closed(
        tmp_path,
        ("EarnedCore.v", "EarnedGeneric.v", "EarnedMulti.v", "UniversalCodes.v",
         "SmHostBlocks.v", "AxDgBlock.v"),
        AXIS_DG_BLOCK_EXPECTED_CLOSED,
    )


TC_MINIMAL_CHAIN = (
    "EarnedCore.v", "TcBlocks.v", "Tc2Am.v", "Tc2Forced.v", "Tc2Stage.v",
    "Tc2Chain.v", "Tc2Collision.v", "Tc2Embed.v", "Tc2Mult.v",
)
TC_MINIMAL_EXPECTED_CLOSED = {
    "TcBlocks.v": 0,
    "Tc2Am.v": 3,
    "Tc2Forced.v": 2,
    "Tc2Stage.v": 1,
    "Tc2Chain.v": 4,
    "Tc2Collision.v": 4,
    "Tc2Embed.v": 1,
    "Tc2Mult.v": 1,
}


@pytest.mark.coq
def test_two_counter_minimal_files_compile_axiom_free(tmp_path):
    """The block lemmas of the two-counter Rice theorem (TcBlocks.v) and the
    seven Tc2 files (the collision and slaving lemmas of a program that adds a
    constant, the abstract tame machines, the stage recursion, the chain
    argument, the embedding of the small machine, and the theorem that no
    program multiplies every input by a number coprime to every small number)
    compile with plain coqc against EarnedCore.v and the standard library, and
    every theorem each one prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in TC_MINIMAL_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in TC_MINIMAL_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in TC_MINIMAL_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == TC_MINIMAL_EXPECTED_CLOSED[name], (
                f"{name}: expected {TC_MINIMAL_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout


LIFT_MINIMAL_CHAIN = (
    "EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "LiftPigeon.v",
    "LiftCore.v", "LiftConverse.v", "LiftOneCounter.v",
)
LIFT_MINIMAL_EXPECTED_CLOSED = {
    "LiftPigeon.v": 0,
    "LiftCore.v": 2,
    "LiftConverse.v": 7,
    "LiftOneCounter.v": 3,
}


@pytest.mark.coq
def test_lifting_minimal_files_compile_axiom_free(tmp_path):
    """The lifting of any universal base to a Thiele-complete machine
    (LiftCore.v), the converse and the counterexamples (LiftConverse.v), the
    pigeonhole principle (LiftPigeon.v) and the decision procedure for one
    counter (LiftOneCounter.v) compile with plain coqc against
    ThieleComplete.v and the standard library, and every theorem each one
    prints assumptions for is closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in LIFT_MINIMAL_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in LIFT_MINIMAL_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in LIFT_MINIMAL_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == LIFT_MINIMAL_EXPECTED_CLOSED[name], (
                f"{name}: expected {LIFT_MINIMAL_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout


COMPOSE_MINIMAL_CHAIN = (
    "EarnedCore.v", "EarnedGeneric.v", "ThieleComplete.v", "CzLink.v", "CzShared.v",
)
COMPOSE_MINIMAL_EXPECTED_CLOSED = {"CzLink.v": 5, "CzShared.v": 3}


@pytest.mark.coq
def test_composition_minimal_files_compile_axiom_free(tmp_path):
    """The abstract nesting of driven systems by simulation (CzLink.v: links
    compose, towers keep the record and add surcharges) and the shared-resource
    counterexample on the small machine (CzShared.v: composition keeps the
    earned order only when the parts do not change what each other's claims
    are about) compile with plain coqc against ThieleComplete.v and the
    standard library, and every theorem each one prints assumptions for is
    closed."""
    if shutil.which("coqc") is None:
        pytest.skip("coqc not available")
    lib = tmp_path / "minimal"
    lib.mkdir()
    for name in COMPOSE_MINIMAL_CHAIN:
        (lib / name).write_text((MINIMAL_DIR / name).read_text())
    for name in COMPOSE_MINIMAL_CHAIN:
        proc = subprocess.run(
            ["coqc", "-Q", "minimal", "Minimal", f"minimal/{name}"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=900,
        )
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if name in COMPOSE_MINIMAL_EXPECTED_CLOSED:
            closed = proc.stdout.count("Closed under the global context")
            assert closed == COMPOSE_MINIMAL_EXPECTED_CLOSED[name], (
                f"{name}: expected {COMPOSE_MINIMAL_EXPECTED_CLOSED[name]} closed-assumption "
                f"receipts, saw {closed}\n" + proc.stdout
            )
            assert "Axioms:" not in proc.stdout
