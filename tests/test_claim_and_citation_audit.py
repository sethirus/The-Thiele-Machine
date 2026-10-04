"""Checks that the citation audit resolves every cited Coq name and that the maintained
documents state each result at its proved scope."""

from pathlib import Path
import sys

from scripts import audit_monograph_citations as citations


ROOT = Path(__file__).resolve().parents[1]


def audit_rules():
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import inquisitor
        return inquisitor
    finally:
        sys.path.pop(0)


def test_inline_inductive_constructors_are_indexed(tmp_path, monkeypatch):
    monkeypatch.setattr(citations, "REPO", tmp_path)
    (tmp_path / "Small.v").write_text(
        "Inductive Small := First | Second | Third.\n"
        "Definition choose (x : Small) := match x with First => true | _ => false end.\n"
    )
    names = citations.find_top_level_decls([tmp_path])
    assert {"First", "Second", "Third"} <= names.keys()
    assert "_" not in names


def test_examples_class_fields_and_module_stems_are_indexed(tmp_path, monkeypatch):
    monkeypatch.setattr(citations, "REPO", tmp_path)
    source = tmp_path / "NamedModule.v"
    source.write_text(
        "Class Interface : Type := { required_fact : True }.\n"
        "Example computed_example : True. Proof. exact I. Qed.\n"
    )
    names = citations.find_top_level_decls([tmp_path])
    assert {"NamedModule", "Interface", "required_fact", "computed_example"} <= names.keys()


def test_external_quote_command_and_stdlib_axiom_are_classified():
    assert {"TPM2_Quote", "classic"} <= citations.NON_COQ_TOKENS


def test_vendored_halting_citation_requires_its_source(tmp_path, monkeypatch):
    monkeypatch.setattr(citations, "REPO", tmp_path)
    root = tmp_path / "coq"
    root.mkdir()
    assert "MM2_HALTING_undec" not in citations.find_top_level_decls([root])
    source = tmp_path / "vendor/coq-undecidability/theories/MinskyMachines/MM2_undec.v"
    source.parent.mkdir(parents=True)
    source.write_text(
        "(* Lemma invented_result : True. *)\n"
        "Lemma MM2_HALTING_undec : undecidable MM2_HALTING.\n"
    )
    found = citations.find_top_level_decls([root])
    assert "MM2_HALTING_undec" in found
    assert "invented_result" not in found


def test_latex_code_macro_is_audited_as_a_citation():
    assert citations.extract_texttt_citations(r"\code{named\_theorem}") == [
        ("named_theorem", 1)
    ]


def test_plaintext_backticks_are_audited_as_citations(tmp_path):
    path = tmp_path / "claims.txt"
    path.write_text("The result is `named_theorem`.\n")
    assert citations.extract_citations(path) == [("named_theorem", 1)]


def test_removed_latex_theorem_is_reported(tmp_path, monkeypatch):
    monkeypatch.setattr(citations, "REPO", tmp_path)
    path = tmp_path / "claims.tex"
    path.write_text(r"The result is \code{removed\_theorem}." + "\n")
    report = citations.audit(path, {}, {})
    assert report["missing_idents"] == [("removed_theorem", 1)]


def test_all_maintained_claim_documents_resolve():
    declarations = citations.find_top_level_decls(citations.COQ_ROOTS)
    files = citations.find_files_by_basename(citations.COQ_ROOTS)
    documents = [
        ROOT / "README.md",
        ROOT / "TECHNICAL_DISCLOSURE.md",
        ROOT / "THIELE_MACHINE.txt",
        ROOT / "monograph/monograph.tex",
        ROOT / "monograph/thiele_machine_math_spec.tex",
    ]
    failures = {}
    for path in documents:
        report = citations.audit(path, declarations, files)
        missing = {
            key: report[key]
            for key in ("missing_files", "missing_idents", "missing_opcodes")
            if report[key]
        }
        if missing:
            failures[str(path.relative_to(ROOT))] = missing
    assert not failures, f"unresolved maintained-document citations: {failures}"


def test_commitment_contract_has_no_field_projection_theorems():
    findings = audit_rules().scan_self_referential_record(
        ROOT / "coq/VerifierEscape_Hardness.v"
    )
    assert not findings, [finding.message for finding in findings]


def test_recursion_development_has_no_mislabelled_invariance():
    findings = audit_rules().scan_definitional_invariance(
        ROOT / "coq/kernel/foundation/LRecursion.v"
    )
    assert not findings, [finding.message for finding in findings]


def test_retired_theorem_names_are_not_still_cited():
    retired = {
        "hardness_escape_succeeds",
        "honest_commitments_are_binding",
        "forgeable_commitment_breaks_hardness",
        "transparency_log_escape",
        "log_free_verifier_impossible",
        "split_view_witness",
        "partition_ops_cannot_cost",
        "observer_narrowing_is_free",
        "five_disciplines_are_pointers",
        "deniable_authentication_refutes_strong_criterion",
        "mac_refutes_strong_criterion",
        "capability_refutes_strong_criterion",
        "public_log_confirms",
    }
    documents = [
        ROOT / "README.md",
        ROOT / "TECHNICAL_DISCLOSURE.md",
        ROOT / "THIELE_MACHINE.txt",
        ROOT / "monograph/monograph.tex",
        ROOT / "monograph/thiele_machine_math_spec.tex",
        ROOT / "docs/THEOREM_MEANINGS.md",
    ]
    found = {
        name: [
            str(path.relative_to(ROOT))
            for path in documents
            if name in path.read_text().replace(r"\_", "_")
        ]
        for name in retired
    }
    found = {name: paths for name, paths in found.items() if paths}
    assert not found, f"retired theorem citations remain: {found}"


def test_commitment_contract_is_not_described_as_a_hardness_result():
    documents = [
        ROOT / "README.md",
        ROOT / "TECHNICAL_DISCLOSURE.md",
        ROOT / "THIELE_MACHINE.txt",
        ROOT / "monograph/monograph.tex",
        ROOT / "monograph/thiele_machine_math_spec.tex",
        ROOT / "docs/THEOREM_MEANINGS.md",
        ROOT / "coq/VerifierEscape_Hardness.v",
    ]
    forbidden = ("hardness hypothesis", "weaker soundness guarantee")
    found = {
        str(path.relative_to(ROOT)): [phrase for phrase in forbidden if phrase in path.read_text()]
        for path in documents
    }
    found = {path: phrases for path, phrases in found.items() if phrases}
    assert not found, f"commitment contract is still mislabeled as hardness: {found}"


def test_mu_cost_file_does_not_claim_to_derive_the_vm_schedule():
    source = (ROOT / "coq/kernel/mu_calculus/MuCostDerivation.v").read_text()
    forbidden = [
        "delta MUST equal",
        "parameters are not arbitrary",
        "For LASSERT: mu_delta =",
        "For PNEW/PSPLIT/PMERGE: mu_delta =",
        "The circularity in MuInitiality.v is broken",
    ]
    present = [phrase for phrase in forbidden if phrase in source]
    assert not present, f"unproved VM-cost claims remain: {present}"


def test_repository_coq_build_entrypoints_are_serialized():
    paths = [
        ROOT / ".githooks/pre-commit",
        ROOT / "Makefile",
        ROOT / "scripts/check_isa_proof_freshness.sh",
        ROOT / "scripts/inquisitor.py",
        ROOT / "TECHNICAL_DISCLOSURE.md",
    ]
    offenders = {
        str(path.relative_to(ROOT)): [
            line for line in path.read_text().splitlines()
            if "make" in line.lower()
            and any(f"-j{workers}" in line for workers in range(2, 17))
        ]
        for path in paths
    }
    offenders = {path: lines for path, lines in offenders.items() if lines}
    assert not offenders, f"parallel Coq build entrypoints remain: {offenders}"


def test_pointer_examples_are_not_presented_as_protocol_security_results():
    paths = [
        ROOT / "coq/kernel/frontier/PointerObservable.v",
        ROOT / "coq/kernel/frontier/PointerObservableReductions.v",
        ROOT / "coq/kernel/frontier/PointerObservableCounterexamples.v",
        ROOT / "README.md",
        ROOT / "monograph/thiele_machine_math_spec.tex",
    ]
    forbidden = (
        "five deployed disciplines",
        "Every deployed discipline",
        "machine-checked counterexamples",
        "not a modeling artifact",
        "widely deployed forgery-resistant",
        "forgery resistance is achieved with NO metering",
        "faithful models of the deployed disciplines",
        "independent parties",
    )
    found = {
        str(path.relative_to(ROOT)): [phrase for phrase in forbidden if phrase in path.read_text()]
        for path in paths
    }
    found = {path: phrases for path, phrases in found.items() if phrases}
    assert not found, f"synthetic observer models still carry protocol/security claims: {found}"


def test_domain_wrappers_disclose_their_abstract_scope():
    required = {
        ROOT / "coq/kernel/reductions/GasMetering.v": "domain-inspired abstract wrapper",
        ROOT / "coq/kernel/reductions/PoSFinality.v": "synthetic explicit-finalize Boolean gadget",
        ROOT / "coq/kernel/reductions/TEEAttestation.v": "abstract transcript-plus-nat wrapper",
        ROOT / "coq/kernel/reductions/ProofCarryingVerifier.v": "carried-mu-claim wrapper",
    }
    missing = {
        str(path.relative_to(ROOT)): phrase
        for path, phrase in required.items()
        if phrase not in path.read_text().replace("µ", "mu")
    }
    assert not missing, f"domain-inspired wrappers lack explicit scope fences: {missing}"


def test_factorization_prose_keeps_the_collision_premises():
    technical = (ROOT / "TECHNICAL_DISCLOSURE.md").read_text()
    math_spec = (ROOT / "monograph/thiele_machine_math_spec.tex").read_text()
    assert "supplied colliding transcripts" in technical
    assert "supplied colliding transcripts" in math_spec
    for text in (technical, math_spec):
        assert "substrate/hardness/interaction trichotomy" not in text
    verifier_sources = [
        ROOT / "coq/VerifierModel.v",
        ROOT / "coq/VerifierImpossibility.v",
        ROOT / "coq/VerifierExhaustiveness.v",
    ]
    assert all("closes the trichotomy" not in path.read_text() for path in verifier_sources)


def test_structural_round_one_does_not_overname_halting_coverage():
    source = (ROOT / "coq/kernel/foundation/StructuralCore.v").read_text()
    assert "halting_problem_coverage" in source
    assert "turing_equivalent" not in source
    assert "simulates every two-counter machine" not in source


def test_tpm_quote_model_records_its_scope_and_final_spec_pin():
    source = (ROOT / "coq/kernel/reductions/TPMQuoteGap.v").read_text()
    assert "deliberately scoped abstraction of TPM quote fields" in source
    assert "Version-185_pub.pdf" in source
    assert "real protocol" not in source
    assert "starts at zero" not in source
    assert "Boot-time attestation" not in source


def test_unbounded_vm_is_not_described_as_hardware_faithful():
    source = (ROOT / "coq/kernel/foundation/VMUnboundedStep.v").read_text()
    forbidden = (
        "hardware-faithful",
        "matches the hardware's finite register file",
        "whenever both operands fit in 64 bits",
        "proved per operation",
    )
    present = [phrase for phrase in forbidden if phrase in source]
    assert not present, f"unbounded VM retains a false word-width bridge: {present}"
