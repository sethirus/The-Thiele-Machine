# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Proof-carrying ``LASSERT`` implementation."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Optional

from .certcheck import CertificateError, LassertCertificate, verify_certificate
from .certs import CertStore
from .isa import CSR
from .mu import calculate_mu_cost
from .state import State
from ._types import ModuleId


@dataclass(frozen=True)
class LassertConfig:
    cnf_path: Path
    proof_type: str
    proof_path: Optional[Path]
    model_path: Optional[Path]

    @classmethod
    def load(cls, config_path: Path) -> "LassertConfig":
        raw = json.loads(config_path.read_text(encoding="utf-8"))
        if not isinstance(raw, dict):
            raise ValueError("LASSERT config must be a JSON object")
        try:
            cnf_field = raw["cnf"]
            proof_type = str(raw["proof_type"])
        except KeyError as exc:
            raise ValueError("LASSERT config missing required field") from exc
        cnf_path = Path(cnf_field)
        if not cnf_path.is_absolute():
            cnf_path = (config_path.parent / cnf_path).resolve()
        proof_type_upper = proof_type.upper()
        proof_path: Optional[Path]
        model_path: Optional[Path]
        if proof_type_upper == "LRAT":
            proof_entry = raw.get("proof")
            if proof_entry is None:
                raise ValueError("LRAT certificate requires 'proof' path")
            proof_path = Path(proof_entry)
            if not proof_path.is_absolute():
                proof_path = (config_path.parent / proof_path).resolve()
            model_path = None
        elif proof_type_upper == "MODEL":
            model_entry = raw.get("model")
            if model_entry is None:
                raise ValueError("MODEL certificate requires 'model' path")
            model_path = Path(model_entry)
            if not model_path.is_absolute():
                model_path = (config_path.parent / model_path).resolve()
            proof_path = None
        else:
            raise ValueError(f"Unsupported proof_type: {proof_type}")
        return cls(
            cnf_path=cnf_path,
            proof_type=proof_type_upper,
            proof_path=proof_path,
            model_path=model_path,
        )


@dataclass(frozen=True)
class LassertResult:
    certificate: LassertCertificate
    mu_delta: float
    receipt_payload: Dict[str, object]
    cid: str


def _write_certificate(store: CertStore, cid: str, config: LassertConfig, cert: LassertCertificate) -> None:
    store.write_text(cid, "cnf", cert.cnf.text)
    if cert.proof_type == "LRAT" and config.proof_path is not None:
        store.write_text(cid, "lrat", config.proof_path.read_text(encoding="utf-8"))
    elif cert.proof_type == "MODEL" and config.model_path is not None:
        store.write_text(cid, "model", config.model_path.read_text(encoding="utf-8"))
    store.save_hash(cid, cert.cnf.text.encode("utf-8"))


def lassert(state: State, module: ModuleId, config_path: Path, outdir: Path) -> LassertResult:
    """Validate an LASSERT proofpack specified by ``config_path``."""

    module_id = ModuleId(int(module))
    config = LassertConfig.load(config_path)
    try:
        certificate = verify_certificate(
            cnf_path=config.cnf_path,
            proof_type=config.proof_type,
            proof_path=config.proof_path,
            model_path=config.model_path,
        )
    except CertificateError as exc:
        raise ValueError(f"certificate verification failed: {exc}") from exc

    state.add_axiom(module_id, certificate.cnf.text)
    store = CertStore(outdir)
    cid = store.next_id()
    _write_certificate(store, cid, config, certificate)

    if certificate.status == "UNSAT":
        state.csr[CSR.STATUS] = 0
        state.csr[CSR.ERR] = 1
    else:
        state.csr[CSR.STATUS] = 1
        state.csr[CSR.ERR] = 0
    state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))

    # Compute semantic μ-cost using CONSERVATIVE BOUND
    # 
    # Why conservative? Computing exact model count is #P-complete (intractable).
    # Instead, we use after = 1 which GUARANTEES μ ≥ log₂(|Ω|/|Ω'|):
    #   - For SAT: actual |Ω'| ≥ 1, so our bound log₂(2^n/1) ≥ log₂(2^n/|Ω'|)
    #   - For UNSAT: |Ω'| = 0 makes log undefined; we charge maximum (n bits)
    # 
    # Trade-off: May OVERCHARGE when multiple solutions exist. This is 
    # intentional: conservative enforcement, not exact computation.
    num_vars = certificate.cnf.num_vars
    before_count = 2 ** num_vars if num_vars < 64 else 2**63  # Cap to avoid overflow
    
    # Conservative bound: always assume single solution (after = 1)
    # This guarantees μ ≥ log₂(|Ω|/|Ω'|) without #P-complete model counting
    after_count = 1
    mu_delta = calculate_mu_cost(certificate.cnf.text, before_count, after_count)

    receipt_payload = {
        "op": "LASSERT",
        "cnf_sha256": certificate.cnf.sha256,
        "proof_type": certificate.proof_type,
        "proof_sha256": certificate.proof_sha256,
        "status": certificate.status,
        "mu_delta": mu_delta,
        "cid": cid,
    }

    return LassertResult(
        certificate=certificate,
        mu_delta=mu_delta,
        receipt_payload=receipt_payload,
        cid=cid,
    )


def ljoin(state: State, cert1: str, cert2: str, outdir: Path) -> str:
    """Join two certificate hashes and write a combined certificate."""

    store = CertStore(outdir)
    cid = store.next_id()
    combined = (cert1 + cert2).encode("utf-8")
    store.write_bytes(cid, "join", combined)
    digest = store.save_hash(cid, combined)
    state.csr[CSR.CERT_ADDR] = str(store.hash_path(cid))
    if cert1 != cert2:
        state.csr[CSR.ERR] = 1
    return digest


__all__ = ["lassert", "ljoin", "LassertResult"]
