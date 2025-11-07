#!/usr/bin/env python3
"""Canonicalize legacy receipt JSON files so the verifier accepts them.

This script updates receipts in-place by copying observation.mu_delta -> mu_delta,
observation.cert -> certificate, computing certificate_hash when a certificate
is present, and computing the canonical step_hash for each step using the
repository's canonical JSON encoding rules.

Run: python scripts/canonicalize_receipts.py receipts
"""
from pathlib import Path
import json
import hashlib
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools.receipts import compute_step_hash, compute_global_digest
from scripts.thiele_verify import parse_cnf, _canonicalise_cnf_and_map, parse_model, _canonicalise_model
from thielecpu.receipts import ensure_kernel_keys, sign_receipt, _resolve_verify_key, _load_verify_key_bytes
import os
from typing import Optional


def canonicalize_step(step: dict, receipt_dir: Path) -> bool:
    changed = False
    # Pull mu_delta up from observation if present
    obs = step.get("observation")
    if "mu_delta" not in step and isinstance(obs, dict) and "mu_delta" in obs:
        step["mu_delta"] = obs["mu_delta"]
        changed = True

    # Pull certificate up from observation if present
    if "certificate" not in step and isinstance(obs, dict) and "cert" in obs:
        step["certificate"] = obs["cert"]
        changed = True

    # Compute certificate_hash if missing and certificate present
    if "certificate" in step and "certificate_hash" not in step:
        cert = step["certificate"]
        if isinstance(cert, str):
            payload = cert.encode("utf-8")
        else:
            payload = json.dumps(cert, sort_keys=True).encode("utf-8")
        step["certificate_hash"] = hashlib.sha256(payload).hexdigest()
        changed = True

    # If a model blob exists and a CNF is available, produce a canonicalised model
    model_uri = step.get("model_blob_uri")
    cnf_uri = step.get("cnf_blob_uri")
    if not model_uri and isinstance(step.get("certificate"), dict):
        # Some receipts embed model info under certificate; try common keys
        cert = step["certificate"]
        model_uri = cert.get("model_blob_uri") or cert.get("model_path")
        cnf_uri = cnf_uri or (cert.get("cnf", {}) or {}).get("path")

    def _read_blob_uri(uri: Optional[str]) -> Optional[bytes]:
        if uri is None:
            return None
        p = Path(uri)
        if not p.is_absolute():
            p = receipt_dir / uri
        if p.exists():
            return p.read_bytes()
        # treat inline blob
        try:
            return uri.encode("utf-8")
        except Exception:
            return None

    if model_uri and cnf_uri:
        cnf_blob = _read_blob_uri(cnf_uri)
        model_blob = _read_blob_uri(model_uri)
        if cnf_blob is not None and model_blob is not None:
            try:
                cnf = parse_cnf(cnf_blob)
                canonical_cnf, var_map = _canonicalise_cnf_and_map(cnf)
                raw_model = parse_model(model_blob)
                mapped_model = _canonicalise_model(raw_model, var_map)
                # write canonical model file next to the original model if possible
                orig_path = Path(model_uri)
                if not orig_path.is_absolute():
                    orig_path = receipt_dir / model_uri
                # store canonical models under a dedicated cert_store/models directory
                models_dir = receipt_dir / "cert_store" / "models"
                models_dir.mkdir(parents=True, exist_ok=True)
                # Use the original model path's base name (orig_path was computed above)
                base_name = orig_path.stem
                # Prefer 'idx' but fall back to 'step' (tests use 'step').
                step_index = step.get('idx', step.get('step', '?'))
                # Ensure index is safe for filenames (avoid characters like '?')
                step_index_text = str(step_index) if isinstance(step_index, (int, str)) else "?"
                new_name = f"{base_name}.step{step_index_text}.canonical.model"
                new_path = models_dir / new_name
                new_path.parent.mkdir(parents=True, exist_ok=True)
                # write DIMACS-style model as space separated literals ending with 0
                with open(new_path, "wb") as fh:
                    fh.write((" ".join(str(l) for l in mapped_model) + " 0\n").encode("utf-8"))
                model_sha = hashlib.sha256(new_path.read_bytes()).hexdigest()
                step["model_blob_uri"] = str(new_path)
                step["model_sha256"] = model_sha
                changed = True
            except Exception as e:
                # If anything goes wrong, don't block canonicalisation of other fields
                # but surface the error during debugging so we can fix root causes.
                try:
                    import traceback

                    print("[canonicalize] model canonicalisation failed:", e)
                    traceback.print_exc()
                except Exception:
                    pass

    # If the step carries an LRAT or DRAT proof, run the analyzer (best-effort) to
    # decide if normalization is required. This avoids accepting RAT-only
    # LRATs silently.
    pf = step.get("proof_portable")
    proof_uri = step.get("proof_blob_uri")
    if pf in ("LRAT", "DRAT") and proof_uri:
        try:
            analyzer = Path(__file__).resolve().parents[1] / "scripts" / "analyze_lrat.py"
            cnf_path = None
            if cnf_uri:
                blob = _read_blob_uri(cnf_uri)
                # if cnf_uri refers to a file under receipt_dir, pass it through
                p = Path(cnf_uri)
                if not p.is_absolute():
                    p = receipt_dir / cnf_uri
                if p.exists():
                    cnf_path = p
            # run analyzer with --normalize to attempt drat-trim when available
            import subprocess

            res = subprocess.run([sys.executable, str(analyzer), str(proof_uri), "--cnf", str(cnf_path) if cnf_path else "", "--normalize"], check=False)
            if res.returncode == 0:
                step["status"] = "ok"
            else:
                step["status"] = "requires_normalization"
            changed = True
        except Exception:
            # non-fatal; set default status if not already present
            if "status" not in step:
                step["status"] = "requires_normalization"
                changed = True

    # Step hash/signature are computed at file level to ensure consistent
    # signing and hashing order (signature is included in the step payload
    # and therefore influences the step_hash). The canonicalize_file function
    # will assign per-step signatures and recompute step_hash values.

    return changed


def canonicalize_file(path: Path) -> bool:
    data = json.loads(path.read_text(encoding="utf-8"))
    if "steps" not in data:
        return False
    changed_any = False
    for step in data["steps"]:
        if canonicalize_step(step, path.parent):
            changed_any = True
    if changed_any:
        # Per-step signing: sign each step (payload excludes 'signature') and then
        # compute the canonical step_hash which will include the signature field.
        try:
            ensure_kernel_keys()
        except Exception:
            # signing is best-effort
            pass

        step_hashes = []
        for idx, step in enumerate(data.get("steps", [])):
            # prepare payload to sign: copy step without existing 'signature' or 'step_hash'
            payload = {k: v for k, v in step.items() if k not in ("signature", "step_hash")}
            try:
                sig = sign_receipt(payload)
                step["signature"] = sig
            except Exception:
                # If signing fails, leave unsigned and continue
                pass
            # recompute step_hash now that signature may be present
            step_hash = compute_step_hash(step)
            step["step_hash"] = step_hash
            step_hashes.append(step_hash)

        # recompute global digest from step_hashes
        if step_hashes:
            data["global_digest"] = compute_global_digest(step_hashes)

        # bump spec version to 1.1 to indicate canonicalisation has been applied
        data["spec_version"] = "1.1"

        # expose kernel_pubkey (best-effort) if available
        try:
            verify_key_path = _resolve_verify_key()
            vk_bytes = _load_verify_key_bytes(verify_key_path)
            if len(vk_bytes) == 32:
                pub_hex = vk_bytes.hex()
            else:
                try:
                    text = vk_bytes.decode('ascii').strip()
                    if len(text) == 64 and all(c in '0123456789abcdefABCDEF' for c in text):
                        pub_hex = text.lower()
                    else:
                        pub_hex = vk_bytes.hex()
                except Exception:
                    pub_hex = vk_bytes.hex()
            data["kernel_pubkey"] = pub_hex
        except Exception:
            pass

        path.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, indent=2), encoding="utf-8")
    return changed_any


def main():
    import argparse

    p = argparse.ArgumentParser(description="Canonicalize receipt JSON files in a directory")
    p.add_argument("directory", help="Directory containing receipt JSON files")
    args = p.parse_args()
    d = Path(args.directory)
    if not d.is_dir():
        print(f"Not a directory: {d}")
        raise SystemExit(2)
    changed = False
    for pth in sorted(d.glob("*.json")):
        try:
            updated = canonicalize_file(pth)
            if updated:
                print(f"Updated: {pth}")
                changed = True
            else:
                print(f"No change: {pth}")
        except Exception as e:
            print(f"Failed to canonicalize {pth}: {e}")
    if changed:
        print("Some receipts were canonicalized. Please run: python scripts/challenge.py verify receipts")


if __name__ == '__main__':
    main()
