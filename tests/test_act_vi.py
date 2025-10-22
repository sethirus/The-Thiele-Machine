# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
from pathlib import Path

from demonstrate_isomorphism import run_act_vi


def test_act_vi_offline(tmp_path):
    out = run_act_vi(mode="offline", allow_network=False, cmb_file=None, output_dir=str(tmp_path), data_source="offline")
    receipt_path = Path(out["receipt_path"])
    proof_path = Path(out["prediction_certificate_path"])
    assert receipt_path.exists()
    assert proof_path.exists()
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert "predicted_trial" in receipt
    assert isinstance(receipt.get("prediction_proved"), bool)
    assert "robustness" in receipt
    assert receipt.get("prediction_proof_method") == "analytic"
    assert "prediction_certificate" in receipt
    assert "certificate" in receipt["robustness"]
    assert receipt["robustness"].get("proof_method") == "analytic"
    assert 0.0 <= float(receipt["robustness"].get("sample_fraction", 0.0)) <= 1.0
    assert isinstance(receipt.get("mdl_bits"), float)
    assert Path(out["robust_certificate_path"]).exists()


def test_mdl_description_length():
    from demonstrate_isomorphism import SimpleRule, mdl_description_length

    r = SimpleRule(idx=0, threshold=0.1, true_pair=(1, 0), false_pair=(0, 1), param_count=1)
    bits = mdl_description_length(r)
    assert isinstance(bits, float)
    assert bits >= 8.0


def test_write_fits_from_csv(tmp_path):
    from demonstrate_isomorphism import write_fits_from_csv

    csv_path = tmp_path / "sample.csv"
    csv_path.write_text("0.1\n0.2\n0.3\n", encoding="utf-8")
    fits_path = tmp_path / "out.fits"
    try:
        write_fits_from_csv(csv_path, fits_path)
    except ImportError:
        # astropy not installed in test environment; treat as skipped
        import pytest

        pytest.skip("astropy not available; skipping FITS write test")
    assert fits_path.exists()
