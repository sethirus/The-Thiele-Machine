from __future__ import annotations

from pathlib import Path

import pytest


def _write_csv(path: Path, text: str) -> None:
    path.write_text(text.strip() + "\n", encoding="utf-8")


def test_prereg_a_filters_by_sources(tmp_path: Path) -> None:
    from tools.prereg_a_landauer import load_datapoints

    d = tmp_path / "data"
    d.mkdir()

    _write_csv(
        d / "a.csv",
        """
paper_id,figure_id,dataset_id,value_kind,tau_unit,tau_s,work_over_kT,work_err_over_kT,info_bits_removed
PaperA,Fig1,DS1,work_over_kT,s,1.0,1.0,,1.0
PaperB,Fig1,DS2,work_over_kT,s,1.0,1.0,,1.0
""",
    )

    pts = load_datapoints(d)
    assert {p.paper_id for p in pts} == {"PaperA", "PaperB"}


@pytest.mark.parametrize(
    "bad_row,expected_substr",
    [
        (
            "PaperA,Fig1,DS1,badkind,s,1.0,1.0,,1.0",
            "value_kind",
        ),
        (
            "PaperA,Fig1,DS1,work_over_kT,none,1.0,1.0,,1.0",
            "tau_unit='none'",
        ),
        (
            "PaperA,Fig1,DS1,a_coeff,s,1.0,1.0,,1.0",
            "value_kind='a_coeff'",
        ),
        (
            "PaperA,Fig1,DS1,work_over_kT,s,-1.0,1.0,,1.0",
            "tau_s must be >0",
        ),
    ],
)
def test_prereg_a_schema_rejects_invalid_rows(tmp_path: Path, bad_row: str, expected_substr: str) -> None:
    from tools.prereg_a_landauer import load_datapoints

    d = tmp_path / "data"
    d.mkdir()

    _write_csv(
        d / "bad.csv",
        """
paper_id,figure_id,dataset_id,value_kind,tau_unit,tau_s,work_over_kT,work_err_over_kT,info_bits_removed
"""
        + bad_row
        + "\n",
    )

    with pytest.raises(ValueError) as excinfo:
        load_datapoints(d)
    assert expected_substr in str(excinfo.value)
