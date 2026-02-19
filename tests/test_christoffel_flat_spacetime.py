"""Lightweight Christoffel/curvature behavior checks against production helpers."""

from tools.prove_einstein import computation_to_metric, metric_to_curvature


def test_uniform_mass_has_zero_curvature_proxy() -> None:
    uniform_modules = {
        0: {"region": [0], "mass": 1.0},
        1: {"region": [1], "mass": 1.0},
        2: {"region": [2], "mass": 1.0},
    }
    einstein_proxy = metric_to_curvature(uniform_modules)
    assert einstein_proxy == 0.0


def test_nonuniform_mass_has_positive_curvature_proxy() -> None:
    modules = computation_to_metric()
    einstein_proxy = metric_to_curvature(modules)
    assert einstein_proxy > 0.0
