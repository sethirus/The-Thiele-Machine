"""Empirical checks around Einstein relation proxies in production demo utilities."""

from tools.prove_einstein import computation_to_metric, curvature_to_einstein, metric_to_curvature


def test_curvature_proxy_increases_with_mass_variance() -> None:
    low_variance_modules = {
        0: {"region": [0], "mass": 1.0},
        1: {"region": [1], "mass": 1.0},
        2: {"region": [2], "mass": 1.0},
    }
    high_variance_modules = {
        0: {"region": [0], "mass": 0.5},
        1: {"region": [1], "mass": 1.0},
        2: {"region": [2], "mass": 1.5},
    }

    low = metric_to_curvature(low_variance_modules)
    high = metric_to_curvature(high_variance_modules)
    assert low == 0.0
    assert high > low


def test_demo_pipeline_runs_without_error() -> None:
    modules = computation_to_metric()
    einstein_proxy = metric_to_curvature(modules)
    assert einstein_proxy > 0.0
    curvature_to_einstein(modules, einstein_proxy)
