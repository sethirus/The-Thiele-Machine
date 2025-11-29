# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Thiele Machine Benchmarks

This package contains benchmarks that prove measurable advantages of the
Thiele Machine over classical computation.
"""

from .advantage_benchmarks import (
    BenchmarkResult,
    benchmark_binary_vs_linear_search,
    benchmark_constraint_propagation,
    benchmark_divide_and_conquer,
    benchmark_early_termination,
    benchmark_verification_vs_discovery,
    benchmark_graph_components,
    run_all_benchmarks,
)

__all__ = [
    "BenchmarkResult",
    "benchmark_binary_vs_linear_search",
    "benchmark_constraint_propagation",
    "benchmark_divide_and_conquer",
    "benchmark_early_termination",
    "benchmark_verification_vs_discovery",
    "benchmark_graph_components",
    "run_all_benchmarks",
]
