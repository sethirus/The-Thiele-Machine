"""Shared statistical utilities for public-data protocols."""

from __future__ import annotations

import math
from typing import Iterable, Sequence, Tuple


def _median(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def _quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return 0.0
    if q <= 0.0:
        return values[0]
    if q >= 1.0:
        return values[-1]
    position = q * (len(values) - 1)
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    if lower == upper:
        return values[lower]
    weight = position - lower
    return values[lower] * (1.0 - weight) + values[upper] * weight


def _rank(values: Sequence[float]) -> list[float]:
    n = len(values)
    indexed = sorted(range(n), key=lambda idx: values[idx])
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i
        while j + 1 < n and values[indexed[j + 1]] == values[indexed[i]]:
            j += 1
        rank_value = (i + j + 2) / 2.0
        for k in range(i, j + 1):
            ranks[indexed[k]] = rank_value
        i = j + 1
    return ranks


def theil_sen_statistics(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float, float, float]:
    """Return Theil–Sen slope/intercept and a central 95% interval."""

    n = len(xs)
    slopes: list[float] = []
    for i in range(n):
        for j in range(i + 1, n):
            if xs[j] == xs[i]:
                continue
            slopes.append((ys[j] - ys[i]) / (xs[j] - xs[i]))
    if not slopes:
        slope = 0.0
        intercept = _median(ys)
        return slope, intercept, slope, slope
    slopes.sort()
    slope = _median(slopes)
    intercepts = [ys[idx] - slope * xs[idx] for idx in range(n)]
    intercept = _median(intercepts)
    low = _quantile(slopes, 0.025)
    high = _quantile(slopes, 0.975)
    return slope, intercept, low, high


def spearman(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float]:
    """Return Spearman's ρ and a normal-approximation p-value."""

    if len(xs) != len(ys):
        raise ValueError("Spearman samples must share length")
    n = len(xs)
    if n < 3:
        return 0.0, 1.0
    rank_x = _rank(xs)
    rank_y = _rank(ys)
    mean_x = sum(rank_x) / n
    mean_y = sum(rank_y) / n
    cov = sum((rank_x[i] - mean_x) * (rank_y[i] - mean_y) for i in range(n))
    std_x = math.sqrt(sum((rank - mean_x) ** 2 for rank in rank_x))
    std_y = math.sqrt(sum((rank - mean_y) ** 2 for rank in rank_y))
    if std_x == 0.0 or std_y == 0.0:
        return 0.0, 1.0
    rho = cov / (std_x * std_y)
    rho = max(-1.0, min(1.0, rho))
    t_stat = abs(rho) * math.sqrt((n - 2) / max(1e-12, 1.0 - rho**2))
    p_value = math.erfc(t_stat / math.sqrt(2.0))
    return rho, p_value


def _least_squares(xs: Sequence[float], ys: Sequence[float]) -> Tuple[float, float]:
    if len(xs) != len(ys):
        raise ValueError("Samples must share length")
    n = len(xs)
    if n == 0:
        return 0.0, 0.0
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    var = sum((x - mean_x) ** 2 for x in xs)
    if var == 0.0:
        return 0.0, mean_y
    slope = cov / var
    intercept = mean_y - slope * mean_x
    return slope, intercept


def _aic(residuals: Iterable[float], k: int) -> float:
    residuals = list(residuals)
    n = len(residuals)
    if n == 0:
        return float("inf")
    sse = sum(res**2 for res in residuals)
    sse = max(sse, 1e-30)
    return 2 * k + n * math.log(sse / n)


def delta_aic_exp_vs_poly(xs: Sequence[float], ys: Sequence[float]) -> float:
    """Return ΔAIC(exp−poly) for ``ys`` sampled at ``xs``."""

    if len(xs) != len(ys):
        raise ValueError("Samples must share length")
    if len(xs) < 3:
        return 0.0

    slope_poly, intercept_poly = _least_squares(xs, ys)
    poly_residuals = [y - (intercept_poly + slope_poly * x) for x, y in zip(xs, ys)]

    safe_ys = [max(y, 1e-12) for y in ys]
    log_y = [math.log(value) for value in safe_ys]
    slope_exp, intercept_exp = _least_squares(xs, log_y)
    exp_residuals = [
        y - math.exp(intercept_exp + slope_exp * x) for x, y in zip(xs, ys)
    ]

    aic_poly = _aic(poly_residuals, 2)
    aic_exp = _aic(exp_residuals, 2)
    return aic_poly - aic_exp


__all__ = ["delta_aic_exp_vs_poly", "spearman", "theil_sen_statistics"]

