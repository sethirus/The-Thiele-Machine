"""Small, reusable checks for empirical evaluation artifacts.

These helpers are intentionally generic so experiment scripts can emit
self-verifying JSON artifacts (monotonicity, conservation, invariants)
without duplicating logic.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable, Sequence, TypeVar, Any


T = TypeVar("T")


@dataclass(frozen=True)
class CheckResult:
    name: str
    passed: bool
    detail: str | None = None

    def as_dict(self) -> dict[str, object]:
        payload: dict[str, object] = {"name": self.name, "passed": self.passed}
        if self.detail:
            payload["detail"] = self.detail
        return payload


def _as_key_fn(key: str | Callable[[T], Any] | None) -> Callable[[T], Any]:
    if key is None:
        return lambda x: x
    if isinstance(key, str):
        return lambda x: getattr(x, key) if hasattr(x, key) else x[key]  # type: ignore[index]
    return key


def check_monotonic_nonincreasing(
    items: Sequence[T],
    *,
    name: str,
    key: str | Callable[[T], Any] | None = None,
) -> CheckResult:
    """Return PASS iff key(item[i]) >= key(item[i+1]) for all i."""

    if len(items) < 2:
        return CheckResult(name=name, passed=True, detail="<2 points")

    key_fn = _as_key_fn(key)
    prev = key_fn(items[0])
    for i, item in enumerate(items[1:], start=1):
        cur = key_fn(item)
        if prev < cur:
            return CheckResult(
                name=name,
                passed=False,
                detail=f"violation at index {i}: {prev!r} < {cur!r}",
            )
        prev = cur
    return CheckResult(name=name, passed=True)


def check_monotonic_nondecreasing(
    items: Sequence[T],
    *,
    name: str,
    key: str | Callable[[T], Any] | None = None,
) -> CheckResult:
    """Return PASS iff key(item[i]) <= key(item[i+1]) for all i."""

    if len(items) < 2:
        return CheckResult(name=name, passed=True, detail="<2 points")

    key_fn = _as_key_fn(key)
    prev = key_fn(items[0])
    for i, item in enumerate(items[1:], start=1):
        cur = key_fn(item)
        if prev > cur:
            return CheckResult(
                name=name,
                passed=False,
                detail=f"violation at index {i}: {prev!r} > {cur!r}",
            )
        prev = cur
    return CheckResult(name=name, passed=True)


def summarize_range(values: Iterable[float]) -> dict[str, float | None]:
    values_list = list(values)
    if not values_list:
        return {"min": None, "max": None, "mean": None}
    return {
        "min": min(values_list),
        "max": max(values_list),
        "mean": sum(values_list) / len(values_list),
    }
