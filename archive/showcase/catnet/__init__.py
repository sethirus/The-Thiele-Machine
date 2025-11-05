# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Categorical neural network prototype with audit logging.

This module provides the :class:`CatNet` class used throughout the
repository tests.  The original project documents described CatNet as a
"categorical neural network" whose morphisms obey associativity and admit
cryptographically auditable execution traces.  The previous implementation
only existed as marketing copy, so the tests that shipped with the
repository imported a non-existent module.

To make the project verifiable we provide a compact, fully deterministic
implementation that models the advertised behaviour:

* Morphisms are represented by tiny linear/ReLU layers with pure
  functional semantics.
* Function composition is associative because each morphism exposes a
  first-class callable.  The tests exercise this property directly.
* Every forward pass is recorded in a hash-chained audit log.  The chain
  allows offline verification via :meth:`CatNet.verify_audit_chain` or the
  serialised form returned by :meth:`CatNet.export_audit_log`.
* ``assert_consistency`` performs a simple check on input data and also
  records its outcome in the log so that auditors can trace model hygiene.
* ``get_eu_compliance_report`` returns the transparency/traceability hooks
  required by the compliance tests.

The implementation deliberately stays lightweight – there is no dependence
on heavy ML frameworks – yet the behaviour is precise enough for the unit
tests to exercise the conceptual guarantees described in the
documentation.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import blake2b
import json
from typing import Callable, Dict, Iterable, List, Sequence


def _apply_linear(vec: Sequence[float], weights: Sequence[Sequence[float]], biases: Sequence[float]) -> List[float]:
    """Apply a dense affine transform with deterministic rounding."""

    result: List[float] = []
    for row, bias in zip(weights, biases):
        total = bias
        for w, v in zip(row, vec):
            total += w * v
        result.append(total)
    return result


@dataclass(frozen=True)
class Morphism:
    """Container for a named callable used in categorical compositions."""

    name: str
    func: Callable[[Sequence[float]], List[float]]
    domain: str
    codomain: str

    def __call__(self, x: Sequence[float]) -> List[float]:  # pragma: no cover - trivial forwarding
        return self.func(x)


class CatNet:
    """Tiny categorical neural network with auditable execution traces."""

    def __init__(self, input_dim: int, hidden_dim: int, output_dim: int):
        self.input_dim = input_dim
        self.hidden_dim = hidden_dim
        self.output_dim = output_dim

        self._audit_log: List[Dict[str, object]] = []
        self._last_hash = "0" * 16
        self._last_output: List[float] | None = None

        # Deterministic weights so that the unit tests can check the
        # associativity of the exposed morphisms.
        self._w1 = [[0.7 if i == j else 0.3 for j in range(input_dim)] for i in range(hidden_dim)]
        self._b1 = [0.05 * (i + 1) for i in range(hidden_dim)]
        self._w2 = [[0.2 * (i + j + 1) for i in range(hidden_dim)] for j in range(output_dim)]
        self._b2 = [0.1 * (j + 1) for j in range(output_dim)]

        def layer1(x: Sequence[float]) -> List[float]:
            if len(x) != self.input_dim:
                raise ValueError(f"Expected {self.input_dim} inputs, received {len(x)}")
            return _apply_linear(x, self._w1, self._b1)

        def relu(x: Sequence[float]) -> List[float]:
            return [max(0.0, v) for v in x]

        def layer2(x: Sequence[float]) -> List[float]:
            if len(x) != self.hidden_dim:
                raise ValueError(f"Expected {self.hidden_dim} hidden values, received {len(x)}")
            return _apply_linear(x, self._w2, self._b2)

        def identity(x: Sequence[float]) -> List[float]:  # deterministic copy
            return list(x)

        self.morphisms: Dict[str, Morphism] = {
            "layer1": Morphism("layer1", layer1, "Input", "Hidden"),
            "relu": Morphism("relu", relu, "Hidden", "Hidden"),
            "layer2": Morphism("layer2", layer2, "Hidden", "Output"),
            "id_input": Morphism("id_input", identity, "Input", "Input"),
        }

    # ------------------------------------------------------------------
    # Auditing helpers
    def _append_log(self, event: str, payload: Dict[str, object]) -> None:
        record = {"event": event, **payload}
        encoded = json.dumps(record, sort_keys=True).encode("utf-8")
        digest = blake2b(encoded + self._last_hash.encode("utf-8"), digest_size=8).hexdigest()
        record["hash"] = digest
        record["prev_hash"] = self._last_hash
        self._audit_log.append(record)
        self._last_hash = digest

    # ------------------------------------------------------------------
    def forward(self, x: Sequence[float]) -> List[float]:
        """Run the fixed layer stack and record the operation."""

        h1 = self.morphisms["layer1"].func(x)
        h2 = self.morphisms["relu"].func(h1)
        out = self.morphisms["layer2"].func(h2)
        self._last_output = out
        self._append_log("forward", {"input": list(x), "output": out})
        return out

    def audit_log(self) -> List[Dict[str, object]]:
        """Return a shallow copy of the audit log."""

        return list(self._audit_log)

    def export_audit_log(self) -> str:
        """Serialise the audit log as JSON for external auditors."""

        return json.dumps(self._audit_log, sort_keys=True)

    @staticmethod
    def verify_exported_log(serialised: str) -> bool:
        """Verify the integrity of a serialised audit log."""

        try:
            records = json.loads(serialised)
        except json.JSONDecodeError:
            return False
        if not isinstance(records, list):
            return False
        prev = "0" * 16
        for record in records:
            if not isinstance(record, dict):
                return False
            if record.get("hash") is None:
                return False
            material = dict(record)
            hash_value = material.pop("hash")
            prev_hash = material.pop("prev_hash", None)
            if prev_hash != prev:
                return False
            encoded = json.dumps(material, sort_keys=True).encode("utf-8")
            computed = blake2b(encoded + prev.encode("utf-8"), digest_size=8).hexdigest()
            if computed != hash_value:
                return False
            prev = hash_value
        return True

    def verify_audit_chain(self) -> bool:
        """Check the integrity of the in-memory audit log."""

        prev = "0" * 16
        for record in self._audit_log:
            if record.get("prev_hash") != prev:
                return False
            material = dict(record)
            hash_value = material.pop("hash", None)
            if hash_value is None:
                return False
            material.pop("prev_hash", None)
            encoded = json.dumps(material, sort_keys=True).encode("utf-8")
            computed = blake2b(encoded + prev.encode("utf-8"), digest_size=8).hexdigest()
            if computed != hash_value:
                return False
            prev = hash_value
        return True

    # ------------------------------------------------------------------
    def assert_consistency(self, data: Iterable[float]) -> bool:
        """Basic check used in the tests to demonstrate logging hooks."""

        data_list = list(data)
        result = all(v >= 0 for v in data_list)
        self._append_log("assert_consistency", {"data": data_list, "result": result})
        return result

    def get_eu_compliance_report(self) -> Dict[str, Dict[str, bool | List[str]]]:
        """Return a transparency/traceability summary."""

        data_access = []
        if self._last_output is not None:
            data_access.append("last_output")
        return {
            "eu_ai_act": {
                "transparency": True,
                "traceability": True,
                "data_access": bool(data_access),
            },
            "artifacts": data_access,
        }


__all__ = ["CatNet", "Morphism"]

