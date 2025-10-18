# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from __future__ import annotations

import copy
import json
import math
import os
import random
import hmac
import hashlib
import time
from typing import Callable, List, Optional

try:  # Optional PyTorch dependency
    import torch
    import torch.nn as nn
    import torch.nn.functional as F
    TORCH_AVAILABLE = True
except Exception:  # pragma: no cover - torch optional for tests
    torch = None  # type: ignore
    nn = None  # type: ignore
    F = None  # type: ignore
    TORCH_AVAILABLE = False

EXPORT_SIGNING_KEY_ENV = "CATNET_SIGNING_KEY"


def _seed_everything(seed: int = 1337) -> None:
    random.seed(seed)
    try:
        import numpy as np  # type: ignore
        np.random.seed(seed)
    except Exception:
        pass
    if TORCH_AVAILABLE:
        torch.manual_seed(seed)


class CategoryElement:
    def __init__(self, name: str, data: List[float]):
        self.name = name
        self.element_id = name
        self.data = data


class CallableMorphism:
    def __init__(
        self, name: str, func: Callable[[List[float]], List[float]], source: CategoryElement, target: CategoryElement
    ) -> None:
        self.name = name
        self.func = func
        self.source = source
        self.target = target


class CatNet:
    """A tiny neural network built from categorical primitives with audit logging."""

    def __init__(
        self,
        input_size: int,
        hidden_size: int,
        output_size: int,
        storage_path: Optional[str] = None,
    ) -> None:
        _seed_everything()
        self._clock = time.monotonic_ns
        self._seq = 0
        self._audit_log: List[dict] = []
        self._storage_path: Optional[str] = None
        if storage_path is not None:
            self.enable_append_only_storage(storage_path)

        # Objects
        self.input_obj = CategoryElement("Input", [0.0] * input_size)
        self.hidden_obj = CategoryElement("Hidden", [0.0] * hidden_size)
        self.output_obj = CategoryElement("Output", [0.0] * output_size)

        # Parameters
        if TORCH_AVAILABLE:
            self.weights1 = nn.Parameter(torch.randn(hidden_size, input_size) * 0.1)
            self.bias1 = nn.Parameter(torch.zeros(hidden_size))
            self.weights2 = nn.Parameter(torch.randn(output_size, hidden_size) * 0.1)
            self.bias2 = nn.Parameter(torch.zeros(output_size))
        else:  # fallback to pure Python lists
            self.weights1 = [
                [random.gauss(0, 0.1) for _ in range(input_size)] for _ in range(hidden_size)
            ]
            self.bias1 = [0.0 for _ in range(hidden_size)]
            self.weights2 = [
                [random.gauss(0, 0.1) for _ in range(hidden_size)] for _ in range(output_size)
            ]
            self.bias2 = [0.0 for _ in range(output_size)]

        # Morphisms
        self.morphisms: dict[str, CallableMorphism] = {}
        layer1 = CallableMorphism(
            "layer1",
            self.linear_layer(self.weights1, self.bias1),
            self.input_obj,
            self.hidden_obj,
        )
        relu = CallableMorphism("relu", self.relu, self.hidden_obj, self.hidden_obj)
        layer2 = CallableMorphism(
            "layer2",
            self.linear_layer(self.weights2, self.bias2),
            self.hidden_obj,
            self.output_obj,
        )
        self.morphisms["layer1"] = layer1
        self.morphisms["relu"] = relu
        self.morphisms["layer2"] = layer2
        self.morphisms["id_input"] = CallableMorphism("id_input", lambda x: list(x), self.input_obj, self.input_obj)
        self.morphisms["id_hidden"] = CallableMorphism("id_hidden", lambda x: list(x), self.hidden_obj, self.hidden_obj)
        self.morphisms["id_output"] = CallableMorphism("id_output", lambda x: list(x), self.output_obj, self.output_obj)

        # simple logic oracle for demonstrative consistency checks
        self.logic_oracle = lambda axioms: all(a > 0 for a in axioms)

        # log seed
        entry = {"event": "init", "seed": 1337}
        self._add_entry(entry)

    # ------------------------------------------------------------------
    # Utility functions
    def _next_stamp(self) -> dict:
        self._seq += 1
        return {"ts_ns": self._clock(), "seq": self._seq}

    def _append_to_storage(self, entry: dict) -> None:
        if self._storage_path:
            with open(self._storage_path, "a") as f:
                f.write(json.dumps(entry, sort_keys=True) + "\n")

    def enable_append_only_storage(self, path: str) -> None:
        self._storage_path = path
        with open(self._storage_path, "a"):
            pass

    # ------------------------------------------------------------------
    def _add_entry(self, entry: dict) -> None:
        prev_hash = self._audit_log[-1]["crypto_hash"] if self._audit_log else ""
        entry["previous_hash"] = prev_hash
        entry["stamp"] = self._next_stamp()
        entry_for_hash = {k: v for k, v in entry.items() if k != "crypto_hash"}
        entry_json = json.dumps(entry_for_hash, sort_keys=True)
        entry["crypto_hash"] = hashlib.sha256(entry_json.encode()).hexdigest()
        self._audit_log.append(entry)
        self._append_to_storage(entry)

    @staticmethod
    def _to_list(value):
        if TORCH_AVAILABLE and isinstance(value, (torch.Tensor, nn.Parameter)):
            return value.detach().tolist()
        return value

    # ------------------------------------------------------------------
    def linear_layer(
        self,
        weights: "nn.Parameter | List[List[float]]",
        bias: "nn.Parameter | List[float]",
    ) -> Callable[[List[float]], List[float]]:
        if TORCH_AVAILABLE:
            def layer(x: List[float]) -> List[float]:
                x_t = torch.tensor(x, dtype=torch.float32)
                out = F.linear(x_t, weights, bias)
                return out.tolist()
            return layer
        else:
            def layer(x: List[float]) -> List[float]:
                return [
                    sum(w * xi for w, xi in zip(row, x)) + b
                    for row, b in zip(weights, bias)
                ]
            return layer

    def relu(self, x: List[float]) -> List[float]:
        if TORCH_AVAILABLE:
            x_t = torch.tensor(x, dtype=torch.float32)
            return F.relu(x_t).tolist()
        return [max(0.0, xi) for xi in x]

    def softmax(self, x: List[float]) -> List[float]:
        m = max(x)
        exps = [math.exp(xi - m) for xi in x]
        s = sum(exps)
        return [e / s for e in exps]

    def assert_consistency(self, axioms: List[int]) -> bool:
        """Check axioms with the logic oracle and log the result."""
        is_consistent = bool(self.logic_oracle(axioms))
        entry = {
            "event": "assert_consistency",
            "axioms": list(axioms),
            "result": is_consistent,
        }
        self._add_entry(entry)
        if not is_consistent:
            print("PARADOX DETECTED. Infinite cost incurred.")
        return is_consistent

    # ------------------------------------------------------------------
    def forward(self, x: List[float]) -> List[float]:
        h = self.morphisms["layer1"].func(x)
        h_relu = self.morphisms["relu"].func(h)
        y = self.morphisms["layer2"].func(h_relu)
        y_softmax = self.softmax(y)
        entry = {
            "event": "forward",
            "input": list(x),
            "hidden": list(h),
            "hidden_relu": list(h_relu),
            "output": list(y_softmax),
            "parameters": self.parameters(),
        }
        self._add_entry(entry)
        return y_softmax

    def parameters(self):
        if TORCH_AVAILABLE:
            return [
                self.weights1.detach().tolist(),
                self.bias1.detach().tolist(),
                self.weights2.detach().tolist(),
                self.bias2.detach().tolist(),
            ]
        return [
            [row[:] for row in self.weights1],
            list(self.bias1),
            [row[:] for row in self.weights2],
            list(self.bias2),
        ]

    def set_parameters(self, weights1, bias1, weights2, bias2):
        old_params = self.parameters()
        new_params = [
            self._to_list(weights1),
            self._to_list(bias1),
            self._to_list(weights2),
            self._to_list(bias2),
        ]
        entry = {
            "event": "set_parameters",
            "old_parameters": copy.deepcopy(old_params),
            "new_parameters": copy.deepcopy(new_params),
        }
        self._add_entry(entry)
        if TORCH_AVAILABLE:
            self.weights1 = nn.Parameter(torch.tensor(weights1, dtype=torch.float32))
            self.bias1 = nn.Parameter(torch.tensor(bias1, dtype=torch.float32))
            self.weights2 = nn.Parameter(torch.tensor(weights2, dtype=torch.float32))
            self.bias2 = nn.Parameter(torch.tensor(bias2, dtype=torch.float32))
        else:
            self.weights1 = [list(row) for row in weights1]
            self.bias1 = list(bias1)
            self.weights2 = [list(row) for row in weights2]
            self.bias2 = list(bias2)
        self.morphisms["layer1"].func = self.linear_layer(self.weights1, self.bias1)
        self.morphisms["layer2"].func = self.linear_layer(self.weights2, self.bias2)

    # ------------------------------------------------------------------
    def audit_log(self) -> List[dict]:
        return copy.deepcopy(self._audit_log)

    def export_audit_log(self) -> str:
        export_data = {
            "version": "1.0",
            "entries": copy.deepcopy(self._audit_log),
        }
        sign_json = json.dumps(export_data, sort_keys=True)
        key = os.getenv(EXPORT_SIGNING_KEY_ENV, "dev-key")
        export_data["signature"] = hmac.new(key.encode(), sign_json.encode(), hashlib.sha256).hexdigest()
        return json.dumps(export_data, indent=2)

    @staticmethod
    def verify_exported_log(export_str: str) -> bool:
        data = json.loads(export_str)
        signature = data.pop("signature", None)
        if not signature:
            return False
        sign_json = json.dumps(data, sort_keys=True)
        key = os.getenv(EXPORT_SIGNING_KEY_ENV, "dev-key")
        expected = hmac.new(key.encode(), sign_json.encode(), hashlib.sha256).hexdigest()
        return signature == expected

    def get_eu_compliance_report(self) -> dict:
        """Return a minimal EU AI Act transparency/traceability report."""
        forward_logged = any(e.get("event") == "forward" for e in self._audit_log)
        audit_chain_valid = self.verify_audit_chain()
        export_valid = CatNet.verify_exported_log(self.export_audit_log())
        return {
            "eu_ai_act": {
                "transparency": forward_logged,
                "traceability": audit_chain_valid,
                "data_access": export_valid,
            }
        }

    def verify_audit_chain(self) -> bool:
        for i, entry in enumerate(self._audit_log):
            if "crypto_hash" not in entry:
                return False
            entry_for_hash = {k: v for k, v in entry.items() if k != "crypto_hash"}
            expected = hashlib.sha256(json.dumps(entry_for_hash, sort_keys=True).encode()).hexdigest()
            if entry["crypto_hash"] != expected:
                return False
            if i == 0:
                if entry.get("previous_hash"):
                    return False
            else:
                if entry.get("previous_hash") != self._audit_log[i - 1]["crypto_hash"]:
                    return False
        return True


# Simple demo usage
if __name__ == "__main__":
    net = CatNet(2, 2, 2)
    out = net.forward([0.5, -0.1])
    print("out", out)
    export = net.export_audit_log()
    print(export)
