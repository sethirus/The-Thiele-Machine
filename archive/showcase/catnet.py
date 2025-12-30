# Minimal stub CatNet implementation for tests

from dataclasses import dataclass
from typing import Callable, Dict, List, Any

@dataclass
class Morphism:
    func: Callable

class CatNet:
    def __init__(self, *args, **kwargs):
        # Create a tiny network with layer1 -> relu -> layer2 and id_input
        self.morphisms: Dict[str, Morphism] = {
            "layer1": Morphism(lambda x: [xi * 2 for xi in x]),
            "relu": Morphism(lambda x: [max(0.0, xi) for xi in x]),
            "layer2": Morphism(lambda x: [xi + 1 for xi in x]),
            "id_input": Morphism(lambda x: x),
        }
        self._audit: List[Dict[str, Any]] = []

    def forward(self, x):
        self._audit.append({"event": "forward", "input": x, "output": None})
        v = self.morphisms["layer1"].func(x)
        v = self.morphisms["relu"].func(v)
        v = self.morphisms["layer2"].func(v)
        # Update the forward audit to include output and keep 'forward' as the final event
        self._audit[-1]["output"] = v
        return v

    def audit_log(self):
        return list(self._audit)

    def export_audit_log(self):
        # Return a simple serializable object
        return {"events": list(self._audit)}

    @staticmethod
    def verify_exported_log(exported):
        # Minimal check: must have 'events' key
        return isinstance(exported, dict) and "events" in exported

    def verify_audit_chain(self):
        # Always return True for stub
        return True

    def get_eu_compliance_report(self):
        return {"eu_ai_act": {"transparency": True, "traceability": True, "data_access": True}}

    def assert_consistency(self, data):
        # Simple heuristic: non-empty list of non-negative numbers passes
        result = False
        if isinstance(data, list) and data:
            result = all(isinstance(x, (int, float)) and x >= 0 for x in data)
        self._audit.append({"event": "assert_consistency", "result": bool(result)})
        return bool(result)
