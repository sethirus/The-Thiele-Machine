# Minimal CatNet placeholder used in tests to simulate the required interface.
from dataclasses import dataclass

@dataclass
class Morphism:
    name: str
    func: callable

class CatNet:
    def __init__(self, a, b, c):
        # minimal morphisms: layer1, relu, layer2, id_input
        self.morphisms = {
            'layer1': Morphism('layer1', lambda x: [xi * 2.0 for xi in x]),
            'relu': Morphism('relu', lambda x: [max(0.0, xi) for xi in x]),
            'layer2': Morphism('layer2', lambda x: [xi + 0.1 for xi in x]),
            'id_input': Morphism('id_input', lambda x: x),
        }
        self._audit = []

    def forward(self, x):
        self._audit.append({'event': 'forward', 'x': x})
        # compose: layer1 -> relu -> layer2
        y = self.morphisms['layer1'].func(x)
        y = self.morphisms['relu'].func(y)
        y = self.morphisms['layer2'].func(y)
        return y

    def audit_log(self):
        return list(self._audit)

    def export_audit_log(self):
        return {'exported': self._audit}

    @staticmethod
    def verify_exported_log(exported):
        return 'exported' in exported

    def verify_audit_chain(self):
        return True

    def get_eu_compliance_report(self):
        """Return EU AI Act compliance report stub."""
        return {
            'eu_ai_act': {
                'transparency': True,
                'traceability': True,
                'data_access': True,
            }
        }

    def assert_consistency(self, data):
        """Check consistency of input data (stub: passes for non-negative values)."""
        result = all(x >= 0 for x in data)
        self._audit.append({'event': 'assert_consistency', 'result': result})
        return result
