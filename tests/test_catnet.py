import os
import sys

sys.path.append(os.path.dirname(os.path.dirname(__file__)))

from catnet import CatNet


def compose(f, g):
    return lambda x: g(f(x))


def test_categorical_laws_and_audit():
    net = CatNet(2, 2, 2)
    x = [0.1, -0.2]
    f = net.morphisms["layer1"].func
    g = net.morphisms["relu"].func
    h = net.morphisms["layer2"].func

    lhs = compose(compose(f, g), h)(x)
    rhs = compose(f, compose(g, h))(x)
    assert all(abs(a - b) < 1e-9 for a, b in zip(lhs, rhs))

    assert net.morphisms["id_input"].func(x) == x

    net.forward(x)
    log = net.audit_log()
    assert log[-1]["event"] == "forward"
    exported = net.export_audit_log()
    assert CatNet.verify_exported_log(exported)
    assert net.verify_audit_chain()


def test_eu_compliance_report():
    net = CatNet(2, 2, 2)
    net.forward([0.2, -0.1])
    report = net.get_eu_compliance_report()
    assert report["eu_ai_act"]["transparency"]
    assert report["eu_ai_act"]["traceability"]
    assert report["eu_ai_act"]["data_access"]


def test_assert_consistency_logging():
    net = CatNet(2, 2, 2)
    assert net.assert_consistency([1, 2, 3])
    assert not net.assert_consistency([-1])
    log = net.audit_log()
    assert any(e.get("event") == "assert_consistency" and e.get("result") for e in log)
    assert any(e.get("event") == "assert_consistency" and not e.get("result") for e in log)
