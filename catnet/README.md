# CatNet

CatNet instantiates the Thiele Machine in the category of vector spaces. Objects
are layers and morphisms are differentiable maps. Composition is computation and
forward passes are logged in a tamper-evident audit chain signed via HMAC.
It also exposes a minimal EU AI Act transparency report via `get_eu_compliance_report()`.

The file `coq/catnet/coqproofs/CatNet.v` contains a Coq proof that appending an
entry preserves the audit log's cryptographic chain, providing a
machine-checked tamper-proof guarantee for the log structure.

```bash
python -m catnet.demo_mnist
python -m catnet.demo_control
```
