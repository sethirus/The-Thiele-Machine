# PROOF_STATUS

| Axiom | Lemma(s) | Status |
| ----- | -------- | ------ |
| Conservativity | `tm_cpu_simulates_step` | ✅ |
| No-Free-Sight | – | ❌ |
| Paradox ⇒ μ=∞ | `cost_of_paradox_is_infinite` | ✅ |
| Auditability | – | ❌ |
| Subsumption | `thiele_machine_subsumes_turing_machine` | ✅ |

No-Free-Sight and Auditability are empirically witnessed by the demos and
challenge harness but currently lack mechanized proofs.

All lemmas in the mechanized development are now discharged; no admitted
proof obligations remain.
