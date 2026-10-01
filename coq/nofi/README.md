# No-Free-Insight (NoFI)

**Mission:** No-Free-Insight abstraction proofs establishing fundamental limits on information extraction.

## Structure

- `Instance_Kernel.v` - Instance Kernel - Key results: Certified_spec, trace_run_mu_monotone (+2 more)
- `MuChaitinTheory_Interface.v` - Mu Chaitin Theory Interface
- `MuChaitinTheory_Theorem.v` - Mu Chaitin Theory Theorem - supra_cert_run_implies_paid_payload, mu_info_nat_le_from_mu_budget, proves_bits_bounded_by_description. These hold for any instance of `MU_CHAITIN_THEORY_SYSTEM`, whose `priced` field asks every instruction to be priced; the VM's schedule is not (`current_schedule_not_globally_cert_priced`), so the VM has no instance, and the main bound takes the μ payment as an interface field.
- `MuChaitinTheory_TraceLocal.v` - Mu Chaitin Theory with trace-local pricing: only instructions on the theory's traces must be priced, the μ payment is derived from the kernel certification theorem, and one fixed VM run instantiates the interface (kernel_trace_instance_bound: k <= 9) - Key results: supra_cert_paid_payload_trace_local, proves_bits_bounded_by_description_trace_local, kernel_trace_instance_bound
- `NoFreeInsight_Interface.v` - No Free Insight Interface
- `NoFreeInsight_Theorem.v` - No Free Insight Theorem - Key results: no_free_insight

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `Instance_Kernel.v` | 0 | ✅ |
| `MuChaitinTheory_Interface.v` | 0 | ✅ |
| `MuChaitinTheory_Theorem.v` | 0 | ✅ |
| `MuChaitinTheory_TraceLocal.v` | 0 | ✅ |
| `NoFreeInsight_Interface.v` | 0 | ✅ |
| `NoFreeInsight_Theorem.v` | 0 | ✅ |

**Result:** All 6 files verified with 0 admits.
