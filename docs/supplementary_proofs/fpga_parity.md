# FPGA Log Cross-Compilation

The script [`cross_compile_fpga_logs.py`](./cross_compile_fpga_logs.py) parses the
hardware verification log at
[`audit_logs/agent_hardware_verification.log`](../audit_logs/agent_hardware_verification.log)
and compares the sequential/autonomous µ-ledger totals against the canonical
values asserted in the HDL test bench
[`hardware/synthesis_trap/thiele_graph_solver_tb.v`](../hardware/synthesis_trap/thiele_graph_solver_tb.v).

Running the script produces `hardware_software_parity.json`, e.g.:

```bash
python supplementary_proofs/cross_compile_fpga_logs.py
```

The resulting JSON report confirms parity for all µ-ledger counters:

```json
{
  "hardware_totals": {
    "sequential": {
      "mu_question_bits": 1288,
      "mu_information_q16": 934848,
      "mu_total_q16": 85345216
    },
    "autonomous": {
      "mu_question_bits": 1288,
      "mu_information_q16": 934848,
      "mu_total_q16": 85345216
    }
  },
  "expected_totals": {
    "mu_question_bits": 1288,
    "mu_information_q16": 934848,
    "mu_total_q16": 85345216
  },
  "parity_checks": {
    "sequential": {
      "mu_question_bits": true,
      "mu_information_q16": true,
      "mu_total_q16": true
    },
    "autonomous": {
      "mu_question_bits": true,
      "mu_information_q16": true,
      "mu_total_q16": true
    }
  }
}
```

Auditors can re-run the script to regenerate the parity report after rebuilding
hardware or software artefacts, ensuring that the FPGA traces stay aligned with
the specification encoded by the software ledger.
