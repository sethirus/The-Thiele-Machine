# Audit trail status

A narrative audit dated 2025-11-07 previously accompanied the partition
scaling experiments and highlighted that the published reruns failed three of
four preregistered criteria, that the final proof executable did not reach the
claimed fixed point, and that Operation Cosmic Witness used a fragile
single-threshold rule. Those findings remain accurate for the archived runs in
`experiments/legacy/`, but they are now explicitly marked as diagnostic
history.

The active workflow is instead governed by the ephemeral gate in
`scripts/run_partition_ephemeral.py`, the reconciled final-instrument payload,
and the updated Operation Cosmic Witness search (explicitly labelled as a toy
CHSH-style decision rule over 16 scalar CMB temperatures). Auditors should
treat the legacy note as superseded by the new protocol while keeping it
available for context.
