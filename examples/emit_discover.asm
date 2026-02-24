# emit_discover.asm
# Demonstrates EMIT and PDISCOVER together.
# EMIT      op_a op_b cost  → Emit an observable event (visible in hw trace).
# PDISCOVER op_a op_b cost  → Query whether a partition is discoverable (no-op probe).
# All operands are numeric (module / partition IDs), not register names.

PNEW 0 0 1          # create fresh partition at slot 0
EMIT 0 1 1          # emit event: module=0, channel=1
PDISCOVER 0 1 1     # discover: partition-0 vs context-1
EMIT 1 0 1          # emit event: module=1, channel=0
PDISCOVER 1 0 1     # discover: partition-1 vs context-0
EMIT 0 0 2          # emit higher-cost event
PDISCOVER 0 0 2     # final discovery probe

HALT 0
