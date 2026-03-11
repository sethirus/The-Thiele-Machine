# partition_demo.asm
# Demonstrates PNEW, PSPLIT, PMERGE, PDISCOVER.
# Partition graph is managed externally by the host driver.
# Hardware charges mu and increments partition_ops counter.

PNEW 0 0 1          # Create partition, module_id=0, cost=1
PNEW 1 0 1          # Create partition, module_id=1, cost=1
PSPLIT 0 1 2 1      # Split module 0 into 1 and 2, cost=1
PMERGE 1 2 1        # Merge modules 1 and 2, cost=1
PDISCOVER 0 0 1     # Record discovery in module 0, cost=1
HALT 0
