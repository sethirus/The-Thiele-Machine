# VM + Hardware Prune Phase 2 (2026-03-01)

This archive stores files moved during classification-driven pruning.

## Pruning basis

Input classification report:
- `artifacts/inventory/vm_hardware_classification_2026-03-01.tsv`

Archive-candidate classes moved from active tree:
- `thielecpu/build/*` generated snapshots
- `thielecpu/hardware/rtl/archive/*` legacy RTL
- `thielecpu/hardware/testbench/archive/*` legacy testbenches

## Moves performed

- `thielecpu/build/thiele_ecp5.json`
- `thielecpu/hardware/rtl/archive/` (entire directory)
- `thielecpu/hardware/testbench/archive/` (entire directory)

## Additional pruning

Removed rebuildable caches from active tree:
- all `thielecpu/**/__pycache__/`

## Post-prune verification

- `make rtl-check` passes after pruning.
- Post-prune inventory:
  - `artifacts/inventory/vm_hardware_accounting_post_prune_2026-03-01.md`
