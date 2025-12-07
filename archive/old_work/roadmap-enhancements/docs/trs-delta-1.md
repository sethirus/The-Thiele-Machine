# TRS-DELTA-1: Delta Receipt Specification

## Overview

Delta receipts enable efficient updates by shipping only changed chunks with a pointer to a base `global_digest`. This dramatically reduces bandwidth for incremental updates.

## Format

```json
{
  "version": "TRS-DELTA-1",
  "base_receipt": {
    "global_digest": "abc123...",
    "source": "https://example.com/base.receipt.json"
  },
  "delta": {
    "added_files": [...],
    "modified_files": [...],
    "deleted_files": [...]
  },
  "global_digest": "def456..."
}
```

## Efficiency

For a 1% change in a large artifact:
- Full receipt: 100 MB
- Delta receipt: ~1 MB + overhead
- Compression ratio: 100×

## Implementation

### Creating Delta

```python
python3 src/thiele_receipts/delta.py \
  --base base.receipt.json \
  --new new.receipt.json \
  --out delta.receipt.json
```

### Applying Delta

```python
python3 src/thiele_receipts/replay_delta.py \
  --base base.receipt.json \
  --delta delta.receipt.json \
  --verify
```

## Algorithm

1. Compare file lists between base and new receipts
2. Identify added/modified/deleted files
3. For modified files, compute chunk-level diffs
4. Serialize only the delta
5. Verify: base + delta → new receipt

## Security

- Base receipt must be verified before applying delta
- Delta is signed independently
- Global digest computed from full state, not delta
- Prevents rollback attacks via monotonic versioning

## Use Cases

- Software updates (ship only changed binaries)
- Database snapshots (incremental backups)
- Container images (layer-based updates)
- Large datasets (scientific data versioning)
