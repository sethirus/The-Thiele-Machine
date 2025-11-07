# Signing and Trust Setup

Setting up signing keys and trust manifests ensures Thiele receipts remain
cryptographically meaningful. This guide walks through the most common
workflows: generating keys, signing receipts, and verifying them with trust
anchors.

## 1. Generate an Ed25519 key pair

Use the helper shipped with the repository:

```bash
python3 tools/sign_receipts.py generate
```

The command prints a hex-encoded private key and matching public key. Store the
private key somewhere safe, for example:

```
~/.thiele/keys/my-project.key
```

Record the public key (or publish it) so verifiers can authenticate receipts.

## 2. Sign receipts when you create them

Pass the `--sign` flag to `create_receipt.py`, along with a descriptive key ID
that your trust manifest will reference later.

```bash
# Single file
python3 create_receipt.py path/to/artifact \
    --sign ~/.thiele/keys/my-project.key \
    --key-id my-project-2025

# Entire directory
python3 create_receipt.py --directory ./dist \
    --sign ~/.thiele/keys/my-project.key \
    --key-id my-project-2025
```

The key ID is not cryptographically required but makes trust manifests far more
useful. If you omit `--key-id`, the CLI emits a hint reminding you to set one.

> **Unsigned receipts:** The CLI rejects unsigned receipts by default. Use
> `--allow-unsigned` only for testing or legacy migrations.

## 3. Create or update a trust manifest

Trust manifests map signer key IDs to the public keys you trust and restrict
where each key applies. A minimal example:

```json
{
  "trusted_keys": {
    "my-project-2025": {
      "public_key": "0123deadbeef...",
      "patterns": ["receipts/*.json"]
    }
  }
}
```

Save the manifest alongside your receipts (for example, `receipts/trust_manifest.json`).
You can maintain multiple manifests for different contexts.

## 4. Verify receipts with trust anchors

There are two equivalent ways to provide trust when verifying receipts.

### Option A: Explicit public key

```bash
python3 tools/verify_trs10.py artifact.receipt.json \
    --trusted-pubkey 0123deadbeef...
```

### Option B: Trust manifest

```bash
python3 tools/verify_trs10.py artifact.receipt.json \
    --trust-manifest receipts/trust_manifest.json
```

The replay verifier supports the same flags for TRS-0 receipts:

```bash
python3 verifier/replay.py receipts/ \
    --trust-manifest receipts/trust_manifest.json
```

### Auto-discovery rules

Both CLIs look for trust manifests automatically when you omit
`--trust-manifest`:

- `tools/verify_trs10.py` checks:
  1. `trust_manifest.json` next to the receipt.
  2. `receipts/trust_manifest.json` relative to the repository root.
- `verifier/replay.py` checks:
  1. `trust_manifest.json` next to the provided file, or inside the provided directory.
  2. `receipts/trust_manifest.json` relative to the repository root.

If neither location exists, supply `--trusted-pubkey` or create a manifest.

## 5. Troubleshooting

- **“Receipt must be signed with Ed25519”** – Ensure you passed `--sign` to
  `create_receipt.py` or used `tools/sign_receipts.py sign` to apply a
  signature.
- **“No trust manifest or trusted public key”** – Provide
  `--trust-manifest <path>` or `--trusted-pubkey <hex>`. Use
  `--allow-unsigned` only when you intentionally want to bypass signature
  checks (for example, during a migration).
- **Manifest mismatch errors** – Verify that the key ID in the receipt matches
  the manifest entry and that the entry’s `public_key` field contains the
  signer’s current public key.

For a deeper dive into receipt structure and workflows, see the
[Receipt Guide](RECEIPT_GUIDE.md).
