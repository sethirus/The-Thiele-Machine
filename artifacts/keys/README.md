# Signing keys

## `bitlock_ed25519_private.pem` — NON-SECRET reproducibility fixture

This Ed25519 keypair is a **committed test fixture, not a secret.** It exists
so the bitlock manifest (`artifacts/isomorphism_bitlock_manifest.json`) and the
stack-audit summary (`artifacts/proof_gate/stack_audit_summary.json`) are
**byte-for-byte reproducible** by anyone who checks out the repository.

Because the private key is public, a signature made with it certifies
**integrity** (the signed content was not altered after signing with this known
key) but **not authenticity** (it says nothing about *who* signed). The manifest
already embeds its own `public_key_hex`, so the signature is self-certifying —
it is a deterministic content tag, not an authorship proof. Anyone can re-sign
the same content with their own key; that is expected, and is why this key is
safe to publish.

Do **not** use this key for anything that requires authenticity. Real secrets
never live in the tree — they are git-ignored (see the `Certificates / keys`
block in the repo `.gitignore`).

### Producing an authenticated signature

Pass an external key explicitly:

```sh
python3 scripts/generate_bitlock_manifest.py --signing-key-file /path/to/private.pem
python3 scripts/audit_stack.py              --signing-key-file /path/to/private.pem
```

or set the environment variable once:

```sh
export THIELE_BITLOCK_SIGNING_KEY=/path/to/private.pem
```

When neither is supplied the scripts fall back to this fixture and print a
warning, so an integrity-only signature can never be silently mistaken for an
authenticated one (`scripts/_signing_key.py`).

### .gitignore policy

`.gitignore` ignores `artifacts/keys/*.pem` with an explicit allowlist for this
documented fixture. Any *other* `.pem` you drop here stays local and will not be
committed.
