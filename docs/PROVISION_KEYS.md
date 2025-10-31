# Provisioning Kernel Keys

Operators deploying the Thiele Machine in production MUST provision an Ed25519
kernel keypair before starting the runtime with `THIELE_PRODUCTION=1`.

Use the included provisioning helper to generate a keypair locally and copy the
files to the runtime host using a secure channel (scp over a bastion, signed
USB, etc.). Example usage:

```sh
python scripts/provision_keys.py \
  --secret-path /etc/thiele/kernel_secret.key \
  --public-path /etc/thiele/kernel_public.key
```

Recommended permissions:

- Secret key file: mode 0600, owned by the runtime user
- Public key file: mode 0644 (optional), or 0600 if you prefer stricter access

Production guidance:

- Do not set `THIELE_PRODUCTION=1` until keys are provisioned and verified.
- For regulated deployments, generate keys on an air-gapped machine and transfer
  them via a verified secure channel.
- Rotate keys via an operator-driven process; follow the same steps when
  replacing keys and restart the runtime with appropriate rotation notes.

Verification: after provisioning, confirm the keypair is valid:

```py
from thielecpu.receipts import ensure_kernel_keys
ensure_kernel_keys()
```

`ensure_kernel_keys()` will refuse to auto-generate keys when
`THIELE_PRODUCTION=1` is set; this protects production from accidental
deterministic test-key use.
