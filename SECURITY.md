# Security Policy

This is a research project. If you believe you have found a security vulnerability, please open a GitHub issue with the `security` label. We do not currently offer a bug bounty.

## Signing keys

- The repository no longer ships the Ed25519 kernel signing key. On first use the tooling generates a local keypair in `kernel_secret.key` (private) and `kernel_public.key` (public) with restrictive filesystem permissions. If you need to supply your own keys, place them at those paths or set the `THIELE_KERNEL_SIGNING_KEY`/`THIELE_KERNEL_VERIFY_KEY` environment variables.
- Signatures created **before 2025-11-07** used a private key that was bundled with the repository. They should be treated as demonstrative only and must not be relied on for authenticity.
- Generated keys are intended for local experiments and demos. Operators running production infrastructure should provision their own key material (see `scripts/provision_keys.py`) and set `THIELE_PRODUCTION=1` to disable automatic key creation.
