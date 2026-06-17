"""Shared resolution of the bitlock / stack-audit signing-key path.

SECURITY NOTE
-------------
``artifacts/keys/bitlock_ed25519_private.pem`` is a NON-SECRET, committed
*test fixture*. Its only job is to make the bitlock manifest and the
stack-audit summary byte-for-byte reproducible by anyone who checks out the
repository. Because the private bytes are public, a signature made with it
certifies INTEGRITY (the signed content was not altered after signing with
this known key) but NOT AUTHENTICITY (it proves nothing about *who* signed).

Real production secrets never live in the tree: they are git-ignored (see the
``Certificates / keys`` block in ``.gitignore`` and ``kernel_secret.key``).

To produce an authenticated signature, supply an external key explicitly:

    --signing-key-file /path/to/private.pem

or set the environment variable:

    THIELE_BITLOCK_SIGNING_KEY=/path/to/private.pem

If neither is given, the committed fixture key is used as a deliberate
last-resort fallback and a warning is printed, so an integrity-only signature
can never be silently mistaken for an authenticated one.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]

# The committed, non-secret reproducibility fixture. Documented in
# artifacts/keys/README.md.
FIXTURE_KEY = REPO_ROOT / "artifacts" / "keys" / "bitlock_ed25519_private.pem"

# Environment override for an external (real) signing key.
ENV_VAR = "THIELE_BITLOCK_SIGNING_KEY"


def resolve_signing_key_path(explicit: "str | os.PathLike[str] | None", *, warn: bool = True) -> Path:
    """Resolve which private-key file to sign with.

    Precedence: explicit ``--signing-key-file`` argument, then the
    ``THIELE_BITLOCK_SIGNING_KEY`` environment variable, then the committed
    non-secret fixture (with a stderr warning). The fixture path is returned
    absolute; an explicit/env path is returned as given.
    """
    if explicit:
        return Path(explicit)

    env = os.environ.get(ENV_VAR)
    if env:
        return Path(env)

    if warn:
        try:
            shown = FIXTURE_KEY.relative_to(REPO_ROOT)
        except ValueError:
            shown = FIXTURE_KEY
        print(
            "WARNING: no signing key supplied (--signing-key-file or "
            f"${ENV_VAR}); falling back to the NON-SECRET committed fixture "
            f"{shown}. The resulting signature certifies integrity only, not "
            "authenticity. Pass an external key for an authenticated signature.",
            file=sys.stderr,
        )
    return FIXTURE_KEY
