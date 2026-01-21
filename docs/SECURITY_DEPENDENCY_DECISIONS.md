# Dependency security decisions (short)

This document records triage and mitigation decisions for Python dependencies identified by `pip-audit`.

- `ecdsa` (CVE-2024-23342): timed side-channel on P-256; no upstream fix planned. Action: **excluded** from main `requirements.txt` and `requirements_fixed.txt`. Projects should prefer **Ed25519 (PyNaCl)** or **cryptography** for signature operations. If ECDSA is required, pin to a vetted implementation and run platform-specific mitigations (constant-time HSM, hardware signing, or audited libraries).

- `nbconvert` (CVE-2025-53000): Windows-specific search-path exploitation when converting SVG→PDF. Action: **excluded** from main requirements; kept in `requirements-optional.txt` with instructions. CI runs on Linux and does not use nbconvert; developers needing notebook→PDF conversions should do so in an isolated Windows host or use a patched converter.

- `biopython` (CVE-2025-68463): XXE vulnerability via Bio.Entrez. Action: Not required by the project; listed in `requirements-optional.txt` as a caution. If needed, use `defusedxml` and parsing utilities with secure settings.

CI: Added `pip-audit` baseline and will fail on newly introduced HIGH/CRITICAL vulns (see CI patch). This ensures new vulnerabilities are triaged quickly.

If you want, I can prepare a small PR/patch to reintroduce safe ECDSA usage via `cryptography` (EC) APIs if you prefer maintaining ECDSA compatibility with constant-time primitives.
