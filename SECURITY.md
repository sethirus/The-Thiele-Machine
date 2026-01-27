# Security Policy

Thank you for your interest in reporting a vulnerability in The Thiele Machine. Please follow the guidelines below.

## Reporting a vulnerability
- Email: security@thethielemachine.org
- PGP key: available at https://thethielemachine.org/pgp.txt (if no key is available, send an encrypted message using the public key once posted)

Please include:
- A clear description of the issue and steps to reproduce
- The component(s) affected (file paths, package names, etc.)
- Any available exploit or PoC code

We will acknowledge receipt within 72 hours and provide updates on remediation.

## Policies
- We follow a 90-day disclosure policy for coordinated fixes. For critical issues we will shorten this window.
- Do not post public details before a fix has been released unless there is a safety or legal reason to do so.

## Known Advisories

### CVE-2025-53000 (nbconvert)
**Status**: Acknowledged, not applicable to CI environment  
**Description**: Windows-specific vulnerability in nbconvert's SVG-to-PDF conversion (unsafe search path DLL injection).  
**Mitigation**: This vulnerability only affects Windows users running local SVG-to-PDF conversions. Our CI runs on Linux (ubuntu-latest) and is not affected. The dependency is pulled in transitively by jupyter_server. If you need local conversion on Windows, install nbconvert in an isolated virtual environment.

## Automated scanning
This repository runs dependency and secret scanning in CI (pip-audit and gitleaks). If you find an issue that these scans missed, please report it via the contact above.
