Release verification checklist
=============================

This short checklist describes how to independently verify the v1.0.3 release artifacts and metadata.

1. Obtain the release tarball
   - Download `The-Thiele-Machine-v1.0.3.tar.gz` from the GitHub release page or from the project artifacts.

2. Verify the SHA-256 checksum
   - Run: `sha256sum The-Thiele-Machine-v1.0.3.tar.gz` and confirm it matches the manifest entry in `artifacts/MANIFEST.sha256` once the release tarball is minted.
   - Expected value (v1.0.3): _publish the hash from the packaged release tarball_.

3. Verify the GPG detached signature (if present)
   - If the release page includes `The-Thiele-Machine-v1.0.3.tar.gz.asc`, download it alongside the tarball.
   - Import the maintainer's public key (if you do not already trust it):
     - `gpg --import GPG_PUBLIC_KEY.asc`
   - Verify: `gpg --verify The-Thiele-Machine-v1.0.3.tar.gz.asc The-Thiele-Machine-v1.0.3.tar.gz`
   - Expected fingerprint: `ACF1665CDBD486D22E87B3615127D27049B531F1` (compare carefully before trusting).

4. Verify the Git tag signature (optional / user action required)
   - After the maintainer signs the annotated git tag locally and pushes it, fetch tags and verify:
     - `git fetch --tags`
     - `git tag -v v1.0.3`
   - GitHub will display a "Verified" badge if the tag is signed with the maintainer's public key uploaded to GitHub.

5. Verify Software Heritage provenance
   - The expected Software Heritage snapshot for the release is
     `swh:1:dir:d3894a5c31028e8d0b6d3bcdde9d257148d61e59`.
   - You can query the Software Heritage API or visit https://archive.softwareheritage.org/ to inspect the archived snapshot.

6. Verify metadata (CITATION and MANIFEST)
   - Inspect `CITATION.cff` for the preferred citation and identifiers (DOI, SWHID, tarball SHA, and GPG fingerprint).
   - Once the release is packaged, confirm `artifacts/MANIFEST.sha256` includes the tarball entry and that the recorded SHA matches the value above.

7. Reproduce the computation and receipts
   - Create a Python virtualenv and install project deps: `pip install -e .`
   - Regenerate canonical receipts: `python3 demonstrate_isomorphism.py` (recommended).
     If you require the broader set of experiments, run `python attempt.py` instead.
   - Run the verifier: `python scripts/challenge.py verify receipts` and confirm it reports successful verification and the expected μ-bit accounting.
   - Optionally replay receipts in Coq: `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json`.

8. Re-run Coq verification (recommended for formal consumers)
   - Inside a container: `docker run --rm -v "$PWD":/work coqorg/coq:8.18 bash -c "cd /work && ./coq/verify_subsumption.sh"`
   - Or install the Coq Platform locally (8.18 recommended) and run `./coq/verify_subsumption.sh`.

9. Optional: Upload artifacts to archives (maintainer action)
   - Optional publishing helpers have been archived to `scripts/optional_publish/`.
     To publish, see `scripts/optional_publish/README.md` and run the helper scripts
     after making them executable and exporting your tokens.

If you complete these steps and encounter any mismatch, stop and contact the maintainers immediately (see `CONTACT.txt`).
