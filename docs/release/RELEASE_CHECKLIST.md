1) Bump version; ensure LICENSE = Apache-2.0 and files above exist.
2) Create source tarball; compute SHA-256; commit `artifacts/MANIFEST.sha256`.
3) Create a signed tag:  git tag -s v1.0.3 -m "Thiele Machine v1.0.3"
4) GitHub release: attach tarball + MANIFEST + DEFENSIVE_PUBLICATION.md PDF.
5) Enable Zenodo GitHub archiving; publish release -> gets DOI. Add DOI to CITATION.cff.
6) Submit repo URL to Software Heritage; record SWHID in DEFENSIVE_PUBLICATION.md.
7) Upload DEFENSIVE_PUBLICATION.md (as PDF), RESULTS.md, and the release tarball to OSF Preprints.
8) (Optional) arXiv: upload PDF with code DOI in the metadata.
9) Post the SHA-256s and DOI on your project site/README so third parties can verify.