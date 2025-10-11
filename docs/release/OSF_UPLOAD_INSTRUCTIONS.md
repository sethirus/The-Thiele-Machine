OSF upload instructions
=======================

To upload release artifacts to the Open Science Framework (OSF) you can use
the `osfclient` command-line tool. These instructions summarise the steps:

1. Create a personal access token on OSF:
   - Visit https://osf.io/settings/tokens/ and create a new token with "osf.full_write" scope.
   - Copy the token somewhere safe; treat it like a password.

2. Install the client:
   - `pip install osfclient`

3. Identify your project node id:
   - The node id is visible in the project URL: `https://osf.io/<NODE_ID>/`

4. Upload files using the helper script (preferred):
   - `OSF_TOKEN=<token> OSF_NODE_ID=<node_id> ./scripts/publish_to_osf.sh`

If you prefer not to use `osfclient`, OSF also provides a REST API for
uploads, but it requires a multi-step upload flow. The helper script is
intended to be a light wrapper around `osfclient` to reduce friction.

Security note: never commit API tokens into the repository. Use CI/secret
management or local environment variables when running these scripts.
OSF Submission Instructions (for maintainers)
============================================

1. Create a project or preprint on OSF: https://osf.io/preprints/
2. Upload the following files (suggested order):
   - `The-Thiele-Machine-v1.0.3.tar.gz`
   - `documents/The_Thiele_Machine.pdf`
   - `artifacts/MANIFEST.sha256`
   - `DEFENSIVE_PUBLICATION.md`
   - `CITATION.cff`
   - `LICENSE`, `PATENT-PLEDGE.md`, `NOTICE`, `RELEASE_CHECKLIST.md`
3. Fill in metadata: Title, Authors, Abstract (use first page of PDF),
   Keywords: Thiele Machine, Partition Logic, Coq, SMT, Verilog.
4. Publish and record the OSF DOI in `DEFENSIVE_PUBLICATION.md`.
