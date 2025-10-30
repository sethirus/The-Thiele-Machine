# Contributing

Thank you for helping test the falsifiable predictions of the Thiele Machine.  The project welcomes two broad classes of
contributions:

1. **Replication artefacts.** New proofpacks, datasets, and analytics that reinforce or challenge the μ-ledger predictions.
2. **Counterexample hunts.** Targeted attempts to violate the Landauer inequality or to make blind solvers beat sighted ones.

## Ground rules

- Run `python -m tools.falsifiability_analysis --update-readme README.md` before opening any pull request.  Commits must include
  the refreshed README dashboard if the metrics change.
- Run `python -m tools.generate_admit_report` and stage `ADMIT_REPORT.txt` whenever Coq sources move.
- Keep philosophical commentary in `documents/philosophy.md`; pull requests should focus on reproducible data, code, or proofs.
- Prefer small, well-documented artefacts over monolithic dumps.  Each proofpack directory should contain a `README` describing
  how it was generated and the hypotheses it tests.

## Reporting counterexamples

1. Open a GitHub issue and label it `counterexample`.
2. Include:
   - the exact CLI invocation used to trigger the anomaly,
   - the full stdout/stderr logs,
   - a tarball or gist with the minimal subset of ledgers needed to reproduce the failure,
   - system details (OS, Python version, CPU/GPU, temperature assumptions).
3. Re-run the falsifiability scan and paste the relevant section of the README dashboard showing the negative slack or
   suspicious ratio.
4. Expect maintainers to request independent confirmation.  Please respond quickly so we can determine whether the law has been
   falsified.

## Submitting replication results

1. Follow the [Replication Guide](REPLICATION_GUIDE.md) to regenerate proofpacks.
2. Commit the new `artifacts/experiments/<RUN_TAG>/` directory, the updated README dashboard, and any supporting notebooks.
3. Summarise the experimental setup and findings in the pull request description, explicitly stating whether the falsifiable
   predictions held.
4. If your run introduces new tools or dependencies, update `pyproject.toml` and document them in `REPLICATION_GUIDE.md`.

## Code style

- Python: adhere to the repository’s existing patterns; the test suite covers all public tooling.
- Coq: prefer constructive proofs.  Do not introduce new axioms without prior discussion.
- Documentation: keep README empirical and ship theory in `documents/`.

Thanks for putting the law to the test!
