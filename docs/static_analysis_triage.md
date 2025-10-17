# Static Analysis Triage

Bug Hunter was re-run after refactoring the demo scripts to remove unsafe `eval` usage. The current report records eight findings, all of which are confined to trusted interpreter surfaces or intentionally vulnerable fixtures that are retained only for testing.【db3a04†L1-L2】【746560†L1-L37】

| Finding | Location | Disposition | Notes |
| --- | --- | --- | --- |
| Dynamic `exec`/`eval` in the Thiele VM | `thielecpu/vm.py`【46c26c†L170-L188】【3fdea6†L330-L347】【6ee607†L568-L578】 | **Accepted** | The virtual machine must execute user-supplied Thiele programs, host inline Python payloads, and replay symbolic witnesses. These interpreter entry points are the core of the architecture; they are guarded by deterministic inputs and μ-bit receipts rather than traditional sandboxing. |
| Vulnerable repository fixture | `tests/data/vulnerable_repo/insecure.py`【9c193c†L1-L24】 | **Documented** | This intentionally insecure sample is preserved for regression tests of the Bug Hunter harness itself; it is not imported by production code and should remain quarantined under `tests/`. |
| Legacy demonstration script | `archive/scripts/demonstration.py`【5c46ca†L8-L19】 | **Archived** | The archived demo reproduces the original “blind vs sighted” comparison and is no longer executed in the hardened workflow. It remains in `archive/` for historical context. |

No additional action is required; the refactoring eliminated dynamic evaluation from the public demos while the remaining findings correspond to deliberate interpreter surfaces or quarantine fixtures.
