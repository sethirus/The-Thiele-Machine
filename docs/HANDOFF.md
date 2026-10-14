# Hand-off for an assistant session

This file is for an assistant picking up the release work on this repository
with no other context. Read all of it before touching anything. The author is
Devon Thiele; every word of the book is his; the rules below are his.

## Standing rules

- Commits use the author's Git identity, read from the last commit
  (`git -c user.name="$(git log -1 --format=%an)" -c user.email="$(git log -1 --format=%ae)" commit ...`).
  No assistant authorship, no `Co-Authored-By` trailers, no model identifiers in
  commit messages or files.
- No release tags are created or moved, and no Zenodo deposit is made; those are the author's.
- The book (`monograph/monograph.tex`) is written in the author's first-person voice. No hedging,
  no apologising, no "a sharp reader" or "a sceptic" framings, no history of the project in the
  book. Pictures and things in prose (chairs, cells, hills, beads); letters only inside boxed
  statements and in the deliberate "Exactly" or "In the exact form" paragraphs. A reader with no
  training should be able to follow every paragraph.
- Every theorem in the book carries its proof on the page, and every result has a falsifier in
  the section "How to break this".
- Nothing goes into the book about old versions of the project.
- Tracked Coq object files (`*.vo`, `*.glob`) are build products. Never commit changed ones:
  restore them with `git checkout -- $(git ls-files '*.vo' '*.glob')` before committing.

## What the release carries

- The point, opening the book: nothing becomes something for free. A blank cell becoming a 0
  gives off heat by happening (any real device, finite time; time sets how much); keeping it is
  paid on top, in a merge (Landauer's floor, a premise, when the merged states were really
  possible) or in room. A machine with one state changes nothing, so every machine is made of
  kept distinctions, and the blank-zero-one cell is already the smallest Thiele machine.
  Certification is the sharpest case, not the point itself. The book runs in that order: Part I the
  bill, Part II what structure is made of, Part III established, Part IV checking it.
- The bill, Part I (What a chair is, A record and a toll, Why the toll isn't arbitrary,
  Learning borrows, committing pays); `minimal/HeatOrRoom.v` (the run form and the exact retention bound).
- The section "What a chair is" in Part I: the step law, the write as a merge, recurrence for
  reversible machines, the noisy chairs (both directions, collision weight and Shannon entropy),
  the quantum chairs, time's bill, the same bill at every scale, and the laboratory instances; the
  bead erasure there is a simulation (`scripts/bead_erasure_sim.py`, needs numpy), and
  `scripts/break_it.py` searches every small machine for counterexamples (a search, not warrant). Kernel files:
  `minimal/StepLaw.v`, `KeptDistinction.v`, `HaltingHole.v`, `NondetChairs.v`, `Recurrence.v`,
  `NoisyChairs.v`, `GibbsGap.v`, `BrownianComputer.v`, `QuantumChairs.v` (the last needs the
  Mathematical Components library: `libcoq-mathcomp-field`).
- The specification (`monograph/thiele_machine_math_spec.tex`), `README.md`,
  `THIELE_MACHINE.txt`, `TECHNICAL_DISCLOSURE.md`, `docs/THEOREM_MEANINGS.md`, `CITATION.cff`
  and `.zenodo.json` carry the same results and the version 4.1.0.

## The gates, in order

```
cd coq && coq_makefile -f _CoqProject -o Makefile.coq && make -j4 -f Makefile.coq
python3 build/probe/build_full_probe.py
bash scripts/generate_assumption_receipt.sh
python3 scripts/sync_assumption_receipt_readme.py
python3 scripts/check_assumption_consistency.py
make assumption-receipt-check
python3 scripts/inquisitor.py
python3 scripts/coq_proof_scope.py validate_alignment
make vacuity-audit
cd monograph && bash build_monograph.sh && cd page-composition && python3 build.py && python3 review.py
python3 -m pytest -q
```

`monograph/COMPANION_CHECKS.txt` pins the receipt's SHA-256 and the corpus digest; after a
receipt regeneration, update it from `artifacts/print_assumptions_all_proofs.json` (the test
`tests/test_edition_numbers.py` says exactly what it expects). Build products under `coq/` and
`minimal/` are compared against the tracked copies by CI's "Purge stale tracked Coq .vo files"
step, so a clean rebuild is the reference.

## How to review adversarially

Read the diff of the last release commits against their parent. For every sentence that states a
result, find the theorem that states it and the proof on the page; if either is missing, add it or
cut the sentence. For every theorem, find its falsifier in "How to break this". For every Coq name
cited in any document, confirm it exists and has an entry in `docs/THEOREM_MEANINGS.md`
(`tests/test_theorem_meanings.py`). For every number quoted from an experiment, confirm it against
the cited paper. Run the gates. Fix what fails. Commit under the author's identity and push to the
branch the session was given. When two consecutive passes find nothing to change and CI is green
on both workflows (`ci.yml` on push, `ci-full.yml` nightly), the work is done: disable the routine
that started the session and say so.
