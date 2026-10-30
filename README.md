# The Thiele Machine

The Thiele Machine is a model of computation with a price in the step where something settles and stays settled. It computes nothing a Turing machine can't. What it adds is the price, and a way to see what keeping an answer takes.

This repository holds the whole of it: the book that argues the model, a companion with the exact statements, a formal development that checks the same statements, the tooling and tests that keep that development honest, the record of the earlier builds, and the defensive publication that keeps all of it free to use.

[The book](monograph/monograph.pdf) · [Exact statements](monograph/thiele_machine_math_spec.pdf) · [Plain-text introduction](THIELE_MACHINE.txt) · [Formal development](coq/README.md) · [Reproduction](docs/REPRODUCTION.md)

## The picture

Here's a computer you can run with a pencil. Write 3 on a scrap of paper. The move is: erase the number and write the next one up. Tell it to stop at 5, and ask one question of each number: is it done? 3, no. 4, no. 5, yes. Once it says yes it keeps saying yes, because the machine has stopped.

A machine that has stopped is still somewhere on the next tick. 5 goes to 5. Draw the arrows: 4 goes to 5, and 5 goes to 5. Two different starting places, one landing place. Standing on 5, you can't tell whether you just got there or have been there all along.

Try to dodge it. Let the stopped machine rock between 5-tick and 5-tock, both saying done. Now 4 goes to 5-tick and 5-tock goes to 5-tick: two arrows still land on one spot. The one way out is to never land anywhere twice, writing something new on every tick, and on a finite sheet the paper runs out.

So whenever a machine settles an answer and keeps it, two states become one, or it uses up fresh paper on every tick for as long as it runs. That part isn't a choice. You drew it, and the book proves it for any machine that goes from one state to a next. What I do with it is a choice, and I say so: I charge for the move where the answer goes from not done to done.

## The definition

A thing. Moves that take it to the next thing. A way to tell how settled the thing is, where settled never goes back to unsettled. Some run, from a start you pick, that actually settles it more than it was. A price on every move, nothing or more, never a refund. And one rule, the toll: a move that settles something more than it was costs something.

Settled can be yes or no, or a checklist of ticks that don't come off. When something other than the machine picks what happens next, chance or a person or a message coming in, each way it can go is its own move, and the picking sits outside the machine.

Turing's machine already has something that settles and stays settled: whether it has stopped. What it doesn't have is a price on the move that stops it. Put one in and a Turing machine that ever stops fits the definition. Cover a Thiele machine's record and set the price of settling to zero, and what's left is a bare machine that steps: every one of them, Turing's included, is a Thiele machine with a blindfold on.

One more condition does a lot of work, and it's one you put on a machine, not part of the definition. A record is **established** when it goes up only right after a passing check of the very claim it records, with nothing that claim is about changed in between. Two computers can end with the same sorted list, one checked and one copied. A ticked box that only goes up after the check tells them apart.

## What's in this repository

### The book and its companions

- [`monograph/monograph.pdf`](monograph/monograph.pdf), *The Thiele Machine: No Free Insight*, second edition, with its source (`monograph.tex`) and a plain-text copy (`monograph.txt`). Every argument is made on the page, with the reader, and chapter 22 sorts every claim into shown, chosen, assumed, cited, thesis, or not claimed.
- [`monograph/thiele_machine_math_spec.pdf`](monograph/thiele_machine_math_spec.pdf), the exact statements: each definition and each result the book shows, with its hypotheses written out and a pointer to the chapter that argues it.
- [`monograph/checks/`](monograph/checks/): a Python check for every chapter that counts something, trying every small case, and short formal proofs of the newer results. [`proof_map.md`](monograph/checks/proof_map.md) maps each line of the ledger to the check and the proofs that cover it.
- [`THIELE_MACHINE.txt`](THIELE_MACHINE.txt), the short version in plain text.

### The formal development

- [`coq/`](coq/README.md): the model and its results in Coq 8.18. [`coq/kernel/`](coq/kernel/README.md) holds the definition over any order and the member predicate (`foundation/`), the toll and its consequences on finite machines with their log, entropy and heat forms (`nfi/`), windows and the pointer criterion (`frontier/`), narrow models of external systems such as Certificate Transparency, proof-carrying code, TPM quotes, Casper FFG and gas metering (`reductions/`), and a two-state calorimeter protocol (`thermodynamic/`). [`coq/RESULTS.md`](coq/RESULTS.md) lists what the formal check covers and its status.
- [`minimal/`](minimal/): the small models on the Coq standard library alone, among them the smallest machine, the step law, merge or fresh states, recurrence, the noisy and quantum forms, and the verifier collision.

The arguments stand on the book's pages; the formal development is a tool for catching mistakes in them, not a reason to believe them. It's held to its own gates: every proof builds with nothing admitted, no theorem depends on a project-local axiom, the assumption receipt (`artifacts/print_assumptions_all_proofs.json`) records the axioms every named declaration uses, a vacuity gate checks that the headline theorems aren't true for an empty reason, the Inquisitor audits proof hygiene, and `coqchk` rechecks every module.

### Tooling and tests

- [`scripts/`](scripts/): the build and audit tooling, among them `reproduce_coq.py` (a fresh source-only rebuild), the receipt and vacuity scripts, the Inquisitor, `break_it.py` (a search of every small machine for counterexamples to the counting results, with a control for each premise) and `bead_erasure_sim.py` (a simulation of a bead-erasure model, not a measurement).
- [`tests/`](tests/): the pytest suite, which runs the book's checks, the searches, the document checks and the formal gates.
- [`docs/`](docs/): how to reproduce everything ([`REPRODUCTION.md`](docs/REPRODUCTION.md)), what counts as proved, tested or simulated ([`ASSURANCE.md`](docs/ASSURANCE.md)), and which generated files are kept ([`ARTIFACTS.md`](docs/ARTIFACTS.md)).

```sh
make verify        # compile the axiom-free core in minimal/ and run the clean-room measurement
make coq-gate      # build every proof and fail on any Admitted
make test          # run the test suite
```

### Earlier builds

The model has been built more than once, and each build is kept where it can be checked:

- Release v3.3.0 carried a 51-instruction virtual machine, an extracted OCaml runner, a Kami CPU, generated Verilog and an FPGA bitstream, all proved to obey the toll.
- Release v4.1.1 carried a small two-counter machine whose record goes up only after a checked, committed and certified claim, its universal programs, a verified compiler, and the CHSH and Tsirelson mathematics, with the first edition of the book.
- [`archive/`](archive/README.md) keeps the sources set aside from the main tree, the first edition of the book among them. None of it is built or tested with the main tree; check out the tag it names to run it.

### Defensive publication

[`TECHNICAL_DISCLOSURE.md`](TECHNICAL_DISCLOSURE.md) records every concept in this repository with its dates and locations, so no one can claim it as new. The [patent pledge](PATENT_PLEDGE.md) is my commitment not to sue anyone for patent infringement over using, building or describing any of it, unless they sue first.

## What the book shows

Each of these is argued on the page, with the reader, under the conditions its chapter states.

- **Keeping takes a merge or fresh paper.** Every step of a machine with one next state lands somewhere new, makes two arrows meet, or goes round a loop. On finitely many states, settling something for good makes two arrows meet. Chapters 1 and 2.
- **The toll isn't only a preference.** With finitely many states, settled staying settled, and Bennett's rule (a move where two arrows meet costs at least one), the toll follows. Take any one of the three away and a machine walks through. Chapter 3.
- **The smallest one.** Two boxes and one move that sends both to YES. Every machine with a move is what's left of a Thiele machine once you cover a coin. Chapter 4.
- **Looking isn't keeping.** A look can be free; it uses a blank page that can be handed back. Keeping what you saw is what pays. Chapter 6.
- **A window can't price what it hides.** A window with a clash can't price exactly, and the book finds the least it has to overcharge. Chapters 7 and 15.
- **A box over any machine.** A box that answers only to the machine and never comes down is a cup turned by one event. Chapter 14.
- **Four doors.** A machine that reads its box to skip work it already paid for pays in fresh editions, a box that comes down, room for every value checked, or wrong answers, and under two stated conditions there's no fifth. Chapter 16.
- **What a machine can't decide about itself.** No procedure inside the machine decides whether its own shortcuts are sound, under the conditions stated. Chapter 17.
- **Heat, given Landauer.** If Landauer's principle holds, a merge of states the machine could really have been in gives off at least a set amount of heat; on a state that's already known it sets no floor at all. The principle is an assumption with its critics named, never something the book proves. Chapter 20.
- **How much room keeping takes.** Exact counts of the states a machine needs to hold off a merge. Chapter 21.

The theses are labelled as theses, among them the pointer thesis (Chapter 19) and the Thiele thesis (Chapter 22).

## Publication and license

Devon Thiele, *The Thiele Machine: No Free Insight* (2026).
[Publication record](https://doi.org/10.5281/zenodo.17316437) · [Tagged releases](https://github.com/sethirus/The-Thiele-Machine/releases)

The publication is the book's PDF together with the matching tagged snapshot of this repository, in the same Zenodo version.

The software is licensed under [Apache 2.0](LICENSE). The book, the exact statements and `THIELE_MACHINE.txt` are licensed under CC-BY-SA-4.0.

Questions, objections and corrections: thethielemachine@gmail.com, or [open an issue](https://github.com/sethirus/The-Thiele-Machine/issues).
