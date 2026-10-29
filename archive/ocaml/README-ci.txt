The extracted OCaml runner
==========================

ocaml/RealizeExtract.v extracts the small machine, the multi-register host
(with and without PAY), the programs U and U_P with their loaders, the PSlot
evaluation and the register-storage compaction of RealizeCompact.v to OCaml.
ocaml/realize_driver.ml is the command-line driver around that code; it reads
programs from standard input and prints states, and it defines no machine
behaviour.

Build and run by hand (project compiled, coqc 8.18, OCaml with zarith):

    scripts/realize_extract.sh build/realize
    echo "small 3 0 0 2  0 0 0 0  2 0 0 0" | build/realize/realize_driver

The tests that compare the extracted code with thiele_small/ are
tests/test_realize_ocaml.py. A missing OCaml toolchain makes them fail, not
skip, whenever CI=true, under GitHub Actions and with --strict-backends, so a
lost install cannot turn into a pass. Without those they skip, with the reason.

Why the programs are written in chunks. U and U_P are lists of about 3700
instructions. Written as one literal, the extraction is straight-line code as
long as the list inside the one function that initialises the module, and
ocamlopt recurses over that length: with the 8 MB stack of Linux it stops with
"Fatal error: exception Stack overflow". scripts/realize_gen_programs.py
therefore writes each list as chunks of 64 instructions, each chunk a function
of unit, joined by append; the chunks are proved equal to the originals like
the whole list was (RealizePrograms.v).

CI. On Ubuntu the toolchain is `apt install ocaml libzarith-ocaml-dev`. The
python-tests job of ci.yml installs it and runs tests/test_realize_ocaml.py in
the same pytest run as everything else. The job realize-universal of ci-full.yml
runs U and U_P on guests with record instructions (program code at least 2^24,
hundreds of millions of host steps) with scripts/realize_universal_runs.py and
uploads the measured host steps and wall time of each run.

Windows development PC. ocamlfind from Coq Platform has no native compiler. The
opam switch under %LOCALAPPDATA%/opam/default (OCaml 5.3.0, zarith 1.14) is used
by the test when the ocamlfind on PATH is not enough. To reproduce the Linux
stack limit there, set OCAMLRUNPARAM=l=1000000 (an 8 MB OCaml stack) when
compiling.

The extracted verified compiler
===============================

ocaml/CmpExtract.v extracts the source interpreter, the shape check, the
compiler to the host program and the fast runner of CmpRun.v. ocaml/cmp_driver.ml
is the command-line driver: it reads a source program (s-expressions) and its
inputs from standard input and prints the answer, the variables and the step
counts. It defines no behaviour of the compiler. The guest and U_P stages are
covered by the theorem cmp_pipeline only: they are not extracted.

    scripts/cmp_extract.sh build/cmp

The tests are tests/test_cmp_compiler.py, with the helpers cmp_src.py (the
source language and an independent python interpreter and virtual machines),
cmp_corpus.py (programs and a random generator) and cmp_harness.py (building and
running the driver). They fail, they do not skip, when the OCaml or Coq
toolchain is missing under CI, GitHub Actions or --strict-backends. The python
job of ci.yml runs them with everything else; the job compiler-runs of
ci-full.yml runs the whole file, slow cases included, and keeps the measured
source operations, counter machine steps and host steps (scripts/cmp_report.py
summarises the report). The unary counters make the host cost grow with the
values, so the slowest cases take minutes.
