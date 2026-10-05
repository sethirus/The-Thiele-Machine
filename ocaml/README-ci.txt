The extracted OCaml runner
==========================

ocaml/RealizeExtract.v extracts the small machine, the
multi-register host (with and without PAY), the programs U and U_P with their
loaders, and the PSlot evaluation to OCaml. ocaml/realize_driver.ml is the
command-line driver around that code; it reads programs from standard input
and prints states, and it defines no machine behaviour.

Build and run by hand (project compiled, coqc 8.18, OCaml with zarith):

    scripts/realize_extract.sh build/realize
    echo "small 3 0 0 2  0 0 0 0  2 0 0 0" | build/realize/realize_driver

The tests that compare the extracted code with thiele_small/ are
tests/test_realize_ocaml.py. They skip, with a reason, when ocamlfind,
ocamlopt or zarith is missing.

CI. On Ubuntu the toolchain is `apt install ocaml libzarith-ocaml-dev`. The
tests run in the same job that builds the Coq tree and runs pytest with
--strict-backends, so that job's apt package list must include `ocaml` and
`libzarith-ocaml-dev` (otherwise those tests skip, and the strict run
reports skips). A separate job is also possible; see realize-status.md for
the YAML.
