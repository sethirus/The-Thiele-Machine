# Pinned upstream source

Repository: https://github.com/uds-psl/coq-library-undecidability
Commit: 8880e198bdc44cba1bd901f1fee701a95fc440ae (coq-8.18 branch)
License: Mozilla Public License 2.0, retained in LICENSE.

Theories are copied without source changes. The Thiele files that use them
live in coq/kernel/foundation/ (MM2ComplementUndec.v and the universal-host
files), outside this upstream tree. Build only the dependency closure those
files need.

The upstream predicate named `undecidable` has synthetic meaning:
decidability of the predicate implies co-enumerability of SBTM halting.
It is not itself the proposition `~ decidable p`. The bridge and status
must preserve that distinction rather than claiming a stronger result.

## Modules built for the Thiele files

The Thiele files import these library modules, all copied without source
changes and listed in `UNDEC_MODULES` of `coq/Makefile.local`:

- `MinskyMachines/MMenv/env.v`, `mme_defs.v` and `mme_utils.v`, the Minsky
  machine with an environment of registers;
- `MuRec/MuRec.v`, `MuRec/Util/recalg.v` and `MuRec/Util/ra_mm_env.v`, the
  mu-recursive algorithms and their compilation to Minsky machines;
- `MinskyMachines/MMA/mma_utils.v`, `FRACTRAN/Util/prime_seq.v`,
  `Shared/Libs/DLW/Code/compiler.v` and `Shared/Libs/DLW/Utils/{utils,gcd,prime}.v`.

Their build dependencies come with them through the library's own makefile.

The lifting theorem files (LiftModelsAll.v, LiftHeadline.v) also need the
equivalence of the classical models, so `Synthetic/Models_Equivalent.v`,
`H10/H10.v`, `TM/TM.v` and `MuRec/Util/ra_sem_eq.v` are listed too; the library's
own makefile builds the rest of their closure (the Diophantine, Turing machine
and reduction modules), all copied without source changes.
