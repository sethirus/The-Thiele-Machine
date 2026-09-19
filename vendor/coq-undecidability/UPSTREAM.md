# Pinned upstream source

Repository: https://github.com/uds-psl/coq-library-undecidability
Commit: 8880e198bdc44cba1bd901f1fee701a95fc440ae (coq-8.18 branch)
License: Mozilla Public License 2.0, retained in LICENSE.

Theories are copied without source changes. The Thiele bridge is in
coq/kernel/foundation/VMUnboundedCM2Bridge.v, outside this upstream tree.
Build only the dependency closure needed for MinskyMachines/MM2_undec.vo.

The upstream predicate named `undecidable` has synthetic meaning:
decidability of the predicate implies co-enumerability of SBTM halting.
It is not itself the proposition `~ decidable p`. The bridge and status
must preserve that distinction rather than claiming a stronger result.
