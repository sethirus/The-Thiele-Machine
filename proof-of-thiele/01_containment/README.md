# Pillar 1 – Containment of Turing computation

The kernel proof `coq/kernel/Subsumption.v` shows that a Thiele Machine whose
instruction set is restricted to the blind subset simulates every Turing
machine (`thiele_simulates_turing`) and that sighted instructions produce runs
that classical traces cannot reach (`turing_is_strictly_contained`). The script
`coq/verify_subsumption.sh` rebuilds this theorem from scratch using Coq's
trusted kernel.

To replay the containment argument, run:

```bash
make -C proof-of-thiele containment
```

This command clears the Coq build artefacts, regenerates the kernel model, and
replays the subsumption proof. Any missing dependency or failed axiom discharge
halts the build. The admitted lemmas are catalogued in `coq/ADMIT_REPORT.txt`
so auditors can review the precise trust surface.
