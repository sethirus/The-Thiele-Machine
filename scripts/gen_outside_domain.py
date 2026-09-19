#!/usr/bin/env python3
"""Generate OutsideDomain.v: for every admitted constructor, the four
non-trap guards are false at the boundary's own fetched word.

The generated file proves, per opcode, that the fetched word's *trap-class*
guards are all false from the constructor's own premises, so an admitted
instruction is never an outside-domain trap. Morph-runtime faults are excluded
by the constructors that admit them.

Each lemma's statement is extracted verbatim from RetireMaster.v's own
`admitted` inductive, matching the mechanical pass used for
TableInvariantsPreserved.v.
"""
import re, sys

ROOT = '/workspaces/The-Thiele-Machine'
src = open(f'{ROOT}/coq/kami_hw/RetireMaster.v').read()

# Split the admitted inductive into constructor blocks.
body = src.split('Inductive admitted', 1)[1]
body = body.split('\n\nLemma', 1)[0]
blocks = re.split(r'\n\| (adm_\w+) :', body)
cons = []
for i in range(1, len(blocks), 2):
    cons.append((blocks[i], '| ' + blocks[i+1]))

print(f"{len(cons)} constructors")
for n, _ in cons:
    print(n)
