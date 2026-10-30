"""Exhaustive checks of the counting claims in chapter eight of the book."""
from itertools import product
fails = []
# sheets: with m checks true at a value, 2^m reachable sheets, all needing distinct states
for m in range(0, 6):
    sheets = set()
    for run in product([0, 1], repeat=m):        # run or skip each true check
        sheets.add(tuple(run))
    if len(sheets) != 2 ** m: fails.append(('sheets', m))
# small piece: states F, TU, TC; CHECK sends TU->TC, TC->TC, F->F: a merge above the same value
CHECK = {'F': 'F', 'TU': 'TC', 'TC': 'TC'}
if len(set(CHECK.values())) == 3: fails.append('check merge')
# editions: the filing machine reaches 2^n distinct states above the same final list
def run(choices):
    page, marker, file = True, 'raw', ()
    for c in choices:
        if c and page: marker = 'checked'            # CHECK
        file = file + (marker == 'checked',)        # WRITE true: file the answer
        page, marker = True, 'raw'
    return (page, marker, file)
for n in range(0, 9):
    ends = {run(c) for c in product([0, 1], repeat=n)}
    if len(ends) != 2 ** n or len({(e[0], e[1]) for e in ends}) != 1: fails.append(('editions', n))
# the two computers: established record rises only after a passing check; counts 2 and 1
def machine(prog):
    rec, count, checked = False, 0, False
    for op in prog:
        if op == 'check': count += 1; checked = True
        elif op == 'raise':
            count += 1
            if checked: rec = True
    return rec, count
if machine(['sort', 'check', 'raise']) != (True, 2) or machine(['copy', 'raise']) != (False, 1):
    fails.append('two computers')
# bare toll: the copier can pay one and raise with no check
bare = lambda prog: (('raise' in prog), prog.count('raise'))
if bare(['copy', 'raise']) != (True, 1): fails.append('bare')
print('failures:', len(fails))
