"""Executable research models, not replacements for the book's machine.

PASS is emitted by a trusted successful validator, never by an untrusted caller.
WRITE is a completely mediated edition-changing write. USE asks whether a PASS
occurred after every dependent WRITE. Costs below count metadata operations,
not the work needed to validate the underlying predicate.
Python object sizes and big-integer operations are not word-RAM cost measures.
"""


class Eager:
    def __init__(self, dependencies, objects):
        self.dependencies = tuple(map(frozenset, dependencies))
        self.columns = [0] * objects
        for i, deps in enumerate(self.dependencies):
            for j in deps:
                self.columns[j] |= 1 << i
        self.bits = 0

    def passed(self, i):
        self.bits |= 1 << i

    def write(self, j):
        self.bits &= ~self.columns[j]

    def use(self, i):
        return bool(self.bits & (1 << i))


class BoundedLazy:
    """Finite timestamps, preserving order through in-place rank compaction.

    N = claim count + object count. Exactly N last-event tokens are possible.
    Nonzero timestamps are distinct and in 1..2N. The slots array maps a live
    timestamp to its token; all other slots are empty. Compaction costs O(N),
    happens only after at least N updates since the previous compaction, and
    preserves every comparison between surviving last-event timestamps.
    """

    def __init__(self, dependencies, objects):
        self.dependencies = tuple(map(frozenset, dependencies))
        self.n = len(dependencies)
        self.size = self.n + objects
        assert self.size > 0
        self.limit = 2 * self.size
        self.stamps = [0] * self.size
        self.slots = [None] * (self.limit + 1)
        self.clock = 0
        # Instrumentation below is not used by the algorithm or its answers.
        self.compactions = 0
        self.compaction_cells = 0
        self.updates = 0

    def _compact(self):
        rank = 0
        for old in range(1, self.limit + 1):
            owner = self.slots[old]
            if owner is not None:
                rank += 1
                self.stamps[owner] = rank
                self.slots[old] = None
                self.slots[rank] = owner
        self.clock = rank
        self.compactions += 1
        self.compaction_cells += self.limit

    def _touch(self, owner):
        if self.clock == self.limit:
            self._compact()
        old = self.stamps[owner]
        if old:
            self.slots[old] = None
        self.clock += 1
        self.stamps[owner] = self.clock
        self.slots[self.clock] = owner
        self.updates += 1

    def passed(self, i):
        self._touch(i)

    def write(self, j):
        self._touch(self.n + j)

    def use(self, i):
        checked = self.stamps[i]
        return checked != 0 and all(
            self.stamps[self.n + j] <= checked for j in self.dependencies[i]
        )

    def check_representation(self):
        nonzero = [x for x in self.stamps if x]
        assert len(nonzero) == len(set(nonzero))
        assert all(0 <= x <= self.clock <= self.limit for x in self.stamps)
        for owner, t in enumerate(self.stamps):
            if t:
                assert self.slots[t] == owner
        for t, owner in enumerate(self.slots):
            if owner is not None:
                assert t > 0 and self.stamps[owner] == t
        assert self.compaction_cells <= 2 * self.updates


class GlobalSparseSet:
    """Simple O(n log n)-bit implementation of constant-time global reset.

    This is not Hagerup's optimal n+1-bit choice dictionary. It supplies an
    elementary executable construction with constant word-operation bounds.
    """

    def __init__(self, n):
        self.dense = [0] * n
        self.sparse = [0] * n
        self.count = 0

    def use(self, i):
        p = self.sparse[i]
        return p < self.count and self.dense[p] == i

    def passed(self, i):
        if not self.use(i):
            self.dense[self.count] = i
            self.sparse[i] = self.count
            self.count += 1

    def reset(self):
        self.count = 0


def history_answer(history, dependencies, i):
    """Independent specification: scan actual events backwards."""
    for kind, x in reversed(history):
        if kind == 'pass' and x == i:
            return True
        if kind == 'write' and x in dependencies[i]:
            return False
    return False


def omv_round(monitor, vector):
    """Reduction, with no primitive bulk refresh: one PASS per claim."""
    for i in range(len(monitor.dependencies)):
        monitor.passed(i)
    for j, bit in enumerate(vector):
        if bit:
            monitor.write(j)
    return [not monitor.use(i) for i in range(len(monitor.dependencies))]
