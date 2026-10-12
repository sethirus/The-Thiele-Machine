"""Partition monitors for the explicit interfaces in Result.txt.

Python is an executable specification of word-array algorithms, not a claim
about Python object sizes. No external packages or proof assistant required.
"""
from dataclasses import dataclass


@dataclass
class Work:
    input_reads: int = 0
    parent_reads: int = 0
    arcs_built: int = 0
    arcs_scanned: int = 0


def copy_labels(values, n, work):
    if len(values) != n:
        raise ValueError('A partition must supply one label per item')
    result = []
    for i in range(n):
        value = values[i]
        work.input_reads += 1
        if not isinstance(value, int) or not 0 <= value < n:
            raise ValueError('Labels must be integers in [0,n)')
        result.append(value)
    return tuple(result)


def refines(p, q):
    """One representative q-label per p-block; O(n) words and time."""
    first = [-1] * len(p)
    for i, label in enumerate(p):
        if first[label] == -1:
            first[label] = q[i]
        elif first[label] != q[i]:
            return False
    return True


def join_linear(p, q, work=None):
    """Connected components of two spanning-star forests, in O(n) time."""
    if work is None:
        work = Work()
    n = len(p)
    head, target, following = [-1] * n, [], []
    def arc(u, v):
        target.append(v)
        following.append(head[u])
        head[u] = len(target) - 1
        work.arcs_built += 1
    for grouping in (p, q):
        first = [-1] * n
        for i, label in enumerate(grouping):
            if first[label] == -1:
                first[label] = i
            else:
                arc(i, first[label])
                arc(first[label], i)
    result = [-1] * n
    block = 0
    for start in range(n):
        if result[start] != -1:
            continue
        result[start] = block
        stack = [start]
        while stack:
            u = stack.pop()
            edge = head[u]
            while edge != -1:
                work.arcs_scanned += 1
                v = target[edge]
                if result[v] == -1:
                    result[v] = block
                    stack.append(v)
                edge = following[edge]
        block += 1
    return tuple(result)


class BulkMonitor:
    """Anchored entailment; complete partitions are the instruction arguments."""
    def __init__(self, key):
        self.n = len(key)
        if self.n < 1:
            raise ValueError('At least one item is required')
        self.work = Work()
        self.key = copy_labels(key, self.n, self.work)
        self.join = tuple(range(self.n))
        self.evidence = False
        self.channel = None
        self.record = None
        self.error = False
        self.ledger = 0

    def step(self, op, argument=None):
        if op not in ('SET', 'CHECK', 'COMMIT', 'CERTIFY'):
            raise ValueError('Unknown operation')
        self.work = Work()
        self.ledger += op != 'SET'
        if self.error:
            return
        if op == 'CERTIFY':
            if self.channel is None:
                self.error = True
            elif self.record is None:
                # Immutable, owned snapshots: pointer capture, not an n-item copy.
                self.record = (self.channel, self.key)
            return
        if op == 'COMMIT' and not self.evidence:
            self.error = True
            return
        p = copy_labels(argument, self.n, self.work)
        if op == 'SET':
            self.key = p
            self.join = tuple(range(self.n))
            self.evidence = False
            self.channel = None
        elif op == 'CHECK':
            if not refines(p, self.key):
                self.error = True
            else:
                self.join = join_linear(self.join, p, self.work)
                self.evidence = True
        else:
            if not refines(p, self.join):
                self.error = True
            else:
                self.channel = p


def pair_partition(n, pair):
    """Observation helper; its O(n) output cost is outside pair instruction cost."""
    labels = list(range(n))
    i, j = pair
    labels[j] = labels[i]
    return tuple(labels)


class PairMonitor:
    """Pair claims with exact or inferred permission; union by size, no compression."""
    def __init__(self, key, exact=False):
        self.n = len(key)
        if self.n < 1:
            raise ValueError('At least one item is required')
        self.exact = exact
        self.work = Work()
        self.key = copy_labels(key, self.n, self.work)
        # Enough bits for triangular indices and their intermediate products.
        self.word_bits = max(8, (2 * self.n * self.n + 1).bit_length())
        self.claim_count = self.n * (self.n - 1) // 2 + 1
        self._reset_evidence()
        self.channel = None
        self.record = None
        self.error = False
        self.ledger = 0

    def _reset_evidence(self):
        self.evidence = False
        if self.exact:
            self.words = [0] * ((self.claim_count + self.word_bits - 1) // self.word_bits)
        else:
            self.parent = list(range(self.n))
            self.size = [1] * self.n

    def _pair(self, argument):
        if len(argument) != 2:
            raise ValueError('A pair claim needs two item indices')
        i, j = argument
        self.work.input_reads += 2
        if not (isinstance(i, int) and isinstance(j, int)
                and 0 <= i < self.n and 0 <= j < self.n):
            raise ValueError('Pair indices must lie in [0,n)')
        return (i, j) if i <= j else (j, i)

    def _index(self, pair):
        i, j = pair
        if i == j:
            return self.claim_count - 1
        return i * (2 * self.n - i - 1) // 2 + j - i - 1

    def _find(self, i):
        while True:
            self.work.parent_reads += 1
            p = self.parent[i]
            if p == i:
                return i
            i = p

    def _union(self, i, j):
        i, j = self._find(i), self._find(j)
        if i == j:
            return
        if self.size[i] > self.size[j]:
            i, j = j, i
        self.parent[i] = j
        self.size[j] += self.size[i]

    def step(self, op, argument=None):
        if op not in ('SET', 'CHECK', 'COMMIT', 'CERTIFY'):
            raise ValueError('Unknown operation')
        self.work = Work()
        self.ledger += op != 'SET'
        if self.error:
            return
        if op == 'SET':
            self.key = copy_labels(argument, self.n, self.work)
            self._reset_evidence()
            self.channel = None
            return
        if op == 'CERTIFY':
            if self.channel is None:
                self.error = True
            elif self.record is None:
                self.record = (self.channel, self.key)
            return
        pair = self._pair(argument)
        i, j = pair
        if op == 'CHECK':
            if self.key[i] != self.key[j]:
                self.error = True
                return
            if self.exact:
                index = self._index(pair)
                self.words[index // self.word_bits] |= 1 << (index % self.word_bits)
            else:
                self._union(i, j)
            self.evidence = True
        else:
            if self.exact:
                index = self._index(pair)
                allowed = bool(self.words[index // self.word_bits] & (1 << (index % self.word_bits)))
            else:
                allowed = self.evidence and self._find(i) == self._find(j)
            if allowed:
                self.channel = pair
            else:
                self.error = True


class WordMemory:
    """Undo journal for the worst-case reduction; logs every overwritten word."""
    def __init__(self, words):
        self.words = list(words)
        self.journal = None
        self.last_undo_words = 0

    def read(self, address):
        return self.words[address]

    def write(self, address, value):
        if self.journal is not None:
            self.journal.append((address, self.words[address]))
        self.words[address] = value

    def begin(self):
        if self.journal is not None:
            raise RuntimeError('A transaction is already open')
        self.journal = []

    def rollback(self):
        if self.journal is None:
            raise RuntimeError('No open transaction')
        self.last_undo_words = len(self.journal)
        for address, value in reversed(self.journal):
            self.words[address] = value
        self.journal = None


class TransactionalPairMachine:
    """CHECK/COMMIT profile at the constant key; trap, ledger, channel all logged."""
    ERROR, LEDGER, EVIDENCE, CHANNEL_I, CHANNEL_J = range(5)

    def __init__(self, n):
        self.n = n
        self.memory = WordMemory([0, 0, 0, -1, -1] + list(range(n)) + [1] * n)

    def find(self, i):
        while True:
            p = self.memory.read(5 + i)
            if p == i:
                return i
            i = p

    def step(self, op, i, j):
        m = self.memory
        m.write(self.LEDGER, m.read(self.LEDGER) + 1)
        if m.read(self.ERROR):
            return
        a, b = self.find(i), self.find(j)
        if op == 'CHECK':
            if a != b:
                if m.read(5 + self.n + a) > m.read(5 + self.n + b):
                    a, b = b, a
                m.write(5 + a, b)
                m.write(5 + self.n + b, m.read(5 + self.n + a) + m.read(5 + self.n + b))
            m.write(self.EVIDENCE, 1)
        elif op == 'COMMIT':
            if m.read(self.EVIDENCE) and a == b:
                m.write(self.CHANNEL_I, i)
                m.write(self.CHANNEL_J, j)
            else:
                m.write(self.ERROR, 1)
        else:
            raise ValueError('This profile supports CHECK and COMMIT')


class ConnectivityViaMonitor:
    """Trusted algorithmic simulator, not a caller API for undoing real traps."""
    def __init__(self, n):
        self.machine = TransactionalPairMachine(n)
        self.machine.step('CHECK', 0, 0)  # Establish the always-valid bottom claim.

    def insert(self, i, j):
        self.machine.step('CHECK', i, j)

    def connected(self, i, j):
        memory = self.machine.memory
        memory.begin()
        try:
            self.machine.step('COMMIT', i, j)
            result = not memory.read(TransactionalPairMachine.ERROR)
        finally:
            memory.rollback()
        return result
