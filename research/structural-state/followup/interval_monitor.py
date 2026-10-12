"""Packed freshness bits with lazy interval invalidation.

Policy intervals are half-open ranges of claim IDs in a supplied static order.
This is a standard blocked lazy segment tree, not a novelty claim. Python
allocation sizes do not establish the theoretical packed-space bound.
"""


class IntervalMonitor:
    def __init__(self, claims, intervals, word_bits=64):
        assert claims > 0 and word_bits > 0
        self.n = claims
        self.w = word_bits
        self.intervals = tuple(intervals)
        assert all(0 <= lo <= hi <= claims for lo, hi in self.intervals)
        self.q = (claims + word_bits - 1) // word_bits
        self.s = 1 << (self.q - 1).bit_length()
        self.height = self.s.bit_length() - 1
        self.words = [0] * self.q
        # One packed lazy-zero flag per node, including leaves.
        self.flags = [0] * ((2 * self.s + word_bits - 1) // word_bits)
        self._flag_set(1, True)
        self.visits = 0  # instrumentation, not used by the algorithm

    def _flag_get(self, node):
        return bool((self.flags[node // self.w] >> (node % self.w)) & 1)

    def _flag_set(self, node, value):
        cell, shift = divmod(node, self.w)
        if value:
            self.flags[cell] |= 1 << shift
        else:
            self.flags[cell] &= ~(1 << shift)

    def passed(self, i):
        assert 0 <= i < self.n
        self.visits = 0
        leaf = i // self.w
        node, left, right = 1, 0, self.s
        while right - left > 1:
            self.visits += 1
            if self._flag_get(node):
                self._flag_set(2 * node, True)
                self._flag_set(2 * node + 1, True)
                self._flag_set(node, False)
            middle = (left + right) // 2
            if leaf < middle:
                node, right = 2 * node, middle
            else:
                node, left = 2 * node + 1, middle
        self.visits += 1
        if self._flag_get(node):
            self.words[leaf] = 0
            self._flag_set(node, False)
        self.words[leaf] |= 1 << (i % self.w)

    def use(self, i):
        assert 0 <= i < self.n
        self.visits = 0
        node = self.s + i // self.w
        while node:
            self.visits += 1
            if self._flag_get(node):
                return False
            node //= 2
        return bool((self.words[i // self.w] >> (i % self.w)) & 1)

    def write(self, j):
        lo, hi = self.intervals[j]
        self.visits = 0
        if lo < hi:
            self._clear(1, 0, self.s * self.w, lo, hi)

    def _clear(self, node, left, right, lo, hi):
        self.visits += 1
        if hi <= left or right <= lo or self._flag_get(node):
            return
        if lo <= left and right <= hi:
            self._flag_set(node, True)
            return
        if right - left == self.w:
            low = max(lo, left) - left
            high = min(hi, right) - left
            mask = ((1 << (high - low)) - 1) << low
            self.words[left // self.w] &= ~mask
            return
        middle = (left + right) // 2
        self._clear(2 * node, left, middle, lo, hi)
        self._clear(2 * node + 1, middle, right, lo, hi)

    def snapshot(self):
        return self.words[:], self.flags[:]

    def restore(self, state):
        self.words, self.flags = state[0][:], state[1][:]

    def check_representation(self):
        assert len(self.words) == self.q
        assert all(0 <= x < (1 << self.w) for x in self.words + self.flags)
        if self.n % self.w:
            assert self.words[-1] >> (self.n % self.w) == 0


def multiphase_answers(dependencies, objects, written, monitor_class):
    """Phase I includes all PASS events; Phase II contains only WRITEs."""
    monitor = monitor_class(dependencies, objects)
    for i in range(len(dependencies)):
        monitor.passed(i)
    for j in written:
        monitor.write(j)
    return [monitor.use(i) for i in range(len(dependencies))]


class WideIntervalMonitor:
    """Word-wide lazy tree; leaf_words trades reset work for protected flags.

    Each internal node has fanout <= word_bits and one packed flags word.
    Leaf blocks contain leaf_words actual packed words. Querying never expands
    a lazy block; PASS expands at most one, and WRITE touches at most two
    partial boundary blocks. All other affected ranges get lazy flags.
    """

    def __init__(self, claims, intervals, word_bits=64, leaf_words=1):
        assert claims > 0 and word_bits >= 2 and leaf_words >= 1
        self.n, self.w, self.leaf_words = claims, word_bits, leaf_words
        self.intervals = tuple(intervals)
        assert all(0 <= lo <= hi <= claims for lo, hi in self.intervals)
        self.fanout = 1 << (word_bits.bit_length() - 1)
        self.block_bits = word_bits * leaf_words
        self.q = (claims + self.block_bits - 1) // self.block_bits
        self.words = [0] * ((claims + word_bits - 1) // word_bits)
        self.levels, self.spans = [], []
        children, span = self.q, self.block_bits
        while True:
            groups = (children + self.fanout - 1) // self.fanout
            self.levels.append([0] * groups)
            self.spans.append(span)
            if groups == 1:
                break
            children, span = groups, span * self.fanout
        self.height = len(self.levels)
        self.full = (1 << self.fanout) - 1
        self.levels[-1][0] = self.full
        self.visits = self.word_touches = 0  # instrumentation only

    def _zero_block(self, block):
        first = block * self.leaf_words
        last = min(first + self.leaf_words, len(self.words))
        for cell in range(first, last):
            self.words[cell] = 0
            self.word_touches += 1

    def passed(self, i):
        assert 0 <= i < self.n
        self.visits = self.word_touches = 0
        for level in range(self.height - 1, -1, -1):
            child_global = i // self.spans[level]
            group, child = divmod(child_global, self.fanout)
            self.visits += 1
            if (self.levels[level][group] >> child) & 1:
                if level == 0:
                    self._zero_block(child_global)
                else:
                    self.levels[level - 1][child_global] = self.full
                self.levels[level][group] &= ~(1 << child)
        self.words[i // self.w] |= 1 << (i % self.w)
        self.word_touches += 1

    def use(self, i):
        assert 0 <= i < self.n
        self.visits = self.word_touches = 0
        for level in range(self.height - 1, -1, -1):
            group, child = divmod(i // self.spans[level], self.fanout)
            self.visits += 1
            if (self.levels[level][group] >> child) & 1:
                return False
        self.word_touches += 1
        return bool((self.words[i // self.w] >> (i % self.w)) & 1)

    def write(self, j):
        self.visits = self.word_touches = 0
        lo, hi = self.intervals[j]
        if lo < hi:
            self._clear(self.height - 1, 0, 0, lo, hi)

    def _clear(self, level, group, start, lo, hi):
        self.visits += 1
        span = self.spans[level]
        full_start = (lo - start + span - 1) // span
        full_end = (hi - start) // span
        if full_start < full_end:
            mask = ((1 << (full_end - full_start)) - 1) << full_start
            self.levels[level][group] |= mask
        boundaries = []
        if (lo - start) % span:
            boundaries.append((lo - start) // span)
        if (hi - start) % span:
            right = (hi - start) // span
            if right not in boundaries:
                boundaries.append(right)
        for child in boundaries:
            if (self.levels[level][group] >> child) & 1:
                continue
            child_start = start + child * span
            low, high = max(lo, child_start), min(hi, child_start + span)
            if level:
                self._clear(level - 1, group * self.fanout + child, child_start, low, high)
            else:
                first, last = low // self.w, (high - 1) // self.w
                for cell in range(first, last + 1):
                    a = max(low, cell * self.w) - cell * self.w
                    b = min(high, (cell + 1) * self.w) - cell * self.w
                    self.words[cell] &= ~(((1 << (b - a)) - 1) << a)
                    self.word_touches += 1

    def snapshot(self):
        return self.words[:], [level[:] for level in self.levels]

    def restore(self, state):
        self.words = state[0][:]
        self.levels = [level[:] for level in state[1]]

    def check_representation(self):
        assert all(0 <= x < (1 << self.w) for x in self.words)
        assert all(0 <= x <= self.full for level in self.levels for x in level)
        if self.n % self.w:
            assert self.words[-1] >> (self.n % self.w) == 0
