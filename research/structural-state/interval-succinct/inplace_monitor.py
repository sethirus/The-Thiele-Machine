"""Range-clear bit vector with its AVL index stored inside logical zero blocks.

Retained mutable algorithmic state is just `words` and `root`. Tree nodes use
the six words of the first block of a maximal run of logical zero blocks.
Node addresses encode their keys. No separate node pool or allocation map is
used. Two words per node hold temporary traversal frames, so the algorithms
are iterative and require only constant external workspace. Python object
overhead is not a claim about physical succinct storage.

Known ingredients: intrusive/free-block indexing and join-based AVL trees.
This implementation and its combination do not establish literature novelty.
"""


class InplaceIntervalMonitor:
    END, LEFT, RIGHT, HEIGHT, FRAME_NEXT, FRAME_DIRECTION = range(6)
    BLOCK_WORDS = 6

    def __init__(self, claims, intervals=(), word_bits=64):
        assert claims > 0 and word_bits >= max(2, claims.bit_length())
        self.n, self.w = claims, word_bits
        self.block_bits = self.BLOCK_WORDS * word_bits
        self.q = (claims + self.block_bits - 1) // self.block_bits
        self.intervals = tuple(intervals)
        assert all(0 <= lo <= hi <= claims for lo, hi in self.intervals)
        self.words = [0] * (self.BLOCK_WORDS * self.q)
        self.root = 1
        self.steps = 0  # instrumentation only, ignored by the algorithm
        self._new(1, self.q)

    def _get(self, node, field):
        assert 1 <= node <= self.q
        self.steps += 1
        return self.words[(node - 1) * self.BLOCK_WORDS + field]

    def _set(self, node, field, value):
        assert 1 <= node <= self.q and 0 <= value < (1 << self.w)
        self.steps += 1
        self.words[(node - 1) * self.BLOCK_WORDS + field] = value

    def _new(self, node, end):
        self._set(node, self.END, end)
        self._set(node, self.LEFT, 0)
        self._set(node, self.RIGHT, 0)
        self._set(node, self.HEIGHT, 1)
        self._set(node, self.FRAME_NEXT, 0)
        self._set(node, self.FRAME_DIRECTION, 0)

    def _height(self, node):
        return self._get(node, self.HEIGHT) if node else 0

    def _fix_height(self, node):
        self._set(node, self.HEIGHT,
                  1 + max(self._height(self._get(node, self.LEFT)),
                          self._height(self._get(node, self.RIGHT))))

    def _rotate_left(self, node):
        other = self._get(node, self.RIGHT)
        self._set(node, self.RIGHT, self._get(other, self.LEFT))
        self._set(other, self.LEFT, node)
        self._fix_height(node)
        self._fix_height(other)
        return other

    def _rotate_right(self, node):
        other = self._get(node, self.LEFT)
        self._set(node, self.LEFT, self._get(other, self.RIGHT))
        self._set(other, self.RIGHT, node)
        self._fix_height(node)
        self._fix_height(other)
        return other

    def _balance(self, node):
        self._fix_height(node)
        left, right = self._get(node, self.LEFT), self._get(node, self.RIGHT)
        difference = self._height(left) - self._height(right)
        assert abs(difference) <= 2
        if difference > 1:
            if self._height(self._get(left, self.LEFT)) < self._height(self._get(left, self.RIGHT)):
                self._set(node, self.LEFT, self._rotate_left(left))
            return self._rotate_right(node)
        if difference < -1:
            if self._height(self._get(right, self.RIGHT)) < self._height(self._get(right, self.LEFT)):
                self._set(node, self.RIGHT, self._rotate_right(right))
            return self._rotate_left(node)
        return node

    def _join3(self, left, pivot, right):
        """Join trees around a detached pivot, preserving physical node IDs."""
        stack = 0
        while abs(self._height(left) - self._height(right)) > 1:
            if self._height(left) > self._height(right):
                owner, direction = left, self.RIGHT
                left = self._get(owner, self.RIGHT)
            else:
                owner, direction = right, self.LEFT
                right = self._get(owner, self.LEFT)
            self._set(owner, self.FRAME_NEXT, stack)
            self._set(owner, self.FRAME_DIRECTION, direction)
            stack = owner
        self._set(pivot, self.LEFT, left)
        self._set(pivot, self.RIGHT, right)
        self._fix_height(pivot)
        result = pivot
        while stack:
            owner = stack
            stack = self._get(owner, self.FRAME_NEXT)
            direction = self._get(owner, self.FRAME_DIRECTION)
            self._set(owner, direction, result)
            result = self._balance(owner)
        return result

    def _split(self, node, key):
        """Return trees with start < key and start >= key, destructively."""
        stack = 0
        while node:
            direction = self.RIGHT if node - 1 < key else self.LEFT
            self._set(node, self.FRAME_NEXT, stack)
            self._set(node, self.FRAME_DIRECTION, direction)
            stack, node = node, self._get(node, direction)
        lower = higher = 0
        while stack:
            owner = stack
            stack = self._get(owner, self.FRAME_NEXT)
            direction = self._get(owner, self.FRAME_DIRECTION)
            # Nested joins visit processed descendants, never the unpopped
            # ancestor nodes whose temporary frames are still live.
            if direction == self.RIGHT:
                lower = self._join3(self._get(owner, self.LEFT), owner, lower)
            else:
                higher = self._join3(higher, owner, self._get(owner, self.RIGHT))
        return lower, higher

    def _pop_max(self, node):
        stack = 0
        while self._get(node, self.RIGHT):
            self._set(node, self.FRAME_NEXT, stack)
            stack, node = node, self._get(node, self.RIGHT)
        removed, result = node, self._get(node, self.LEFT)
        while stack:
            owner = stack
            stack = self._get(owner, self.FRAME_NEXT)
            self._set(owner, self.RIGHT, result)
            result = self._balance(owner)
        return result, removed

    def _join(self, left, right):
        if not left:
            return right
        if not right:
            return left
        left, pivot = self._pop_max(left)
        return self._join3(left, pivot, right)

    def _delete(self, node, key):
        lower, rest = self._split(node, key)
        removed, higher = self._split(rest, key + 1)
        assert removed == key + 1
        return self._join(lower, higher)

    def _insert(self, node, pivot):
        lower, higher = self._split(node, pivot - 1)
        return self._join3(lower, pivot, higher)

    def _predecessor(self, key):
        node, previous = self.root, 0
        while node:
            if node - 1 <= key:
                previous, node = node, self._get(node, self.RIGHT)
            else:
                node = self._get(node, self.LEFT)
        return previous

    def _max(self, node):
        if not node:
            return 0
        while True:
            right = self._get(node, self.RIGHT)
            if not right:
                return node
            node = right

    def _zero_run(self, block):
        node = self._predecessor(block)
        return node if node and block < self._get(node, self.END) else 0

    def _add_zero_interval(self, start, end):
        """Union one block interval into the indexed zero runs, without scan."""
        if start >= end:
            return
        previous = self._predecessor(start)
        if previous and self._get(previous, self.END) >= end:
            return
        lower, rest = self._split(self.root, start)
        previous = self._max(lower)
        if previous and self._get(previous, self.END) >= start:
            lower, removed = self._pop_max(lower)
            start = removed - 1
            end = max(end, self._get(removed, self.END))
        # Include a run starting at end: adjacent zero runs must coalesce.
        middle, higher = self._split(rest, end + 1)
        last = self._max(middle)
        if last:
            end = max(end, self._get(last, self.END))
        # All old nodes in `middle` are now logically dead. No traversal or
        # allocator is required: their storage lies inside the new zero run.
        pivot = start + 1
        self._new(pivot, end)
        self.root = self._join3(lower, pivot, higher)

    def passed(self, i):
        assert 0 <= i < self.n
        self.steps = 0
        block = i // self.block_bits
        run = self._zero_run(block)
        if run:
            start, end = run - 1, self._get(run, self.END)
            self.root = self._delete(self.root, start)
            if start < block:
                self._new(start + 1, block)
                self.root = self._insert(self.root, start + 1)
            if block + 1 < end:
                self._new(block + 2, end)
                self.root = self._insert(self.root, block + 2)
            # The old node, if it occupied this block, has been detached.
            for cell in range(block * self.BLOCK_WORDS, (block + 1) * self.BLOCK_WORDS):
                self.words[cell] = 0
                self.steps += 1
        self.words[i // self.w] |= 1 << (i % self.w)
        self.steps += 1

    def use(self, i):
        assert 0 <= i < self.n
        self.steps = 0
        if self._zero_run(i // self.block_bits):
            return False
        self.steps += 1
        return bool((self.words[i // self.w] >> (i % self.w)) & 1)

    def _clear_partial(self, block, lo, hi):
        if self._zero_run(block):
            return
        for cell in range(lo // self.w, (hi - 1) // self.w + 1):
            a = max(lo, cell * self.w) - cell * self.w
            b = min(hi, (cell + 1) * self.w) - cell * self.w
            self.words[cell] &= ~(((1 << (b - a)) - 1) << a)
            self.steps += 1
        first = block * self.BLOCK_WORDS
        self.steps += self.BLOCK_WORDS
        if not any(self.words[first:first + self.BLOCK_WORDS]):
            self._add_zero_interval(block, block + 1)

    def clear_range(self, lo, hi):
        assert 0 <= lo <= hi <= self.n
        self.steps = 0
        if lo == hi:
            return
        if lo == 0 and hi == self.n:
            self._new(1, self.q)
            self.root = 1
            return
        first, last = lo // self.block_bits, (hi - 1) // self.block_bits
        if first == last:
            if lo % self.block_bits == 0 and hi - lo == self.block_bits:
                self._add_zero_interval(first, first + 1)
            else:
                self._clear_partial(first, lo, hi)
            return
        full_start, full_end = first, last + 1
        if lo % self.block_bits:
            self._clear_partial(first, lo, (first + 1) * self.block_bits)
            full_start += 1
        if hi % self.block_bits:
            self._clear_partial(last, last * self.block_bits, hi)
            full_end -= 1
        self._add_zero_interval(full_start, full_end)

    def write(self, j):
        self.clear_range(*self.intervals[j])

    def snapshot(self):
        return self.root, self.words[:]

    def restore(self, snapshot):
        self.root, self.words = snapshot[0], snapshot[1][:]

    def check_representation(self, expected=None):
        """Expensive test helper. Its sets/lists are not algorithmic storage."""
        assert 0 <= self.root <= self.q
        assert len(self.words) == self.BLOCK_WORDS * self.q
        assert all(0 <= x < (1 << self.w) for x in self.words)
        seen, intervals = set(), []

        def visit(node, low, high):
            if not node:
                return 0
            assert node not in seen and low < node < high
            seen.add(node)
            start, end = node - 1, self._get(node, self.END)
            assert start < end <= self.q
            left = visit(self._get(node, self.LEFT), low, node)
            intervals.append((start, end))
            right = visit(self._get(node, self.RIGHT), node, high)
            assert abs(left - right) <= 1
            assert self._height(node) == max(left, right) + 1
            return max(left, right) + 1

        visit(self.root, 0, self.q + 1)
        assert all(a[1] < b[0] for a, b in zip(intervals, intervals[1:]))
        covered = {block for lo, hi in intervals for block in range(lo, hi)}
        for block in range(self.q):
            if block not in covered:
                first = self.BLOCK_WORDS * block
                assert any(self.words[first:first + self.BLOCK_WORDS])
        if expected is not None:
            assert all(self.use(i) == bool((expected >> i) & 1) for i in range(self.n))
            for block in range(self.q):
                realbits = (expected >> (block * self.block_bits)) & ((1 << self.block_bits) - 1)
                assert (block in covered) == (realbits == 0)
        # All reachable index nodes physically lie in logical-zero blocks.
        assert all(node - 1 in covered for node in seen)
        return len(seen)
