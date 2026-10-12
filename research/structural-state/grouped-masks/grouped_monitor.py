"""EXPERIMENTAL, UNVERIFIED PROTOTYPE. Development paused for scope review.

Packed lazy group invalidation with Hagerup's constant-time bit-vector backend.

The payload, one backend flag per group, and one active bit per group occupy
n+2g bits in a single packed array, rounded once to machine words. Immutable
layout/claim mappings and policy masks are separate. Instrumentation is not
algorithmic state. Python integers model O(1)-word quantities, not physical
Python allocation. For g <= w every public operation is worst-case O(1).

Backend attribution: Torben Hagerup, An Optimal Choice Dictionary (2017),
Sections 3 and 4.1, b=2w. Only insertion/read/reset are needed here. This is
an adaptation of that known algorithm, not a new choice-dictionary result.
"""


class GroupedMonitor:
    def __init__(self, sizes, word_bits=64, masks=()):
        self.sizes = tuple(sizes)  # immutable configuration below
        assert self.sizes and all(s > 0 for s in self.sizes)
        self.n, self.g, self.w = sum(self.sizes), len(self.sizes), word_bits
        assert self.g <= self.w and self.w >= max(4, self.n.bit_length())
        self.mask = (1 << self.w) - 1
        self.masks = tuple(masks)
        assert all(0 <= x < (1 << self.g) for x in self.masks)
        starts, locations, base = [], [], 0
        for group, size in enumerate(self.sizes):
            starts.append(base)
            locations.extend((group, i) for i in range(size))
            base += size
        self.starts, self.locations = tuple(starts), tuple(locations)
        # Only this array is mutable algorithmic persistent state.
        self.words = [0] * ((self.n + 2 * self.g + self.w - 1) // self.w)
        self.accesses = 0  # test instrumentation only
        self._put(self.n + self.g, self.g, 0)

    def _get(self, offset, width):
        """Read <=4w bits, possibly unaligned, with <=5 physical reads."""
        assert 0 <= width <= 4 * self.w
        result = shift = 0
        while width:
            cell, bit = divmod(offset, self.w)
            take = min(width, self.w - bit)
            result |= ((self.words[cell] >> bit) & ((1 << take) - 1)) << shift
            self.accesses += 1
            offset, width, shift = offset + take, width - take, shift + take
        return result

    def _put(self, offset, width, value):
        """Modify <=4w bits, preserving all neighboring packed groups/flags."""
        assert 0 <= width <= 4 * self.w and 0 <= value < (1 << width)
        while width:
            cell, bit = divmod(offset, self.w)
            take = min(width, self.w - bit)
            mask = (1 << take) - 1
            self.words[cell] = ((self.words[cell] & ~(mask << bit)) |
                                ((value & mask) << bit))
            self.accesses += 2  # physical read and write
            offset, width, value = offset + take, width - take, value >> take

    def _base(self, group, i):
        return self.starts[group] + (i - 1) * 4 * self.w

    def _count(self, group):
        return self.sizes[group] // (4 * self.w)

    def _barrier(self, group):
        if self._get(self.n + group, 1):
            return 0
        return self._get(self.starts[group] + 3 * self.w, self.w)

    def _save_barrier(self, group, k):
        self._put(self.n + group, 1, int(k == 0))
        if k:
            # Cell 1 is left of the barrier: these bits cannot be payload.
            self._put(self.starts[group] + 3 * self.w, self.w, k)

    def _pointer(self, group, i, k):
        # Only cell 1, when left of the barrier, contains embedded k.
        # Other upper halves must be read in full to reject spurious matches.
        width = self.w if i == 1 and k else 2 * self.w
        return self._get(self._base(group, i) + 2 * self.w, width)

    def _set_pointer(self, group, i, value):
        self._put(self._base(group, i) + 2 * self.w, 2 * self.w, value)

    def _mate(self, group, i, k):
        other = self._pointer(group, i, k)
        if (1 <= other <= self._count(group) and
                ((i <= k < other) or (other <= k < i)) and
                self._pointer(group, other, k) == i):
            return other
        return i

    def _read(self, group, i, k):
        other = self._mate(group, i, k)
        if other <= k:
            return 0
        if i > k:
            return self._get(self._base(group, i), 4 * self.w)
        low = self._get(self._base(group, i), 2 * self.w)
        high = self._get(self._base(group, other), 2 * self.w)
        return low | (high << (2 * self.w))

    def _simple_write(self, group, i, value, k):
        if i <= k:
            other = self._mate(group, i, k)
            half_mask = (1 << (2 * self.w)) - 1
            self._put(self._base(group, i), 2 * self.w, value & half_mask)
            self._put(self._base(group, other), 2 * self.w, value >> (2 * self.w))
        else:
            self._put(self._base(group, i), 4 * self.w, value)
            other = self._mate(group, i, k)
            if other != i:
                self._set_pointer(group, other, other)

    def _set_chunk_bit(self, group, i, bit):
        k = self._barrier(group)
        old = self._read(group, i, k)
        value = old | (1 << bit)
        if not old:
            assert k > 0
            old_mate = self._mate(group, i, k)
            crossing_mate = self._mate(group, k, k)
            crossing_value = self._read(group, k, k)
            k -= 1
            self._simple_write(group, k + 1, crossing_value, k)
            if i != crossing_mate:
                self._set_pointer(group, old_mate, crossing_mate)
                self._set_pointer(group, crossing_mate, old_mate)
                self._put(self._base(group, crossing_mate), 2 * self.w,
                          self._get(self._base(group, i), 2 * self.w))
        self._simple_write(group, i, value, k)
        self._save_barrier(group, k)

    def _activate(self, group):
        chunks = self._count(group)
        if chunks:
            self._save_barrier(group, chunks)
        tail = self.sizes[group] - chunks * 4 * self.w
        if tail:
            self._put(self.starts[group] + chunks * 4 * self.w, tail, 0)
        self._put(self.n + self.g + group, 1, 1)

    def passed(self, claim):
        assert 0 <= claim < self.n
        self.accesses = 0
        group, local = self.locations[claim]
        if not self._get(self.n + self.g + group, 1):
            self._activate(group)
        chunks = self._count(group)
        if local < chunks * 4 * self.w:
            i, bit = divmod(local, 4 * self.w)
            self._set_chunk_bit(group, i + 1, bit)
        else:
            self._put(self.starts[group] + local, 1, 1)

    def use(self, claim):
        assert 0 <= claim < self.n
        self.accesses = 0
        group, local = self.locations[claim]
        if not self._get(self.n + self.g + group, 1):
            return False
        if local >= self._count(group) * 4 * self.w:
            return bool(self._get(self.starts[group] + local, 1))
        i, bit = divmod(local, 4 * self.w)
        return bool((self._read(group, i + 1, self._barrier(group)) >> bit) & 1)

    def invalidate_mask(self, mask):
        assert 0 <= mask < (1 << self.g)
        self.accesses = 0
        active = self._get(self.n + self.g, self.g)
        self._put(self.n + self.g, self.g, active & ~mask)

    def write(self, object_id):
        self.invalidate_mask(self.masks[object_id])

    def snapshot(self):
        return self.words[:]

    def restore(self, snapshot):
        self.words[:] = snapshot

    def check_representation(self, expected):
        """Test-only oracle: its allocations are not algorithmic workspace."""
        assert len(self.words) * self.w < self.n + 2 * self.g + self.w
        assert all(0 <= x <= self.mask for x in self.words)
        for claim in range(self.n):
            assert self.use(claim) == bool((expected >> claim) & 1), claim
        for group in range(self.g):
            if not self._get(self.n + self.g + group, 1):
                continue
            count = self._count(group)
            if not count:
                continue
            k = self._barrier(group)
            assert 0 <= k <= count
            values = [self._read(group, i, k) for i in range(1, count + 1)]
            assert sum(x == 0 for x in values) == k
            for i, value in enumerate(values):
                logical = (expected >> (self.starts[group] + i * 4 * self.w))
                logical &= (1 << (4 * self.w)) - 1
                assert logical == value
