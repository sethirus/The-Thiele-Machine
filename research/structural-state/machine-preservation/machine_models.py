"""Two explicit models of the Small Machine for differential checking.

Reference: minimal/EarnedCore.v, repository commit
e4c234627651f1b12eb649148a051d5a252ed6b4. The reduced model preserves the
declared operational interface, not numeric version readout. No repository
implementation or manuscript is modified by this experiment.
"""
from dataclasses import dataclass, replace


def evaluate(prop, value):
    kind, parameter = prop
    if kind == 'zero':
        return value == 0
    if kind == 'even':
        return value % 2 == 0
    assert kind == 'ge'
    return value >= parameter


def price(instruction):
    return int(instruction[0] in ('check', 'commit', 'certify'))


@dataclass(frozen=True)
class Reference:
    values: tuple = (0, 0)
    versions: tuple = (0, 0)
    pc: int = 1
    facts: tuple = ()  # newest first: (property, counter, version)
    channel: object = None
    error: bool = False
    ledger: int = 0
    certified: bool = False


def reference_step(s, instruction):
    kind = instruction[0]
    result = replace(s, ledger=s.ledger + price(instruction))
    if s.error:
        return result
    if kind in ('inc', 'dec'):
        c = instruction[1]
        if kind == 'dec' and s.values[c] == 0:
            return replace(result, pc=s.pc + 1)
        values, versions = list(s.values), list(s.versions)
        values[c] += 1 if kind == 'inc' else -1
        versions[c] += 1
        return replace(result, values=tuple(values), versions=tuple(versions),
                       pc=s.pc + 1 if kind == 'inc' else instruction[2])
    if kind == 'halt':
        return result
    if kind == 'check':
        _, prop, c = instruction
        if evaluate(prop, s.values[c]) and len(s.facts) < 16:
            return replace(result, facts=((prop, c, s.versions[c]),) + s.facts,
                           pc=s.pc + 1)
        return replace(result, error=True)
    if kind == 'commit':
        _, prop, c = instruction
        fact = (prop, c, s.versions[c])
        if fact in s.facts:
            return replace(result, channel=fact, pc=s.pc + 1)
        return replace(result, error=True)
    assert kind == 'certify'
    if s.channel is not None:
        return replace(result, certified=True, pc=s.pc + 1)
    return replace(result, error=True)


@dataclass(frozen=True)
class Reduced:
    values: tuple = (0, 0)
    pc: int = 1
    facts: tuple = ()  # newest first: (property, counter), duplicates retained
    live: tuple = (0, 0)  # live prefix length of each counter's subsequence
    channel: object = None  # property and counter of last earned commitment
    error: bool = False
    ledger: int = 0
    certified: bool = False


def abstract(s):
    live = []
    for c in (0, 1):
        versions = [v for _, counter, v in s.facts if counter == c]
        assert all(v <= s.versions[c] for v in versions)
        flags = [v == s.versions[c] for v in versions]
        assert flags == sorted(flags, reverse=True), 'not a fresh prefix'
        live.append(sum(flags))
    return Reduced(s.values, s.pc, tuple((p, c) for p, c, _ in s.facts),
                   tuple(live), None if s.channel is None else s.channel[:2],
                   s.error, s.ledger, s.certified)


def reduced_step(s, instruction):
    kind = instruction[0]
    result = replace(s, ledger=s.ledger + price(instruction))
    if s.error:
        return result
    if kind == 'halt':
        return result
    if kind == 'inc' or kind == 'dec':
        c = instruction[1]
        if kind == 'dec' and not s.values[c]:
            return replace(result, pc=s.pc + 1)
        values, live = list(s.values), list(s.live)
        values[c] += 1 if kind == 'inc' else -1
        live[c] = 0
        return replace(result, values=tuple(values), live=tuple(live),
                       pc=instruction[2] if kind == 'dec' else s.pc + 1)
    if kind == 'check':
        _, prop, c = instruction
        if len(s.facts) == 16 or not evaluate(prop, s.values[c]):
            return replace(result, error=True)
        live = list(s.live)
        live[c] += 1
        return replace(result, facts=((prop, c),) + s.facts,
                       live=tuple(live), pc=s.pc + 1)
    if kind == 'commit':
        _, prop, c = instruction
        remaining, found = s.live[c], False
        for saved_prop, saved_c in s.facts:
            if saved_c == c and remaining:
                found |= saved_prop == prop
                remaining -= 1
        if not found:
            return replace(result, error=True)
        return replace(result, channel=(prop, c), pc=s.pc + 1)
    assert kind == 'certify'
    if s.channel is None:
        return replace(result, error=True)
    return replace(result, certified=True, pc=s.pc + 1)


def run(state, instructions, step):
    for instruction in instructions:
        state = step(state, instruction)
    return state


def program_step(state, program, step):
    if state.error or not 1 <= state.pc <= len(program):
        return state
    instruction = program[state.pc - 1]
    return state if instruction[0] == 'halt' else step(state, instruction)


def boundary_family(a=8, b=8):
    """All (a+1)(b+1) permission states, with identical base window/ledger.

    Each counter is written exactly twice, at a selectable cut in its checks.
    Thus even the reference version numbers at the end agree across histories.
    """
    assert a >= 0 and b >= 0 and a + b <= 16
    initial = Reference(values=(max(1, a), max(1, b)))
    family = {}
    for ra in range(a + 1):
        for rb in range(b + 1):
            trace = []
            for c, count, live in ((0, a, ra), (1, b, rb)):
                for position in range(count + 1):
                    if position == count - live:
                        trace.append(('inc', c))
                        trace.append(('dec', c, len(trace) + 2))
                    if position < count:
                        trace.append(('check', ('ge', position + 1), c))
            state = run(initial, trace, reference_step)
            assert abstract(state).live == (ra, rb)
            family[ra, rb] = state, tuple(trace)
    return initial, family


def reset_cycle(pc):
    # Both counters return to their values; both editions change; pc returns.
    return (('inc', 0), ('dec', 0, pc), ('inc', 1), ('dec', 1, pc))


@dataclass(frozen=True)
class EditionReduced:
    values: tuple = (0, 0)
    editions: tuple = (0, 0)
    pc: int = 1
    facts: tuple = ()
    channel: object = None
    error: bool = False
    ledger: int = 0
    certified: bool = False


def edition_abstract(s):
    ranks = []
    for c in (0, 1):
        stamps = sorted({v for _, counter, v in s.facts if counter == c} |
                        {s.versions[c]})
        assert stamps[-1] == s.versions[c]
        ranks.append({v: rank for rank, v in enumerate(stamps)})
    facts = tuple((p, c, ranks[c][v]) for p, c, v in s.facts)
    channel = None
    if s.channel is not None:
        p, c, v = s.channel
        assert s.channel in s.facts
        channel = p, c, ranks[c][v]
    return EditionReduced(s.values, tuple(ranks[c][s.versions[c]] for c in (0, 1)),
                          s.pc, facts, channel, s.error, s.ledger, s.certified)


def edition_step(s, instruction):
    kind = instruction[0]
    result = replace(s, ledger=s.ledger + price(instruction))
    if s.error or kind == 'halt':
        return result
    if kind in ('inc', 'dec'):
        c = instruction[1]
        if kind == 'dec' and s.values[c] == 0:
            return replace(result, pc=s.pc + 1)
        values, editions = list(s.values), list(s.editions)
        values[c] += 1 if kind == 'inc' else -1
        if any(counter == c and rank == editions[c] for _, counter, rank in s.facts):
            editions[c] += 1
        return replace(result, values=tuple(values), editions=tuple(editions),
                       pc=s.pc + 1 if kind == 'inc' else instruction[2])
    if kind == 'check':
        _, p, c = instruction
        if not evaluate(p, s.values[c]) or len(s.facts) >= 16:
            return replace(result, error=True)
        return replace(result, facts=((p, c, s.editions[c]),) + s.facts, pc=s.pc + 1)
    if kind == 'commit':
        _, p, c = instruction
        fact = (p, c, s.editions[c])
        if fact not in s.facts:
            return replace(result, error=True)
        return replace(result, channel=fact, pc=s.pc + 1)
    assert kind == 'certify'
    if s.channel is None:
        return replace(result, error=True)
    return replace(result, certified=True, pc=s.pc + 1)


def gap_history(a_pattern, b_pattern):
    """Arbitrary 8+8 edition-gap bits, fixed total writes and final base."""
    assert 0 <= a_pattern < 256 and 0 <= b_pattern < 256
    trace = []
    for c, pattern in enumerate((a_pattern, b_pattern)):
        def pair():
            trace.append(('inc', c))
            trace.append(('dec', c, len(trace) + 2))
        for _ in range(8 - pattern.bit_count()):
            pair()  # unused writes occur before any fact concerning c
        for i in range(8):
            trace.append(('check', ('ge', i + 1), c))
            if pattern & (1 << i):
                pair()
    return tuple(trace)


def edition_gaps(s):
    encoded = []
    for c in (0, 1):
        ranks = [v for _, counter, v in reversed(s.facts) if counter == c]
        following = ranks[1:] + [s.editions[c]]
        encoded.append(sum(int(a != b) << i for i, (a, b) in
                           enumerate(zip(ranks, following))))
    return tuple(encoded)
