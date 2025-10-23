"""Refinement scaffolding tests linking the concrete VM to the abstract CHSH sandbox."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, Tuple

import pytest

from thielecpu.state import State
from thielecpu._types import ModuleId


Predicate = Callable[[int], bool]


@dataclass(frozen=True)
class AbstractModule:
    """Canonical representation of a partition module for refinement checks."""

    region: FrozenSet[int]
    axioms: Tuple[str, ...]


@dataclass(frozen=True)
class AbstractSystemState:
    """Minimal abstract state mirroring the Coq sandbox structure."""

    next_id: int
    modules: Dict[int, AbstractModule]


def map_vm_to_abstract(state: State) -> AbstractSystemState:
    """Project the concrete VM state into the abstract refinement model."""

    modules: Dict[int, AbstractModule] = {}
    for mid, region in state.regions.modules.items():
        axioms = tuple(state.axioms.get(ModuleId(mid), []))
        modules[mid] = AbstractModule(region=frozenset(region), axioms=axioms)
    return AbstractSystemState(next_id=state._next_id, modules=modules)


def abstract_psplit(
    state: AbstractSystemState, module_id: int, predicate: Predicate
) -> AbstractSystemState:
    """Mirror ``State.psplit`` on the abstract representation."""

    modules = dict(state.modules)
    target = modules.get(module_id)
    if target is None:
        raise KeyError(f"module {module_id} not present in abstract state")

    part_even = frozenset(x for x in target.region if predicate(x))
    part_odd = frozenset(x for x in target.region if not predicate(x))
    next_id = state.next_id

    if not part_even or not part_odd:
        modules[module_id] = AbstractModule(target.region, target.axioms)
        modules[next_id] = AbstractModule(frozenset(), tuple())
        return AbstractSystemState(next_id=next_id + 1, modules=modules)

    del modules[module_id]
    modules[next_id] = AbstractModule(part_even, target.axioms)
    next_id += 1
    modules[next_id] = AbstractModule(part_odd, target.axioms)
    next_id += 1

    return AbstractSystemState(next_id=next_id, modules=modules)


def abstract_pmerge(
    state: AbstractSystemState, module_left: int, module_right: int
) -> AbstractSystemState:
    """Mirror ``State.pmerge`` on the abstract representation."""

    if module_left == module_right:
        raise ValueError("cannot merge module with itself")

    modules = dict(state.modules)
    left = modules.pop(module_left, None)
    right = modules.pop(module_right, None)
    if left is None or right is None:
        raise KeyError("module missing from abstract state")

    if left.region & right.region:
        raise ValueError("modules overlap; cannot merge")

    union = left.region | right.region
    combined_axioms = left.axioms + right.axioms

    for mid, module in list(modules.items()):
        if module.region == union:
            modules[mid] = AbstractModule(
                region=module.region,
                axioms=module.axioms + combined_axioms,
            )
            return AbstractSystemState(next_id=state.next_id, modules=modules)

    modules[state.next_id] = AbstractModule(union, combined_axioms)
    return AbstractSystemState(next_id=state.next_id + 1, modules=modules)


def abstract_lassert(
    state: AbstractSystemState, module_id: int, axiom: str
) -> AbstractSystemState:
    """Mirror ``State.add_axiom`` on the abstract representation."""

    modules = dict(state.modules)
    target = modules.get(module_id)
    if target is None:
        raise KeyError(f"module {module_id} not present in abstract state")

    modules[module_id] = AbstractModule(
        region=target.region,
        axioms=target.axioms + (axiom,),
    )
    return AbstractSystemState(next_id=state.next_id, modules=modules)


def _fresh_state() -> Tuple[State, ModuleId]:
    state = State()
    module = state.pnew({0, 1, 2, 3})
    state.add_axiom(module, "initial axiom")
    return state, module


def test_map_vm_to_abstract_round_trip_basic():
    state, module = _fresh_state()
    abstract = map_vm_to_abstract(state)
    assert module in abstract.modules
    assert abstract.modules[module].region == frozenset({0, 1, 2, 3})
    assert abstract.modules[module].axioms == ("initial axiom",)


def test_psplit_homomorphism():
    real_state, module_real = _fresh_state()
    abstract_state, module_abstract = _fresh_state()

    predicate: Predicate = lambda x: x % 2 == 0

    real_state.psplit(module_real, predicate)
    real_projection = map_vm_to_abstract(real_state)

    abstract_projection_before = map_vm_to_abstract(abstract_state)
    abstract_projection_after = abstract_psplit(
        abstract_projection_before, module_abstract, predicate
    )

    assert real_projection == abstract_projection_after


def test_psplit_degenerate_matches_vm_behavior():
    real_state, module_real = _fresh_state()
    abstract_state, module_abstract = _fresh_state()

    predicate: Predicate = lambda _x: True

    real_state.psplit(module_real, predicate)
    real_projection = map_vm_to_abstract(real_state)

    abstract_projection_before = map_vm_to_abstract(abstract_state)
    abstract_projection_after = abstract_psplit(
        abstract_projection_before, module_abstract, predicate
    )

    assert real_projection == abstract_projection_after


def _two_module_state() -> Tuple[State, ModuleId, ModuleId]:
    state = State()
    left = state.pnew({0, 1})
    state.add_axiom(left, "left axiom")
    right = state.pnew({2, 3})
    state.add_axiom(right, "right axiom")
    return state, left, right


def test_pmerge_homomorphism():
    real_state, left_real, right_real = _two_module_state()
    abstract_state, left_abs, right_abs = _two_module_state()

    real_state.pmerge(left_real, right_real)
    real_projection = map_vm_to_abstract(real_state)

    abstract_projection_before = map_vm_to_abstract(abstract_state)
    abstract_projection_after = abstract_pmerge(
        abstract_projection_before, left_abs, right_abs
    )

    assert real_projection == abstract_projection_after


def test_lassert_homomorphism():
    real_state, module_real = _fresh_state()
    abstract_state, module_abs = _fresh_state()

    real_state.add_axiom(module_real, "witness axiom")
    real_projection = map_vm_to_abstract(real_state)

    abstract_projection_before = map_vm_to_abstract(abstract_state)
    abstract_projection_after = abstract_lassert(
        abstract_projection_before, module_abs, "witness axiom"
    )

    assert real_projection == abstract_projection_after


def test_pmerge_self_merge_rejected_consistently():
    state, module = _fresh_state()
    abstract = map_vm_to_abstract(state)

    with pytest.raises(ValueError):
        state.pmerge(module, module)

    with pytest.raises(ValueError):
        abstract_pmerge(abstract, module, module)
