import pytest
from measure_cost_separation import run_experiment, DATASET

def test_blind_model_is_inconsistent_and_has_infinite_mdl():
    """
    The blind model (trivial partition) on the paradox dataset
    must be logically inconsistent and thus have an infinite MDL cost.
    """
    blind_partition = ((0, 1, 2, 3),)
    receipt = run_experiment(DATASET, blind_partition)

    assert receipt['is_consistent'] is False
    assert receipt['mdl_cost_bits'] == float('inf')

def test_sighted_model_is_consistent_and_has_finite_mdl():
    """
    The sighted model (correct partition) must be consistent
    and have a measurable, finite MDL cost.
    """
    # The hidden dimension `d` in the dataset is [0,0,0,1]
    # So the correct partition is points {A,B,C} vs {D}
    sighted_partition = ((0, 1, 2), (3,))
    receipt = run_experiment(DATASET, sighted_partition)

    assert receipt['is_consistent'] is True
    assert receipt['mdl_cost_bits'] < float('inf')
    assert receipt['mdl_cost_bits'] > 0
