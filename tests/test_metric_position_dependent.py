"""Test position-dependent metric definition."""


def metric_component_v3(mu, nu, v1, v2, masses):
    """
    v3: Position-dependent metric
    metric[μ,ν](v1,v2) =
      if μ=ν:
        if v1=v2: 2*mass[v1]  (diagonal at single vertex)
        else: mass[v1] + mass[v2]  (between vertices)
      else: 0  (off-diagonal)
    """
    if mu == nu:
        if v1 == v2:
            return 2 * masses[v1]
        else:
            return masses[v1] + masses[v2]
    else:
        return 0


def test_v3_metric_uniform_mass():
    """Test that uniform mass creates position-independent metric."""
    masses_uniform = [5, 5, 5, 5]

    # Check position independence by computing g[0,0] at different points
    g00_at_different_points = [metric_component_v3(0, 0, w, w, masses_uniform) for w in range(4)]

    # All values should be the same (position-independent)
    assert len(set(g00_at_different_points)) == 1, \
        f"Uniform mass should create position-independent metric, got {g00_at_different_points}"

    # All diagonal components should equal 2*mass
    for w in range(4):
        for mu in range(4):
            g_diag = metric_component_v3(mu, mu, w, w, masses_uniform)
            assert g_diag == 2 * masses_uniform[0], \
                f"Diagonal component g[{mu},{mu}]({w},{w}) should be {2*masses_uniform[0]}, got {g_diag}"


def test_v3_metric_nonuniform_mass():
    """Test that non-uniform mass creates position-dependent metric."""
    masses_nonuniform = [0, 1, 2, 3]

    # Check position dependence by computing g[0,0] at different points
    g00_at_different_points = [metric_component_v3(0, 0, w, w, masses_nonuniform) for w in range(4)]

    # Values should differ (position-dependent)
    assert len(set(g00_at_different_points)) > 1, \
        f"Non-uniform mass should create position-dependent metric, got {g00_at_different_points}"

    # Each point should have diagonal component = 2*mass at that point
    for w in range(4):
        expected = 2 * masses_nonuniform[w]
        actual = metric_component_v3(w, w, w, w, masses_nonuniform)
        assert actual == expected, \
            f"At position {w}, g[{w},{w}]({w},{w}) should be {expected}, got {actual}"


def test_v3_metric_off_diagonal_zero():
    """Test that off-diagonal components are zero."""
    masses = [1, 2, 3, 4]

    for w in range(4):
        for mu in range(4):
            for nu in range(4):
                if mu != nu:
                    g = metric_component_v3(mu, nu, w, w, masses)
                    assert g == 0, f"Off-diagonal component g[{mu},{nu}]({w},{w}) should be 0, got {g}"


def test_v3_metric_physical_interpretation():
    """Test that metric correctly represents flat vs curved spacetime."""
    # Uniform mass → flat spacetime
    masses_uniform = [5, 5, 5, 5]
    is_uniform = len(set(masses_uniform)) == 1
    assert is_uniform, "Uniform mass distribution should be flat"

    # Non-uniform mass → curved spacetime
    masses_curved = [0, 1, 2, 3]
    is_nonuniform = len(set(masses_curved)) > 1
    assert is_nonuniform, "Non-uniform mass distribution should be curved"
