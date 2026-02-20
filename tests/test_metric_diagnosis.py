"""Diagnose the metric_component definition."""


def metric_component(mu, nu, v1, v2, edge_length_func):
    """Current definition from RiemannTensor4D.v."""
    if (mu == v1 and nu == v2):
        return edge_length_func(mu, nu)
    elif (mu == v2 and nu == v1):
        return edge_length_func(mu, nu)
    else:
        return 0


def test_metric_component_uniform_mass():
    """Test metric components with uniform mass."""
    # For uniform mass m, edge_length(a,b) = 2m for all a,b
    m = 5
    def edge_length_uniform(a, b):
        return 2 * m

    # Collect all non-zero metric components at each position
    nonzero_components = []
    for w in range(4):
        for mu in range(4):
            for nu in range(4):
                g = metric_component(mu, nu, w, w, edge_length_uniform)
                if g != 0:
                    nonzero_components.append((w, mu, nu, g))

    # Verify metric is only non-zero when μ=ν=w
    for w, mu, nu, g in nonzero_components:
        assert mu == nu == w, f"Metric should only be non-zero when μ=ν=w, but got non-zero at w={w}, μ={mu}, ν={nu}"
        assert g == 2 * m, f"Metric value should be 2*m={2*m}, got {g}"


def test_metric_position_dependence():
    """Test that current metric definition is position-dependent even with uniform mass."""
    m = 5
    def edge_length_uniform(a, b):
        return 2 * m

    # For each direction (μ, ν), collect metric values at different positions
    metric_values_at_positions = {}

    for mu in range(4):
        for nu in range(4):
            values = []
            for w in range(4):
                g = metric_component(mu, nu, w, w, edge_length_uniform)
                values.append(g)
            metric_values_at_positions[(mu, nu)] = values

    # Check if diagonal components vary with position
    diagonal_varies = False
    for mu in range(4):
        values = metric_values_at_positions[(mu, mu)]
        if len(set(values)) > 1:
            diagonal_varies = True
            break

    # The current definition makes diagonal components position-dependent
    # g[μ,μ](w,w) is only non-zero when μ=w
    assert diagonal_varies, "Metric diagonal components should vary with position in current definition"


def test_flat_spacetime_expectation():
    """Test that for truly flat spacetime, metric should be position-independent."""
    # For flat uniform-mass spacetime, we expect:
    # g[μ,ν](w,w) = δ_{μν}·(2m) for ALL w (independent of position)

    # This test documents the EXPECTED behavior, not current behavior
    m = 5
    expected_diagonal = 2 * m
    expected_off_diagonal = 0

    # Verify expectations are well-defined
    assert expected_diagonal > 0, "Diagonal should be positive"
    assert expected_off_diagonal == 0, "Off-diagonal should be zero"
