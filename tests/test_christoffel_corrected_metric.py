"""Test Christoffel with corrected metric definition."""

# CORRECTED metric definition:
# metric_component(μ, ν, v1, v2) = edge_length(μ, ν) if μ=ν, else 0
# (Independent of v1, v2 for flat spacetime)

def metric_component_corrected(mu, nu, v1, v2, edge_length_func):
    if mu == nu:
        return edge_length_func(mu, nu)
    else:
        return 0

def discrete_deriv(f, idx, v, neighbors):
    if not neighbors:
        return 0
    neighbor = neighbors[0]
    return f(neighbor) - f(v)

def get_neighbors(v, n):
    return [(v - 1) % n, (v + 1) % n]


def test_christoffel_corrected_metric():
    """Test that Christoffel symbols are zero with corrected flat metric."""
    # For uniform mass m
    m = 5
    def edge_length_uniform(a, b):
        return 2 * m

    # Check that metric is position-independent
    n_vertices = 4
    for w in range(n_vertices):
        for mu in range(n_vertices):
            for nu in range(n_vertices):
                g = metric_component_corrected(mu, nu, w, w, edge_length_uniform)
                if mu == nu:
                    assert g == 10, f"Diagonal metric g[{mu},{nu}](w={w}) should be 10"
                else:
                    assert g == 0, f"Off-diagonal metric g[{mu},{nu}](w={w}) should be 0"

    # Compute Christoffel symbols - should all be zero for flat metric
    max_christoffel = 0

    for rho in range(n_vertices):
        for mu in range(n_vertices):
            for nu in range(n_vertices):
                for v in range(n_vertices):
                    neighbors_mu = get_neighbors(v, n_vertices)
                    neighbors_nu = get_neighbors(v, n_vertices)
                    neighbors_rho = get_neighbors(v, n_vertices)

                    # Three metric derivatives
                    deriv_mu_g_nu_rho = discrete_deriv(
                        lambda w: metric_component_corrected(nu, rho, w, w, edge_length_uniform),
                        mu, v, neighbors_mu
                    )
                    deriv_nu_g_mu_rho = discrete_deriv(
                        lambda w: metric_component_corrected(mu, rho, w, w, edge_length_uniform),
                        nu, v, neighbors_nu
                    )
                    deriv_rho_g_mu_nu = discrete_deriv(
                        lambda w: metric_component_corrected(mu, nu, w, w, edge_length_uniform),
                        rho, v, neighbors_rho
                    )

                    # Christoffel combination
                    christoffel = 0.5 * (
                        deriv_mu_g_nu_rho + deriv_nu_g_mu_rho - deriv_rho_g_mu_nu
                    )

                    max_christoffel = max(max_christoffel, abs(christoffel))

    # Assert all Christoffel symbols are zero
    assert max_christoffel < 1e-10, f"Christoffel symbols should be zero, max={max_christoffel}"

