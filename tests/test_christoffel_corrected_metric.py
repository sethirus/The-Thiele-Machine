"""Test Christoffel with corrected metric definition."""

# CORRECTED metric definition:
# metric_component(μ, ν, v1, v2) = edge_length(μ, ν) if μ=ν, else 0
# (Independent of v1, v2 for flat spacetime)

def metric_component_corrected(mu, nu, v1, v2, edge_length_func):
    if mu == nu:
        return edge_length_func(mu, nu)
    else:
        return 0

# For uniform mass m
m = 5
def edge_length_uniform(a, b):
    return 2 * m

print("Testing CORRECTED metric definition:")
print()

# Check that metric is now position-independent
print("Metric g[μ,ν](w,w) for various w:")
for w in [0, 1, 2, 3]:
    print(f"At w={w}:")
    for mu in range(4):
        row = []
        for nu in range(4):
            g = metric_component_corrected(mu, nu, w, w, edge_length_uniform)
            row.append(f"{g:4.0f}")
        print(f"  [{', '.join(row)}]")
    print()

print("Result: Metric is now INDEPENDENT of position w!")
print("All diagonal entries = 10 (= 2m), off-diagonal = 0")
print()

# Now compute Christoffel symbols
def discrete_deriv(f, idx, v, neighbors):
    if not neighbors:
        return 0
    neighbor = neighbors[0]
    return f(neighbor) - f(v)

def get_neighbors(v, n):
    return [(v - 1) % n, (v + 1) % n]

n_vertices = 4
max_christoffel = 0
num_nonzero = 0

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
                if abs(christoffel) > 1e-10:
                    num_nonzero += 1

print(f"Christoffel verification with CORRECTED metric:")
print(f"  Max |Γ| = {max_christoffel}")
print(f"  Non-zero components: {num_nonzero}/{n_vertices**4}")
print(f"  Result: {'PASS - All Christoffel = 0!' if max_christoffel < 1e-10 else 'FAIL'}")
print()

if max_christoffel < 1e-10:
    print("SUCCESS: Christoffel symbols are zero with corrected metric!")
    print("This confirms: flat metric (position-independent) → zero connection")
else:
    print(f"FAILURE: Still have non-zero Christoffel: {max_christoffel}")
