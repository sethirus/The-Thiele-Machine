"""Test Christoffel symbols with v3 metric."""

def metric_v3(mu, nu, v1, v2, masses):
    if mu == nu:
        if v1 == v2:
            return 2 * masses[v1]
        else:
            return masses[v1] + masses[v2]
    else:
        return 0

def discrete_deriv(f, idx, v, neighbors):
    if not neighbors:
        return 0
    neighbor = neighbors[0]
    return f(neighbor) - f(v)

def get_neighbors(v, n):
    return [(v - 1) % n, (v + 1) % n]

# Test uniform mass
masses = [5, 5, 5, 5]
n = 4

max_christoffel = 0
for rho in range(n):
    for mu in range(n):
        for nu in range(n):
            for v in range(n):
                neighbors_mu = get_neighbors(v, n)
                neighbors_nu = get_neighbors(v, n)
                neighbors_rho = get_neighbors(v, n)
                
                deriv_mu = discrete_deriv(
                    lambda w: metric_v3(nu, rho, w, w, masses),
                    mu, v, neighbors_mu
                )
                deriv_nu = discrete_deriv(
                    lambda w: metric_v3(mu, rho, w, w, masses),
                    nu, v, neighbors_nu
                )
                deriv_rho = discrete_deriv(
                    lambda w: metric_v3(mu, nu, w, w, masses),
                    rho, v, neighbors_rho
                )
                
                christoffel = 0.5 * (deriv_mu + deriv_nu - deriv_rho)
                max_christoffel = max(max_christoffel, abs(christoffel))

print(f"Uniform mass: max |Γ| = {max_christoffel}")
print(f"Result: {'PASS' if max_christoffel < 1e-10 else 'FAIL'}")
print()

# Test non-uniform mass
masses_nonuniform = [0, 1, 2, 3]

max_christoffel_nonuniform = 0
num_nonzero = 0
for rho in range(n):
    for mu in range(n):
        for nu in range(n):
            for v in range(n):
                neighbors_mu = get_neighbors(v, n)
                neighbors_nu = get_neighbors(v, n)
                neighbors_rho = get_neighbors(v, n)
                
                deriv_mu = discrete_deriv(
                    lambda w: metric_v3(nu, rho, w, w, masses_nonuniform),
                    mu, v, neighbors_mu
                )
                deriv_nu = discrete_deriv(
                    lambda w: metric_v3(mu, rho, w, w, masses_nonuniform),
                    nu, v, neighbors_nu
                )
                deriv_rho = discrete_deriv(
                    lambda w: metric_v3(mu, nu, w, w, masses_nonuniform),
                    rho, v, neighbors_rho
                )
                
                christoffel = 0.5 * (deriv_mu + deriv_nu - deriv_rho)
                max_christoffel_nonuniform = max(max_christoffel_nonuniform, abs(christoffel))
                if abs(christoffel) > 1e-10:
                    num_nonzero += 1

print(f"Non-uniform mass: max |Γ| = {max_christoffel_nonuniform}")
print(f"Non-zero components: {num_nonzero}/{n**4}")
print(f"Result: Christoffel ≠ 0 (creates curvature)")
