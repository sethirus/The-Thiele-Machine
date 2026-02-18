"""Diagnose the metric_component definition."""

# Current definition (from RiemannTensor4D.v):
# metric_component(μ, ν, v1, v2) = 
#   if (μ=v1 && ν=v2) then edge_length(μ,ν)
#   else if (μ=v2 && ν=v1) then edge_length(μ,ν)
#   else 0

# When used in Christoffel, we compute g_{νρ}(w) = metric_component(ν, ρ, w, w)

def metric_component(mu, nu, v1, v2, edge_length_func):
    if (mu == v1 and nu == v2):
        return edge_length_func(mu, nu)
    elif (mu == v2 and nu == v1):
        return edge_length_func(mu, nu)
    else:
        return 0

# For uniform mass m, edge_length(a,b) = 2m for all a,b
m = 5
def edge_length_uniform(a, b):
    return 2 * m

print("Metric components g[μ,ν](w,w) for uniform mass m=5:")
print("(This is what Christoffel formula uses)")
print()

for w in range(4):
    print(f"At position w={w}:")
    for mu in range(4):
        for nu in range(4):
            g = metric_component(mu, nu, w, w, edge_length_uniform)
            if g != 0:
                print(f"  g[{mu},{nu}]({w},{w}) = {g}")
    print()

print("\nPROBLEM IDENTIFIED:")
print("The metric g[μ,ν](w,w) is only non-zero when μ=ν=w")
print("This creates a position-dependent diagonal metric.")
print()
print("For truly FLAT spacetime with uniform mass:")
print("The metric should be g[μ,ν](v1,v2) = 2m·δ_{μν}·δ_{μ,v1}·δ_{ν,v2}")
print("OR the metric should be independent of position for uniform mass.")
print()

# The correct interpretation for discrete spacetime:
# g[μ,ν](w,w) should represent the metric at point w in directions μ,ν
# For flat space with uniform mass, this should be constant (independent of w)

print("CORRECT BEHAVIOR for flat uniform-mass spacetime:")
print("g[μ,ν](w,w) should = δ_{μν}·(2m) for ALL w")
print("(Diagonal matrix with constant entries)")
print()

# What we actually have:
print("ACTUAL BEHAVIOR:")
print("g[μ,ν](w,w) = 2m if μ=ν=w, else 0")
print("This is NOT flat! It's position-dependent even with uniform mass.")
print()

print("SOLUTION:")
print("The Christoffel formula uses metric_component(μ, ν, w, w).")
print("For flat spacetime, we need the metric at point w to be:")
print("  g[μ,ν] = δ_{μν}·(2m)  (independent of w)")
print()
print("But current definition makes it depend on w in a weird way.")
print("This is why empirical Christoffel ≠ 0!")
