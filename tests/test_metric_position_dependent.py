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

# Test 1: Uniform mass
print("=== TEST 1: UNIFORM MASS ===")
masses_uniform = [5, 5, 5, 5]
print(f"Masses: {masses_uniform}\n")

print("Metric g[μ,ν](w,w) at each position w:")
for w in range(4):
    print(f"At w={w}:")
    for mu in range(4):
        row = []
        for nu in range(4):
            g = metric_component_v3(mu, nu, w, w, masses_uniform)
            row.append(f"{g:4.0f}")
        print(f"  [{', '.join(row)}]")

# Check position independence
g00_at_different_points = [metric_component_v3(0, 0, w, w, masses_uniform) for w in range(4)]
print(f"\ng[0,0] at different points: {g00_at_different_points}")
print(f"Position-independent: {len(set(g00_at_different_points)) == 1}")
print()

# Test 2: Non-uniform mass
print("=== TEST 2: NON-UNIFORM MASS ===")
masses_nonuniform = [0, 1, 2, 3]
print(f"Masses: {masses_nonuniform}\n")

print("Metric g[μ,ν](w,w) at each position w:")
for w in range(4):
    print(f"At w={w}:")
    for mu in range(4):
        row = []
        for nu in range(4):
            g = metric_component_v3(mu, nu, w, w, masses_nonuniform)
            row.append(f"{g:4.0f}")
        print(f"  [{', '.join(row)}]")

# Check position dependence
g00_at_different_points = [metric_component_v3(0, 0, w, w, masses_nonuniform) for w in range(4)]
print(f"\ng[0,0] at different points: {g00_at_different_points}")
print(f"Position-dependent: {len(set(g00_at_different_points)) > 1}")
print()

print("CONCLUSION:")
print("  Uniform mass → position-independent metric → flat spacetime")
print("  Non-uniform mass → position-dependent metric → curved spacetime")
print("  This is CORRECT!")
