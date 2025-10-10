# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import time
from scripts.tsp_cnf_provider import TspCnfProvider
from thielecpu.vm import VM
from thielecpu.state import State
import ast

# Define coordinates for att48 TSP problem (48 cities)
cities = [
    (6734.0, 1453.0), (2233.0, 10.0), (5530.0, 1424.0), (401.0, 841.0),
    (3082.0, 1644.0), (7608.0, 4458.0), (7573.0, 3716.0), (7265.0, 1268.0),
    (6898.0, 1885.0), (1112.0, 2049.0), (5468.0, 2605.0), (5989.0, 2873.0),
    (4706.0, 2674.0), (4612.0, 2035.0), (6347.0, 2683.0), (6107.0, 669.0),
    (7611.0, 5184.0), (7462.0, 3590.0), (7732.0, 4723.0), (5900.0, 3561.0),
    (4483.0, 3369.0), (6101.0, 1110.0), (5199.0, 2182.0), (1633.0, 2809.0),
    (4307.0, 2322.0), (675.0, 1006.0), (7555.0, 4819.0), (7541.0, 3981.0),
    (3177.0, 756.0), (7352.0, 4506.0), (7545.0, 2801.0), (3245.0, 3305.0),
    (6426.0, 3173.0), (4608.0, 1198.0), (23.0, 2216.0), (7248.0, 3779.0),
    (7762.0, 4595.0), (7392.0, 2244.0), (3484.0, 2829.0), (6271.0, 2135.0),
    (4985.0, 140.0), (1916.0, 1569.0), (7280.0, 4899.0), (7509.0, 3239.0),
    (10.0, 2676.0), (6807.0, 2993.0), (5185.0, 3258.0), (288.0, 611.0)
]

# Known optimal length: 10628
# We aim to find a tour of length < 10628
CHALLENGE_LENGTH = 10628

provider = TspCnfProvider(cities=cities, max_length=CHALLENGE_LENGTH)

print("="*60)
print("Thiele Machine vs. The Traveling Salesman Problem")
print(f"Cities: {len(cities)}")
print(f"Target: Find a tour of length < {CHALLENGE_LENGTH}")
print("="*60)

start_time = time.time()
# Solve using the virtual machine
clauses = provider.get_all_clauses()
code = f"""
from pysat.solvers import Glucose4

clauses = {clauses}

solver = Glucose4()
for cls in clauses:
    solver.add_clause(cls)

if solver.solve():
    model = solver.get_model()
    print('SAT')
    print(repr(model))
else:
    print('UNSAT')
"""

vm = VM(State())
_, output = vm.execute_python(code)

if 'SAT' in output:
    lines = output.strip().split('\n')
    for line in lines:
        if line.startswith('[') and line.endswith(']'):
            solution_model = ast.literal_eval(line)
            break
else:
    solution_model = None
end_time = time.time()

if solution_model:
    tour = provider.decode_tour(solution_model)
    length = provider.calculate_length(tour)
    print("\n>>> TOUR FOUND <<<")
    print(f"Tour: {tour}")
    print(f"Length: {length:.4f}")
    if length < CHALLENGE_LENGTH:
        print(">>> CHALLENGE MET: Shorter than target! <<<")
    else:
        print(">>> Challenge not met, but a valid tour found. <<<")
else:
    print("\n>>> NO TOUR FOUND <<<")

print(f"Total Time: {end_time - start_time:.4f} seconds.")