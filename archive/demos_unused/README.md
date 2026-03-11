# Demos

Example programs and demonstrations of the Thiele Machine.

## Contents

### benchmarks/
Performance benchmarks demonstrating mu-cost advantages:
- `advantage_benchmarks.py` - Binary search and constraint propagation benchmarks

### scripts/
Demonstration scripts showing Thiele Machine applications:

| Script | Description |
|--------|-------------|
| `shor_on_thiele_demo.py` | Shor-style period reasoning demonstration |
| `graph_coloring_demo.py` | Graph coloring problem solver |
| `solve_sudoku.py` | Sudoku solver using the Thiele Machine |
| `solve_tsp.py` | TSP solver using PDISCOVER instruction |
| `tsp_solver.py` | Full TSP solver implementation |
| `tsp_optimizer.py` | TSP optimization with mu-cost tracking |
| `demo_isomorphism_cli.py` | CLI for isomorphism demonstration |
| `demo_leaky_tag.py` | Security vulnerability demonstration |

## Running Demos

```bash
# From the repository root:
python demos/scripts/shor_on_thiele_demo.py
python demos/scripts/solve_sudoku.py
python demos/benchmarks/advantage_benchmarks.py
```
