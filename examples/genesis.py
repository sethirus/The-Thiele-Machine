import random
import json
from typing import List

# Small, deterministic seed for reproducibility in tests
random.seed(12345)

# Game-of-Life based genesis.py for Thiele VM PYEXEC demo
GRID_SIZE = 32
STEPS = 50


def get_neighbors(g: List[List[int]], x: int, y: int) -> int:
    count = 0
    for i in range(-1, 2):
        for j in range(-1, 2):
            if i == 0 and j == 0:
                continue
            nx, ny = (x + i) % GRID_SIZE, (y + j) % GRID_SIZE
            if g[nx][ny] == 1:
                count += 1
    return count


def measure_complexity(g: List[List[int]]):
    try:
        # If the VM exposes auto_discover_partition, prefer it
        if hasattr(self, 'auto_discover_partition'):
            candidate = self.auto_discover_partition(g)
            return candidate.get('mdl_cost', float('nan'))
        if hasattr(self, 'discover_partition'):
            candidate = self.discover_partition(g)
            return candidate.get('mdl_cost', float('nan'))
    except Exception:
        return float('nan')
    return float('nan')


def main():
    grid = [[random.choice([0, 1]) for _ in range(GRID_SIZE)] for _ in range(GRID_SIZE)]
    results = []
    for step in range(STEPS):
        new_grid = [[0] * GRID_SIZE for _ in range(GRID_SIZE)]
        for x in range(GRID_SIZE):
            for y in range(GRID_SIZE):
                neighbors = get_neighbors(grid, x, y)
                if grid[x][y] == 1 and neighbors in (2, 3):
                    new_grid[x][y] = 1
                elif grid[x][y] == 0 and neighbors == 3:
                    new_grid[x][y] = 1
        grid = new_grid

        current_complexity = measure_complexity(grid)
        print(f'STEP {step}: COMPLEXITY (MDL) = {current_complexity:.6f}')
        results.append({'step': step, 'mdl_cost': current_complexity})

    # Return the final grid for reproducibility
    print('FINAL_STATE: ' + json.dumps({'results': results, 'checksum': sum(sum(row) for row in grid)}))
    return grid


# Execute main unconditionally when invoked via VM PYEXEC
main()
