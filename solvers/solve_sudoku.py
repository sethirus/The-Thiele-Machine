import time
from scripts.sudoku_cnf_provider import SudokuCnfProvider
from scripts.thiele_simulator import ThieleSimulator

# The "World's Hardest Sudoku"
puzzle_string = "800000000003600000070090200050007000000045700000100030001000068008500010090000400"

def print_solution(model, provider):
    # A function to beautifully print the final 9x9 grid
    board = [['.' for _ in range(9)] for _ in range(9)]
    if model:
        pos = {v for v in model if v > 0}
        for r in range(1, 10):
            for c in range(1, 10):
                for d in range(1, 10):
                    if provider.get_var(r, c, d) in pos:
                        board[r-1][c-1] = str(d)
    
    for row in board:
        print(" ".join(row))

start_time = time.time()

print("="*40)
print("Thiele Machine vs. The World's Hardest Sudoku")
print("="*40)

provider = SudokuCnfProvider(puzzle_string)
simulator = ThieleSimulator(provider)

print("Loading puzzle and rules into the engine...")
# The ThieleSimulator's solve method implicitly loads the whole problem
# which is fine for this lightweight case.
solution_model = simulator.solve()

end_time = time.time()

if solution_model:
    print("\n>>> DEDUCTIVE COLLAPSE COMPLETE. SOLUTION FOUND. <<<")
    print(f"Total Time: {end_time - start_time:.4f} seconds.\n")
    print_solution(solution_model, provider)
else:
    print("\n>>> MISSION FAILED. NO SOLUTION FOUND. <<<")