# Standard Programs - Thiele vs Classical Comparison

This directory contains **normal, real-world programs** that a typical developer
would write. Each program is run both classically (blind mode) and with the
Thiele architecture (sighted mode) to demonstrate the separation.

## Programs

### 1. Password Cracker (`password_cracker.py`)
A simple brute-force password finder - shows how Thiele handles search spaces.

### 2. Sudoku Solver (`sudoku_solver.py`)
Classic 9x9 Sudoku solver - constraint propagation and backtracking.

### 3. Graph Coloring (`graph_coloring.py`)
Color a graph with minimum colors - NP-complete problem.

### 4. Knapsack Problem (`knapsack.py`)
0/1 Knapsack optimization - classic dynamic programming.

### 5. Prime Sieve (`prime_sieve.py`)
Find all primes up to N - standard algorithm comparison.

### 6. Anagram Finder (`anagram_finder.py`)
Find all anagrams in a word list - string processing.

### 7. Maze Solver (`maze_solver.py`)
Find path through a maze - graph search.

### 8. Expression Evaluator (`expression_eval.py`)
Parse and evaluate mathematical expressions.

## Running Comparisons

```bash
# Run all comparisons
python3 demos/standard-programs/run_comparisons.py

# Run specific program
python3 demos/standard-programs/password_cracker.py
```

## What We're Testing

1. **Correctness**: Both modes produce identical results
2. **μ-Cost**: Track information-theoretic cost in Thiele mode
3. **Separation**: Show when structure helps (and when it doesn't)
4. **Isomorphism**: Verify VM/RTL/Coq alignment on real programs
