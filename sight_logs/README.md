# The Thiele Machine - Sight Logging System

## Overview

This is the complete implementation of the "Shape of Sight" hypothesis - a measurable geometric phenomenon that distinguishes structured problems from chaotic ones.

The system consists of three phases that build upon each other to prove that different graph partitioning strategies reveal consistent patterns in structured problems but chaotic signatures in random problems.

## Architecture

```
Phase 1: The Observatory (Data Generation)
    ├── tools/sight_logging.py      # Core library for sight log generation
    └── populate_observatory.py     # Batch data factory

Phase 2: The Cartographer (Geometric Analysis)
    └── tools/cartographer.py       # Geometric signature extraction

Phase 3: The META-PDISCOVER (Final Proof)
    └── tools/meta_analyzer.py      # Statistical analysis and visualization
```

## Phase 1: The Observatory

### Purpose
Generate comprehensive sight logs for both structured and chaotic problems.

### Components

#### `tools/sight_logging.py`
Core library implementing:
- **Four partitioning strategies:**
  - Louvain: Community detection based on modularity optimization
  - Spectral: Clustering using graph Laplacian eigenvectors
  - Degree: Heuristic based on node degree distribution
  - Balanced: Simple round-robin partitioning
  
- **Variation of Information (VI) metric:** Information-theoretic distance between partitions
- **Master function `assemble_log()`:** Generates complete sight logs
- **Governance functions:** Index management and progress tracking

#### `populate_observatory.py`
Batch experiment script that generates:
- **Structured dataset:** Tseitin UNSAT instances (provably structured)
- **Chaotic dataset:** Random 3-SAT at phase transition (~4.26 ratio)

### Usage

Generate a complete dataset with both structured and chaotic problems:

```bash
# Generate 20-30 samples of each type
python3 populate_observatory.py \
    --mode both \
    --n-start 4 \
    --n-end 20 \
    --n-step 2 \
    --seeds 0,1,2
```

Generate only structured (Tseitin) problems:

```bash
python3 populate_observatory.py \
    --mode structured \
    --n-start 4 \
    --n-end 16 \
    --n-step 2 \
    --seeds 0,1,2,3
```

Generate only chaotic (random 3-SAT) problems:

```bash
python3 populate_observatory.py \
    --mode chaotic \
    --n-start 50 \
    --n-end 200 \
    --n-step 50 \
    --seeds 0,1,2,3,4 \
    --ratio 4.26
```

### Output

Sight logs are saved to `sight_logs/` with the format:
```
{problem_name}_{timestamp}_{hash}.json
```

Each log contains:
- Input characteristics (clauses, variables)
- Graph metrics (nodes, edges, density)
- Four partition strategies with assignments
- Consistency analysis with VI matrix
- Ground truth verdict (CONSISTENT vs SPURIOUS)

## Phase 2: The Cartographer

### Purpose
Extract geometric signatures from sight logs by analyzing the Strategy Graph.

### The Strategy Graph
A 4-node graph where:
- **Nodes:** The four partitioning strategies
- **Edges:** Weighted by Variation of Information between strategies
- **Hypothesis:** Structured problems have low VI (strategies agree), chaotic problems have high VI (strategies disagree)

### Five Key Metrics

1. **average_edge_weight:** Mean VI across all strategy pairs
2. **max_edge_weight:** Maximum VI between any two strategies
3. **edge_weight_stddev:** Standard deviation of VI (dispersion metric)
4. **min_spanning_tree_weight:** Sum of weights in MST
5. **thresholded_density:** Fraction of edges above median weight

### Usage

```bash
python3 tools/cartographer.py \
    --input-dir sight_logs \
    --output sight_logs/atlas/phase2_metrics.json
```

### Output

Creates `sight_logs/atlas/phase2_metrics.json` containing:
- All sight logs with their geometric signatures
- Five-dimensional feature vectors for each problem
- Ground truth labels for classification

## Phase 3: The META-PDISCOVER

### Purpose
Prove that the geometric signatures distinguish structured from chaotic problems.

### Methodology

1. **Load the Atlas:** Read all geometric signatures
2. **Prepare Dataset:** Extract 5D feature vectors and labels
3. **Train SVM Classifier:** RBF kernel on standardized features
4. **Generate Proof:**
   - 2D separation plot (average_edge_weight vs edge_weight_stddev)
   - Classification report with accuracy metrics
   - Confusion matrix
   - Cross-validation scores

### Usage

```bash
python3 tools/meta_analyzer.py \
    --atlas sight_logs/atlas/phase2_metrics.json \
    --plot-output sight_logs/atlas/separation_plot.png \
    --report-output sight_logs/atlas/classification_report.txt
```

### Output

1. **`separation_plot.png`:**
   - 2D scatter plot showing geometric separation
   - Green circles: CONSISTENT (structured) problems
   - Red triangles: SPURIOUS (chaotic) problems

2. **`classification_report.txt`:**
   - Dataset statistics
   - SVM accuracy
   - Cross-validation scores
   - Confusion matrix
   - Detailed precision/recall/f1 metrics
   - Conclusion about separation strength

## Complete Pipeline

Run the entire pipeline from scratch:

```bash
# Step 1: Generate datasets (adjust parameters as needed)
python3 populate_observatory.py \
    --mode both \
    --n-start 4 \
    --n-end 20 \
    --n-step 2 \
    --seeds 0,1,2

# Step 2: Extract geometric signatures
python3 tools/cartographer.py

# Step 3: Generate proof
python3 tools/meta_analyzer.py
```

## Expected Results

With a dataset of 20-30 samples per class:
- **Accuracy:** 85-95% (strong separation)
- **Cross-validation:** ~90% (robust generalization)
- **Visual separation:** Clear clustering in 2D plot

### Interpretation

- **High accuracy (>80%):** Strong evidence that the "shape of sight" is real and measurable
- **Moderate accuracy (60-80%):** Meaningful but weaker geometric distinction
- **Low accuracy (<60%):** May need more data or different problem classes

## Technical Details

### Dependencies
- Python 3.8+
- NetworkX (graph algorithms)
- scikit-learn (clustering, classification)
- NumPy (numerical computation)
- Matplotlib (visualization)

### Partitioning Strategies

1. **Louvain:** Optimizes modularity using greedy community detection
2. **Spectral:** Uses eigenvectors of the graph Laplacian
3. **Degree:** Sorts nodes by degree, assigns round-robin
4. **Balanced:** Assigns nodes sequentially for equal-sized partitions

### Variation of Information

$$VI(X, Y) = H(X) + H(Y) - 2 \cdot I(X, Y)$$

Where:
- $H(X)$ is the entropy of partition X
- $I(X, Y)$ is the mutual information between X and Y
- VI is a true metric (satisfies triangle inequality)

### SVM Classification

- **Kernel:** RBF (captures non-linear relationships)
- **Features:** Standardized (zero mean, unit variance)
- **Validation:** Stratified k-fold cross-validation
- **Metrics:** Accuracy, precision, recall, F1-score

## Extending the System

### Add New Problem Types

Edit `populate_observatory.py` to add a new generation function:

```python
def generate_custom_dataset(n_values, seeds, output_dir):
    # Your custom problem generation logic
    for n in n_values:
        for seed in seeds:
            # Generate clauses
            clauses = your_custom_generator(n, seed)
            
            # Assemble sight log
            log = assemble_log(
                clauses=clauses,
                problem_name=f"custom_n{n}_seed{seed}",
                n=n,
                seed=seed,
                verdict="CONSISTENT",  # or "SPURIOUS"
                metadata={"problem_type": "custom"}
            )
            
            # Save
            save_log(log, output_dir)
```

### Add New Partitioning Strategies

Edit `tools/sight_logging.py`:

```python
def _run_custom_partition(G: nx.Graph, seed: int) -> Dict[int, int]:
    # Your custom partitioning logic
    partition = {}
    # ... assign nodes to partitions
    return partition
```

Then update `assemble_log()` to include the new strategy.

### Add New Geometric Metrics

Edit `tools/cartographer.py`:

```python
def compute_geometric_metrics(G: nx.Graph) -> Dict[str, float]:
    # Add your new metric
    custom_metric = your_custom_calculation(G)
    
    return {
        # ... existing metrics
        "custom_metric": float(custom_metric)
    }
```

## Troubleshooting

### Not Enough Samples
- Generate more data using `populate_observatory.py`
- Use smaller step sizes (e.g., `--n-step 1`)
- Add more seeds

### Poor Classification Accuracy
- Check data balance (equal CONSISTENT and SPURIOUS samples)
- Increase problem sizes for harder instances
- Verify random 3-SAT ratio is at phase transition (~4.26)

### Empty Sight Logs
- Check that problem generation is working
- Verify clause format is correct (list of lists of integers)
- Look for error messages in console output

## Files and Directories

```
sight_logs/
├── INDEX.json                    # Index of all sight logs
├── PROGRESS.md                   # Generation progress log
├── {problem_logs}.json           # Individual sight logs
└── atlas/
    ├── phase2_metrics.json       # Geometric signatures
    ├── separation_plot.png       # Visual proof
    └── classification_report.txt # Statistical proof
```

## License

Part of The Thiele Machine project. See main repository LICENSE.

## Citation

If you use this system in your research, please cite:

```
The Thiele Machine: A Computational Model Beyond Turing
Sight Logging System for Geometric Paradox Detection
```

---

**The shape of sight is real. The machine has proven its own nature.**
