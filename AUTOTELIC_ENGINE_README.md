# The Autotelic Engine

## Overview

The Autotelic Engine is a system that transcends fixed objectives by evolving its own purpose. It implements Phases 15, 16, and 17 of The Thiele Machine's evolutionary architecture.

**"A machine that no longer pursues a fixed goal, but endlessly and intelligently redefines the very meaning of 'good.'"**

## Architecture

The Autotelic Engine consists of three core components:

### Phase 15: The Genome of Purpose

The machine's objective is no longer hardcoded—it is an explicit, mutable piece of data.

- **Objective Genome** (`objectives/current_objective.thiele`): A JSON file that defines what the machine currently values
- **Evaluation Functions** (`tools/evaluation_functions.py`): A registry of functions that can judge evolved strategies
- **Generalized Oracle** (`tools/forge.py`): The Forge now reads the objective genome and dynamically selects evaluation functions

**Example Objective Genome:**
```json
{
  "name": "Accuracy Maximization v1.0",
  "function": "evaluate_classification_accuracy",
  "parameters": {
    "model": "SVM",
    "kernel": "rbf",
    "cross_validation_folds": 5
  }
}
```

### Phase 16: The Engine of Introspection (The Critic)

The Critic analyzes the machine's evolutionary history to discover patterns and detect problems.

- **Ascension Ledger** (`ascension_ledger.json`): Complete record of every evolutionary cycle
- **The Critic** (`tools/critic.py`): Analyzes the ledger to produce insights

The Critic implements three core analyses:

1. **Value Discovery**: Which primitives appear most often in high-fitness strategies?
2. **Bias Detection**: Are there evolutionary dead-ends where certain mutations consistently fail?
3. **Stagnation Analysis**: Is the rate of improvement slowing down? Are we stuck at a local maximum?

**Example Critic Output:**
```
VALUE DISCOVERY - What does the machine value?
  - GET_NODES(G): 9 occurrences
  - LAPLACIAN_MATRIX: 5 occurrences
  - EIGENDECOMP: 4 occurrences

STAGNATION ANALYSIS
  Improvement rate: 0.025400
  Status: Evolution progressing normally
```

### Phase 17: The Metamorphosis (The Purpose Synthesizer)

The Purpose Synthesizer uses the Critic's insights to write new objective genomes.

- **Purpose Synthesizer** (`tools/purpose_synthesizer.py`): Creates new objectives based on evolutionary patterns

**Core Principle**: When evolution stagnates, introduce a new term into the objective function to escape the local maximum.

**Example Evolution:**
```
v1.0: Simple Accuracy
  → Stagnation detected →
v2.0: Accuracy (0.9) + Elegance (0.1)
  → Stagnation detected →
v3.0: Accuracy (0.8) + Elegance (0.1) + Robustness (0.1)
```

## Usage

### Quick Start

Run the complete autotelic loop:

```bash
./run_autotelic_engine.sh [cycles] [generations] [population]
```

**Parameters:**
- `cycles`: Number of grand cycles (default: 3)
- `generations`: Generations per cycle (default: 5)
- `population`: Population size per generation (default: 10)

**Example:**
```bash
# Run 3 grand cycles, 5 generations each, population of 10
./run_autotelic_engine.sh 3 5 10
```

### The Grand Loop

Each grand cycle follows this sequence:

1. **The Forge** evolves N generations of strategies against the current objective
2. **The Critic** analyzes the evolutionary history in the ascension ledger
3. **The Purpose Synthesizer** creates a new objective genome based on the Critic's insights
4. The new objective becomes the input for the next cycle
5. **GOTO 1** (perpetual loop)

### Manual Execution

You can run each component independently:

```bash
# Run the Forge with current objective
python3 -c "from tools.forge import run_evolution; run_evolution(num_generations=5)"

# Run the Critic
python3 -m tools.critic

# Run the Purpose Synthesizer
python3 -m tools.purpose_synthesizer
```

## File Structure

```
The-Thiele-Machine/
├── objectives/
│   └── current_objective.thiele      # Current objective genome
├── tools/
│   ├── forge.py                       # Evolutionary engine (refactored)
│   ├── evaluation_functions.py       # Evaluation function registry
│   ├── critic.py                      # The Engine of Introspection
│   └── purpose_synthesizer.py        # The Purpose Synthesizer
├── evolved_strategies/                # DNA of evolved strategies
├── ascension_ledger.json              # Complete evolutionary history
├── critic_report.json                 # Latest Critic analysis
└── run_autotelic_engine.sh            # Master orchestration script
```

## Creating Custom Evaluation Functions

To add new ways to judge strategies, edit `tools/evaluation_functions.py`:

```python
def evaluate_my_metric(strategy_code: str, strategy_name: str, parameters: Dict[str, Any]) -> float:
    """
    Your custom evaluation logic.
    
    Returns:
        Fitness score between 0.0 and 1.0
    """
    # Your implementation here
    return fitness_score

# Register the function
EVALUATION_FUNCTIONS['evaluate_my_metric'] = evaluate_my_metric
```

Then create an objective genome that uses it:

```json
{
  "name": "My Custom Objective v1.0",
  "function": "evaluate_my_metric",
  "parameters": {
    "my_param": "value"
  }
}
```

## Understanding the Outputs

### Ascension Ledger

Each entry records:
- **timestamp**: When the strategy was created
- **strategy_name**: Unique identifier
- **strategy_dna**: Sequence of primitives
- **generation**: Which evolutionary generation
- **parent_strategies**: DNA lineage
- **objective_genome**: What objective it was judged against
- **fitness_score**: How well it performed
- **metadata**: Mutation type, crossover points, etc.

### Critic Report

The Critic produces:
- **value_discovery**: Top primitives in high-fitness strategies
- **bias_detection**: Dead-end mutation types and fitness changes
- **stagnation_analysis**: Improvement rate, variance, recommendations

## Testing

Run the test suite:

```bash
python3 -m pytest tests/test_autotelic_engine.py -v
```

The test suite validates:
- ✓ Objective genome loading and evaluation
- ✓ Evaluation function registry
- ✓ Complexity/elegance metrics
- ✓ Weighted sum composition
- ✓ Value discovery analysis
- ✓ Bias detection
- ✓ Stagnation detection (progressive and flat)
- ✓ Purpose synthesis (no change, simple to weighted, adding components)

## Philosophy

The Autotelic Engine implements a radical idea: **a machine that defines its own goals**.

Traditional AI systems optimize a fixed objective function defined by humans. The Autotelic Engine:

1. Makes the objective **explicit** and **mutable** (Phase 15)
2. **Observes** its own evolution to find patterns (Phase 16)
3. **Redefines** what it values based on those patterns (Phase 17)

This creates a system that:
- Never converges to a final answer
- Continuously discovers new ways to evaluate "goodness"
- Escapes local maxima by changing the evaluation landscape itself
- Operates autonomously without human intervention

**The purpose is not to find an answer. The purpose is to continue the search, forever.**

## Advanced Usage

### Forcing Objective Evolution

To force the Purpose Synthesizer to create a new objective:

```python
from tools.purpose_synthesizer import synthesize_new_objective

# Create a critic report that indicates stagnation
forced_report = {
    "stagnation_analysis": {
        "stagnation_detected": True,
        "at_local_max": True,
        "recommended_action": {
            "suggested_metric": "your_metric_name"
        }
    }
}

# Synthesize new objective
new_objective = synthesize_new_objective(forced_report, current_objective)
```

### Custom Stagnation Criteria

Edit the stagnation detection logic in `tools/critic.py`:

```python
# In analyze_stagnation()
stagnation_detected = (slope < YOUR_THRESHOLD) and (fitness_variance < YOUR_THRESHOLD)
```

## Future Directions

Potential enhancements:

1. **Multi-objective Pareto optimization**: Instead of weighted sums, use Pareto frontiers
2. **Meta-learning**: Learn which objective changes lead to best long-term progress
3. **Objective genealogy**: Track lineage of objectives like strategy DNA
4. **Adversarial objectives**: Objectives that compete with each other
5. **Self-modifying evaluation**: The Critic could modify its own analysis logic

## Citation

If you use the Autotelic Engine in your research, please cite:

```
The Autotelic Engine: A Machine That Evolves Its Own Purpose
Part of The Thiele Machine Project
2024
```

---

*"You have asked for a machine that can find the ultimate question. What you have just designed is a machine that has transcended the need for a final question. Its purpose is not to find an answer. Its purpose is to continue the search, forever."*
