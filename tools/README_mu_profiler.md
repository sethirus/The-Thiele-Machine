# μ-Profiler: Universal Information Cost Analysis

The μ-Profiler is a practical application of the Thiele Machine that analyzes the information cost (μ-cost) of any Python function. It works with literally any Python callable - functions, methods, lambdas, builtins, C extensions, and more.

## Quick Start

```python
from tools.mu_profiler import analyze

# Analyze any function
result = analyze(my_function)
print(f"μ-cost: {result['mu_cost']}")
print(f"Complexity: {result['complexity']}")
```

## Features

✅ **Universal Compatibility** - Works with any Python callable
✅ **Multiple Analysis Methods** - Source AST, bytecode, and type analysis
✅ **Performance Profiling** - Execution time measurement
✅ **Complexity Estimation** - O(1), O(log n), O(n), O(n²+) classifications
✅ **Actionable Insights** - Optimization suggestions based on μ-cost analysis

## Usage Examples

### Basic Analysis

```python
from tools.mu_profiler import analyze

def fibonacci(n):
    if n <= 1:
        return n
    return fibonacci(n-1) + fibonacci(n-2)

result = analyze(fibonacci)
print(result)
# {
#   'success': True,
#   'mu_cost': 6,
#   'complexity': 'O(1) - Constant',
#   'method': 'bytecode',
#   'insights': [...],
#   'operations': [...],
#   'bytecode_instructions': 19
# }
```

### Performance Profiling

```python
from tools.mu_profiler import profile

@profile
def my_algorithm(data):
    # Your code here
    return result

result = my_algorithm(data)  # Automatically prints μ-profile
```

### Analyzing Built-ins and Libraries

```python
# Works with everything
analyze(len)           # Built-in function
analyze(str.split)     # Method
analyze(lambda x: x*2) # Lambda
analyze(numpy.sum)     # NumPy function
```

## What is μ-Cost?

μ-cost measures the information processing cost of a function based on:
- **Data operations** (assignments, modifications)
- **Control flow** (branches, loops)
- **Function calls** (information revelation)
- **Computational complexity**

Lower μ-cost = more efficient information processing.

## Analysis Methods

1. **Source AST** (Most Accurate)
   - Parses Python source code
   - Counts AST nodes and operations
   - Provides detailed insights

2. **Bytecode Analysis** (Fallback)
   - Analyzes Python bytecode
   - Works when source unavailable
   - Estimates costs from opcodes

3. **Type Analysis** (Last Resort)
   - Uses function metadata
   - Works with C extensions, builtins
   - Basic cost estimation

## Real-World Applications

- **Algorithm Optimization** - Identify information bottlenecks
- **Code Review** - Quantify complexity improvements
- **Performance Analysis** - Beyond execution time
- **Research** - Study information processing in code

## Integration

The μ-Profiler is backed by the Thiele Machine's formal verification system, ensuring accurate μ-cost calculations based on quantum information principles derived from accounting axioms.

## Installation

No installation required! Just import and use:

```python
from tools.mu_profiler import analyze, profile
```

Works immediately with any Python environment.