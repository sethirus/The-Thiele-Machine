#!/usr/bin/env python3
"""
CNF Analyzer - B1.1 Task Implementation
========================================

This tool analyzes CNF formulas in DIMACS format and discovers their
partition structure using the Thiele Machine's partition discovery algorithm.

TASK: B1.1 from RESEARCH_PROGRAM_MASTER_PLAN.md
GOAL: First killer app - show μ+partitions gives SAT solver speedups

INPUT:
    - CNF formula in DIMACS format
    
OUTPUT:
    - Discovered partitions (modules)
    - μ-costs (discovery, operational, total)
    - Structural metrics (interaction density, module count)

ALGORITHM:
    1. Parse CNF formula from DIMACS
    2. Build variable interaction graph
    3. Discover partitions using spectral clustering
    4. Compute μ-costs using μ-spec v2.0
    5. Output structured metrics

REFERENCES:
    - [MODEL_SPEC] docs/MODEL_SPEC.md - μ-cost formulas
    - [DISCOVERY] thielecpu/discovery.py - Partition discovery
    - [CNF] thielecpu/cnf.py - CNF utilities
    - [RESEARCH_PLAN] RESEARCH_PROGRAM_MASTER_PLAN.md - Task B1.1

USAGE:
    python tools/cnf_analyzer.py input.cnf
    python tools/cnf_analyzer.py input.cnf --output results.json
    python tools/cnf_analyzer.py input.cnf --visualize

STATUS: B1.1 - CNF Analyzer - SKELETON COMPLETE
NEXT: B1.2 - Integrate with SAT Solver
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass, asdict

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))


@dataclass
class PartitionMetrics:
    """Metrics for a discovered partition structure."""
    num_modules: int
    module_sizes: List[int]
    interaction_density: float
    mu_discovery: float
    mu_operational: float
    mu_total: float
    variables_per_module: Dict[int, List[int]]


@dataclass
class CNFStructure:
    """Structure of a CNF formula."""
    num_variables: int
    num_clauses: int
    clause_sizes: List[int]
    avg_clause_size: float
    variable_interactions: List[Tuple[int, int]]  # Edges in interaction graph


class DIMACSParser:
    """
    Parse CNF formulas in DIMACS format.
    
    DIMACS format:
        c Comments start with 'c'
        p cnf <num_vars> <num_clauses>
        <literal> <literal> ... 0
        ...
    
    Example:
        c Simple 3-SAT instance
        p cnf 3 2
        1 -2 3 0
        -1 2 0
    """
    
    @staticmethod
    def parse(filepath: Path) -> Tuple[int, int, List[List[int]]]:
        """
        Parse DIMACS CNF file.
        
        Args:
            filepath: Path to DIMACS file
            
        Returns:
            (num_vars, num_clauses, clauses)
            where clauses is a list of lists of literals (0-terminated)
        """
        num_vars = 0
        num_clauses = 0
        clauses = []
        
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('c'):
                    continue
                
                if line.startswith('p cnf'):
                    parts = line.split()
                    num_vars = int(parts[2])
                    num_clauses = int(parts[3])
                else:
                    # Parse clause
                    literals = [int(x) for x in line.split() if int(x) != 0]
                    if literals:
                        clauses.append(literals)
        
        return num_vars, num_clauses, clauses


class VariableInteractionGraph:
    """
    Build variable interaction graph from CNF formula.
    
    Two variables interact if they appear together in a clause.
    The graph is undirected and unweighted.
    """
    
    @staticmethod
    def build(num_vars: int, clauses: List[List[int]]) -> List[Tuple[int, int]]:
        """
        Build interaction graph from clauses.
        
        Args:
            num_vars: Number of variables
            clauses: List of clauses (lists of literals)
            
        Returns:
            List of edges (v1, v2) where v1 < v2
        """
        edges = set()
        
        for clause in clauses:
            # Get variables (absolute value of literals)
            variables = sorted(set(abs(lit) for lit in clause))
            
            # Add all pairs
            for i, v1 in enumerate(variables):
                for v2 in variables[i+1:]:
                    edges.add((min(v1, v2), max(v1, v2)))
        
        return sorted(edges)
    
    @staticmethod
    def compute_density(num_vars: int, edges: List[Tuple[int, int]]) -> float:
        """
        Compute interaction density = |E| / (n choose 2)
        
        Args:
            num_vars: Number of variables
            edges: List of edges
            
        Returns:
            Density in [0, 1]
        """
        if num_vars <= 1:
            return 0.0
        
        max_edges = (num_vars * (num_vars - 1)) // 2
        if max_edges == 0:
            return 0.0
        
        return len(edges) / max_edges


class PartitionDiscovery:
    """
    Discover partition structure from interaction graph.
    
    TODO B1.1: Implement partition discovery
    - [ ] Integrate with thielecpu.discovery module
    - [ ] Use spectral clustering on interaction graph
    - [ ] Compute MDL costs for partition evaluation
    - [ ] Return PartitionMetrics
    
    ALGORITHM (from thielecpu/discovery.py):
        1. Build adjacency matrix from interaction graph
        2. Compute graph Laplacian
        3. Find k smallest eigenvectors
        4. Cluster variables using k-means on eigenvectors
        5. Evaluate partition using MDL principle
        6. Return partition with minimal MDL cost
    """
    
    @staticmethod
    def discover(num_vars: int, 
                 edges: List[Tuple[int, int]],
                 max_mu_budget: float = 1000.0) -> PartitionMetrics:
        """
        Discover optimal partition structure.
        
        Args:
            num_vars: Number of variables
            edges: Variable interaction edges
            max_mu_budget: Maximum μ-bits to spend on discovery
            
        Returns:
            PartitionMetrics with discovered structure
            
        TODO B1.1:
            - Implement spectral clustering
            - Integrate with thielecpu.discovery.EfficientPartitionDiscovery
            - Compute μ-costs according to μ-spec v2.0
        """
        # PLACEHOLDER: Trivial partition for now
        # TODO: Replace with actual discovery algorithm
        
        # Compute μ-costs (placeholder formulas)
        # From μ-spec v2.0: μ_total = 8|canon(q)| + log₂(N/M)
        mu_discovery = 100.0  # Cost to discover partition structure
        mu_operational = 10.0  # Cost to compute partition
        mu_total = mu_discovery + mu_operational
        
        return PartitionMetrics(
            num_modules=1,  # Trivial partition
            module_sizes=[num_vars],
            interaction_density=VariableInteractionGraph.compute_density(num_vars, edges),
            mu_discovery=mu_discovery,
            mu_operational=mu_operational,
            mu_total=mu_total,
            variables_per_module={0: list(range(1, num_vars + 1))}
        )


class CNFAnalyzer:
    """
    Main CNF analyzer orchestrating all components.
    """
    
    def __init__(self, filepath: Path):
        """Initialize analyzer with CNF file."""
        self.filepath = filepath
        self.num_vars: Optional[int] = None
        self.num_clauses: Optional[int] = None
        self.clauses: Optional[List[List[int]]] = None
        self.structure: Optional[CNFStructure] = None
        self.partition: Optional[PartitionMetrics] = None
    
    def parse(self) -> None:
        """Parse CNF file."""
        print(f"Parsing CNF: {self.filepath}")
        self.num_vars, self.num_clauses, self.clauses = DIMACSParser.parse(self.filepath)
        print(f"  Variables: {self.num_vars}")
        print(f"  Clauses: {self.num_clauses}")
    
    def analyze_structure(self) -> None:
        """Analyze CNF structure."""
        print("\nAnalyzing structure...")
        
        if self.clauses is None:
            raise RuntimeError("Must call parse() first")
        
        # Build interaction graph
        edges = VariableInteractionGraph.build(self.num_vars, self.clauses)
        density = VariableInteractionGraph.compute_density(self.num_vars, edges)
        
        # Compute statistics
        clause_sizes = [len(c) for c in self.clauses]
        avg_size = sum(clause_sizes) / len(clause_sizes) if clause_sizes else 0
        
        self.structure = CNFStructure(
            num_variables=self.num_vars,
            num_clauses=self.num_clauses,
            clause_sizes=clause_sizes,
            avg_clause_size=avg_size,
            variable_interactions=edges
        )
        
        print(f"  Interaction edges: {len(edges)}")
        print(f"  Interaction density: {density:.3f}")
        print(f"  Avg clause size: {avg_size:.1f}")
    
    def discover_partitions(self) -> None:
        """Discover partition structure."""
        print("\nDiscovering partitions...")
        
        if self.structure is None:
            raise RuntimeError("Must call analyze_structure() first")
        
        self.partition = PartitionDiscovery.discover(
            self.structure.num_variables,
            self.structure.variable_interactions
        )
        
        print(f"  Modules found: {self.partition.num_modules}")
        print(f"  μ-discovery: {self.partition.mu_discovery:.2f} bits")
        print(f"  μ-operational: {self.partition.mu_operational:.2f} bits")
        print(f"  μ-total: {self.partition.mu_total:.2f} bits")
    
    def report(self, output_path: Optional[Path] = None) -> Dict:
        """
        Generate analysis report.
        
        Args:
            output_path: Optional path to write JSON report
            
        Returns:
            Report dictionary
        """
        if self.structure is None or self.partition is None:
            raise RuntimeError("Must run full analysis first")
        
        report = {
            "input_file": str(self.filepath),
            "structure": asdict(self.structure),
            "partition": asdict(self.partition),
            "summary": {
                "variables": self.num_vars,
                "clauses": self.num_clauses,
                "modules": self.partition.num_modules,
                "interaction_density": self.partition.interaction_density,
                "mu_total": self.partition.mu_total
            }
        }
        
        if output_path:
            print(f"\nWriting report to: {output_path}")
            with open(output_path, 'w') as f:
                json.dump(report, f, indent=2)
        
        return report


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Analyze CNF formulas and discover partition structure",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    # Basic analysis
    python tools/cnf_analyzer.py examples/tseitin_unsat.cnf
    
    # Save results to JSON
    python tools/cnf_analyzer.py input.cnf --output results.json
    
    # TODO B1.1: Add visualization option
    # python tools/cnf_analyzer.py input.cnf --visualize
    
References:
    - RESEARCH_PROGRAM_MASTER_PLAN.md (Task B1.1)
    - docs/MODEL_SPEC.md (μ-cost formulas)
    - thielecpu/discovery.py (Discovery implementation)
        """
    )
    
    parser.add_argument('input', type=Path, help='CNF file in DIMACS format')
    parser.add_argument('--output', '-o', type=Path, help='Output JSON file')
    parser.add_argument('--visualize', '-v', action='store_true', 
                       help='Visualize interaction graph (TODO B1.1)')
    
    args = parser.parse_args()
    
    # Validate input
    if not args.input.exists():
        print(f"Error: File not found: {args.input}", file=sys.stderr)
        return 1
    
    try:
        # Run analysis pipeline
        analyzer = CNFAnalyzer(args.input)
        analyzer.parse()
        analyzer.analyze_structure()
        analyzer.discover_partitions()
        report = analyzer.report(args.output)
        
        # Print summary
        print("\n" + "="*60)
        print("ANALYSIS COMPLETE")
        print("="*60)
        print(f"Variables: {report['summary']['variables']}")
        print(f"Clauses: {report['summary']['clauses']}")
        print(f"Modules: {report['summary']['modules']}")
        print(f"Density: {report['summary']['interaction_density']:.3f}")
        print(f"μ-total: {report['summary']['mu_total']:.2f} bits")
        print("="*60)
        
        if args.visualize:
            print("\nVisualization: TODO B1.1")
            print("  - Implement graph visualization")
            print("  - Show modules as colored clusters")
            print("  - Display μ-costs")
        
        return 0
        
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
