#!/usr/bin/env python3
"""
The Critic: The Engine of Introspection

This tool analyzes the machine's evolutionary history (ascension ledger)
to discover hidden biases, find what went wrong, and detect stagnation.

It implements:
- Value Discovery: Which primitives appear most in high-fitness strategies?
- Bias Detection: Are there evolutionary dead-ends?
- Stagnation Analysis: Is the rate of improvement slowing down?
"""

import json
import numpy as np
from pathlib import Path
from typing import Dict, List, Any, Tuple
from collections import Counter, defaultdict


def load_ascension_ledger(ledger_path: Path) -> List[Dict[str, Any]]:
    """Load the ascension ledger from disk."""
    try:
        with open(ledger_path, 'r') as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return []


def analyze_value_discovery(ledger: List[Dict[str, Any]], top_n: int = 5) -> Dict[str, Any]:
    """
    Discover which primitives the machine values most.
    
    This finds primitives that appear most often in high-fitness strategies.
    
    Args:
        ledger: The ascension ledger
        top_n: Number of top primitives to identify
    
    Returns:
        Dictionary with value discovery insights
    """
    if not ledger:
        return {"primitives": [], "insight": "No data available"}
    
    # Get fitness threshold (top 25% of strategies)
    fitnesses = [entry['fitness_score'] for entry in ledger]
    fitness_threshold = np.percentile(fitnesses, 75) if fitnesses else 0.0
    
    # Count primitive occurrences in high-fitness strategies
    primitive_counter = Counter()
    high_fitness_count = 0
    
    for entry in ledger:
        if entry['fitness_score'] >= fitness_threshold:
            high_fitness_count += 1
            # Extract primitive names from DNA sequence
            for step in entry.get('strategy_dna', []):
                # Simple heuristic: look for uppercase words (primitive names)
                words = step.split()
                for word in words:
                    # Check if it looks like a primitive (all caps or starts with prim_)
                    if word.isupper() or word.startswith('prim_'):
                        primitive_counter[word] += 1
    
    # Get top primitives
    top_primitives = primitive_counter.most_common(top_n)
    
    insight = f"Analyzed {len(ledger)} strategies. "
    insight += f"Top {top_n} primitives in high-fitness strategies (fitness >= {fitness_threshold:.3f}):"
    
    return {
        "primitives": [
            {"name": name, "frequency": count}
            for name, count in top_primitives
        ],
        "high_fitness_threshold": fitness_threshold,
        "high_fitness_count": high_fitness_count,
        "insight": insight
    }


def analyze_bias_detection(ledger: List[Dict[str, Any]]) -> Dict[str, Any]:
    """
    Detect evolutionary dead-ends and biases.
    
    This finds patterns where certain mutations consistently lead to lower fitness.
    
    Args:
        ledger: The ascension ledger
    
    Returns:
        Dictionary with bias detection insights
    """
    if len(ledger) < 2:
        return {"dead_ends": [], "insight": "Insufficient data for bias detection"}
    
    # Track fitness changes by mutation type
    mutation_effects = defaultdict(list)
    
    for entry in ledger:
        mutation_type = entry.get('metadata', {}).get('mutation_type')
        if mutation_type:
            fitness = entry['fitness_score']
            mutation_effects[mutation_type].append(fitness)
    
    # Identify dead-ends (mutations with consistently low fitness)
    dead_ends = []
    for mutation_type, fitnesses in mutation_effects.items():
        if len(fitnesses) >= 3:  # Need at least 3 samples
            avg_fitness = np.mean(fitnesses)
            overall_avg = np.mean([e['fitness_score'] for e in ledger])
            
            if avg_fitness < overall_avg * 0.7:  # 30% below average
                dead_ends.append({
                    "mutation_type": mutation_type,
                    "avg_fitness": avg_fitness,
                    "sample_count": len(fitnesses)
                })
    
    # Track parent-child fitness changes
    parent_child_changes = []
    for entry in ledger:
        parents = entry.get('parent_strategies', [])
        if parents:
            # Find parent entries
            for parent_name in parents:
                parent_entries = [e for e in ledger if e['strategy_name'] == parent_name]
                if parent_entries:
                    parent_fitness = parent_entries[0]['fitness_score']
                    child_fitness = entry['fitness_score']
                    change = child_fitness - parent_fitness
                    parent_child_changes.append(change)
    
    insight = f"Analyzed {len(ledger)} strategies. "
    if dead_ends:
        insight += f"Found {len(dead_ends)} potential dead-end mutation types. "
    else:
        insight += "No significant dead-ends detected. "
    
    if parent_child_changes:
        avg_change = np.mean(parent_child_changes)
        insight += f"Average parent-child fitness change: {avg_change:+.4f}"
    
    return {
        "dead_ends": dead_ends,
        "avg_parent_child_change": np.mean(parent_child_changes) if parent_child_changes else 0.0,
        "insight": insight
    }


def analyze_stagnation(ledger: List[Dict[str, Any]], window_size: int = 10) -> Dict[str, Any]:
    """
    Detect if evolution is stagnating.
    
    This analyzes the rate of improvement over time.
    
    Args:
        ledger: The ascension ledger
        window_size: Number of recent entries to consider
    
    Returns:
        Dictionary with stagnation analysis
    """
    if len(ledger) < window_size:
        return {
            "stagnation_detected": False,
            "improvement_rate": 0.0,
            "insight": "Insufficient data for stagnation analysis"
        }
    
    # Get recent entries
    recent_ledger = ledger[-window_size:]
    
    # Calculate fitness trend
    fitnesses = [entry['fitness_score'] for entry in recent_ledger]
    
    # Simple linear regression to find slope
    x = np.arange(len(fitnesses))
    slope, intercept = np.polyfit(x, fitnesses, 1)
    
    # Calculate variance in recent fitness
    fitness_variance = np.var(fitnesses)
    
    # Stagnation criteria:
    # 1. Slope is near zero or negative
    # 2. Variance is very low
    stagnation_detected = (slope < 0.001) and (fitness_variance < 0.0001)
    
    # Get max fitness over time
    all_fitnesses = [entry['fitness_score'] for entry in ledger]
    max_fitness = max(all_fitnesses) if all_fitnesses else 0.0
    recent_max = max(fitnesses) if fitnesses else 0.0
    
    # Check if we're stuck at a local maximum
    at_local_max = (abs(recent_max - max_fitness) < 0.01)
    
    insight = f"Analyzed last {window_size} strategies. "
    insight += f"Improvement rate (slope): {slope:.6f}. "
    insight += f"Fitness variance: {fitness_variance:.6f}. "
    
    if stagnation_detected:
        insight += "STAGNATION DETECTED - recommend introducing new objective term."
    elif at_local_max:
        insight += "Near local maximum - evolution may benefit from new objective."
    else:
        insight += "Evolution progressing normally."
    
    # Recommendation
    recommended_action = None
    if stagnation_detected or at_local_max:
        recommended_action = {
            "action": "introduce_new_metric",
            "suggested_metric": "elegance",
            "reason": "Low improvement rate suggests current objective may be saturated"
        }
    
    return {
        "stagnation_detected": bool(stagnation_detected),
        "improvement_rate": float(slope),
        "fitness_variance": float(fitness_variance),
        "at_local_max": bool(at_local_max),
        "max_fitness": float(max_fitness),
        "recent_max_fitness": float(recent_max),
        "recommended_action": recommended_action,
        "insight": insight
    }


def run_critic_analysis(ledger_path: Path) -> Dict[str, Any]:
    """
    Run complete critic analysis on the ascension ledger.
    
    Args:
        ledger_path: Path to the ascension ledger
    
    Returns:
        Complete analysis report with recommendations
    """
    print("=" * 70)
    print("THE CRITIC: ENGINE OF INTROSPECTION")
    print("=" * 70)
    print()
    
    # Load ledger
    ledger = load_ascension_ledger(ledger_path)
    
    if not ledger:
        print("No ascension ledger found. The Critic has nothing to analyze.")
        return {
            "status": "no_data",
            "value_discovery": {},
            "bias_detection": {},
            "stagnation_analysis": {}
        }
    
    print(f"Loaded {len(ledger)} evolutionary records from the ascension ledger.")
    print()
    
    # Run analyses
    print("1. VALUE DISCOVERY - What does the machine value?")
    print("-" * 70)
    value_analysis = analyze_value_discovery(ledger)
    print(value_analysis['insight'])
    for prim in value_analysis['primitives']:
        print(f"  - {prim['name']}: {prim['frequency']} occurrences")
    print()
    
    print("2. BIAS DETECTION - Finding what went wrong")
    print("-" * 70)
    bias_analysis = analyze_bias_detection(ledger)
    print(bias_analysis['insight'])
    for dead_end in bias_analysis['dead_ends']:
        print(f"  - {dead_end['mutation_type']}: avg fitness {dead_end['avg_fitness']:.4f}")
    print()
    
    print("3. STAGNATION ANALYSIS - Is evolution slowing down?")
    print("-" * 70)
    stagnation_analysis = analyze_stagnation(ledger)
    print(stagnation_analysis['insight'])
    if stagnation_analysis.get('recommended_action'):
        action = stagnation_analysis['recommended_action']
        print(f"  Recommendation: {action['action']}")
        print(f"  Suggested metric: {action['suggested_metric']}")
        print(f"  Reason: {action['reason']}")
    print()
    
    print("=" * 70)
    print("CRITIC ANALYSIS COMPLETE")
    print("=" * 70)
    
    # Return structured report
    return {
        "status": "complete",
        "ledger_size": len(ledger),
        "value_discovery": value_analysis,
        "bias_detection": bias_analysis,
        "stagnation_analysis": stagnation_analysis
    }


def main():
    """Main entry point for the critic."""
    ledger_path = Path(__file__).parent.parent / "ascension_ledger.json"
    
    # Run analysis
    report = run_critic_analysis(ledger_path)
    
    # Save report
    report_path = Path(__file__).parent.parent / "critic_report.json"
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2)
    
    print()
    print(f"Full report saved to: {report_path}")


if __name__ == "__main__":
    main()
