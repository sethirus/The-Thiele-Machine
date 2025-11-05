#!/usr/bin/env python3
"""
The Synthesizer of Purpose: The Evolution of Purpose

This tool uses the Critic's insights to mutate the machine's own
objective genome, allowing it to define its own future.

It implements the highest-level engine that can write new objective genomes
based on evolutionary patterns discovered by the Critic.
"""

import json
from pathlib import Path
from typing import Dict, Any, Optional


def synthesize_new_objective(
    critic_report: Dict[str, Any],
    current_objective: Dict[str, Any],
    version: int = 2
) -> Dict[str, Any]:
    """
    Synthesize a new objective genome based on critic insights.
    
    Core principle: If evolution is stalling, introduce a new term into
    the objective function to break out of the local maximum.
    
    Args:
        critic_report: Report from the Critic
        current_objective: Current objective genome
        version: Version number for the new objective
    
    Returns:
        New objective genome
    """
    stagnation = critic_report.get('stagnation_analysis', {})
    
    # Check if we need to evolve the objective
    needs_evolution = stagnation.get('stagnation_detected', False)
    at_local_max = stagnation.get('at_local_max', False)
    
    if not needs_evolution and not at_local_max:
        print("Evolution progressing well - no objective change needed.")
        return current_objective
    
    # Get recommendation from critic
    recommendation = stagnation.get('recommended_action', {})
    suggested_metric = recommendation.get('suggested_metric', 'elegance')
    
    print(f"Stagnation detected. Synthesizing new objective with {suggested_metric} metric...")
    
    # Determine the current objective structure
    current_function = current_objective.get('function', '')
    
    # If current objective is already a weighted sum, add to it
    if current_function == 'weighted_sum':
        # Add new component to existing weighted sum
        new_objective = current_objective.copy()
        components = new_objective.get('parameters', {}).get('components', {}).copy()
        
        # Add elegance component if not present
        if suggested_metric not in components:
            components[suggested_metric] = {
                "weight": 0.1,
                "function": "evaluate_strategy_complexity",
                "parameters": {"method": "inverse_primitive_count"}
            }
            
            # Reweight existing components
            # Reduce all weights slightly to make room for new component
            for comp_name in components:
                if comp_name != suggested_metric:
                    components[comp_name]['weight'] *= 0.9
        
        new_objective['parameters']['components'] = components
        new_objective['name'] = f"Multi-Objective v{version}.0"
        
    else:
        # Convert simple objective to weighted sum
        new_objective = {
            "name": f"Accuracy + {suggested_metric.capitalize()} v{version}.0",
            "function": "weighted_sum",
            "parameters": {
                "components": {
                    "accuracy": {
                        "weight": 0.9,
                        "function": current_objective.get('function', 'evaluate_classification_accuracy'),
                        "parameters": current_objective.get('parameters', {})
                    },
                    suggested_metric: {
                        "weight": 0.1,
                        "function": "evaluate_strategy_complexity",
                        "parameters": {"method": "inverse_primitive_count"}
                    }
                }
            }
        }
    
    return new_objective


def run_purpose_synthesis(
    critic_report_path: Path,
    current_objective_path: Path,
    output_objective_path: Optional[Path] = None
) -> Dict[str, Any]:
    """
    Run the purpose synthesizer to create a new objective genome.
    
    Args:
        critic_report_path: Path to the critic's report
        current_objective_path: Path to current objective genome
        output_objective_path: Path to save new objective (defaults to current_objective.thiele)
    
    Returns:
        The new objective genome
    """
    print("=" * 70)
    print("THE SYNTHESIZER OF PURPOSE: THE EVOLUTION OF PURPOSE")
    print("=" * 70)
    print()
    
    # Load critic report
    try:
        with open(critic_report_path, 'r') as f:
            critic_report = json.load(f)
    except FileNotFoundError:
        print("ERROR: Critic report not found. Run the Critic first.")
        return None
    
    # Load current objective
    try:
        with open(current_objective_path, 'r') as f:
            current_objective = json.load(f)
    except FileNotFoundError:
        print("ERROR: Current objective not found.")
        return None
    
    print("Current Objective:")
    print(f"  Name: {current_objective.get('name', 'Unknown')}")
    print(f"  Function: {current_objective.get('function', 'Unknown')}")
    print()
    
    # Analyze critic report
    stagnation = critic_report.get('stagnation_analysis', {})
    print("Critic Analysis:")
    print(f"  Stagnation Detected: {stagnation.get('stagnation_detected', False)}")
    print(f"  Improvement Rate: {stagnation.get('improvement_rate', 0.0):.6f}")
    print(f"  At Local Maximum: {stagnation.get('at_local_max', False)}")
    print()
    
    # Determine version number
    current_name = current_objective.get('name', '')
    if 'v' in current_name:
        try:
            version_str = current_name.split('v')[1].split('.')[0]
            version = int(version_str) + 1
        except:
            version = 2
    else:
        version = 2
    
    # Synthesize new objective
    print("Synthesizing new objective...")
    new_objective = synthesize_new_objective(critic_report, current_objective, version)
    
    if new_objective == current_objective:
        print("No changes needed to objective.")
        return current_objective
    
    print()
    print("New Objective:")
    print(f"  Name: {new_objective.get('name', 'Unknown')}")
    print(f"  Function: {new_objective.get('function', 'Unknown')}")
    
    if new_objective.get('function') == 'weighted_sum':
        components = new_objective.get('parameters', {}).get('components', {})
        print("  Components:")
        for comp_name, comp_config in components.items():
            weight = comp_config.get('weight', 0.0)
            print(f"    - {comp_name}: weight={weight:.2f}, function={comp_config.get('function', 'unknown')}")
    
    print()
    
    # Save new objective
    if output_objective_path is None:
        output_objective_path = current_objective_path
    
    with open(output_objective_path, 'w') as f:
        json.dump(new_objective, f, indent=2)
    
    print(f"New objective saved to: {output_objective_path}")
    print()
    print("=" * 70)
    print("PURPOSE SYNTHESIS COMPLETE")
    print("=" * 70)
    
    return new_objective


def main():
    """Main entry point for the purpose synthesizer."""
    base_dir = Path(__file__).parent.parent
    
    critic_report_path = base_dir / "critic_report.json"
    current_objective_path = base_dir / "objectives" / "current_objective.thiele"
    
    # Run synthesis
    new_objective = run_purpose_synthesis(
        critic_report_path,
        current_objective_path
    )
    
    if new_objective:
        print()
        print("The machine has redefined its own purpose.")
        print("The next evolutionary cycle will pursue this new objective.")


if __name__ == "__main__":
    main()
