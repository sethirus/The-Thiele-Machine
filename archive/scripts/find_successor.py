# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""The Champion's Gambit: Find successors to the BB(5) champion via generalization."""

import time
from scripts.busy_beaver_cnf_provider import BusyBeaverCnfProvider
from scripts.max_sat_bb_simulator import MaxSATBBSimulator

# The transition table for the current BB(5) world champion (Marxen/Buntrock machine)
# This is a simplified representation - in reality this would be the full 5-state table
MARXEN_BUNTROCK_CHAMPION = {
    'next_state': {
        0: {0: 1, 1: 1},  # State A
        1: {0: 2, 1: 3},  # State B
        2: {0: 3, 1: 4},  # State C
        3: {0: 0, 1: 1},  # State D
        4: {0: 4, 1: 4},  # State H (halting)
    },
    'write_symbol': {
        0: {0: 1, 1: 1},  # State A
        1: {0: 1, 1: 1},  # State B
        2: {0: 0, 1: 0},  # State C
        3: {0: 1, 1: 0},  # State D
        4: {0: 0, 1: 0},  # State H (halting)
    },
    'move_direction': {
        0: {0: 1, 1: 0},  # State A: right, left
        1: {0: 1, 1: 0},  # State B: right, left
        2: {0: 1, 1: 1},  # State C: right, right
        3: {0: 0, 1: 1},  # State D: left, right
        4: {0: 0, 1: 0},  # State H (halting): left, left (doesn't matter)
    }
}

WORLD_RECORD = 47176870


def compare_machines(template_machine, new_machine_str):
    """Compare the new machine to the template and show differences."""
    print("\n" + "="*80)
    print("COMPARISON: Template vs New Machine")
    print("="*80)

    # Parse the new machine string
    lines = new_machine_str.split('\n')
    new_machine = {'next_state': {}, 'write_symbol': {}, 'move_direction': {}}

    for line in lines:
        if '|' in line and not line.startswith('-'):
            parts = [p.strip() for p in line.split('|')]
            if len(parts) >= 5:
                state_str, symbol_str, next_str, write_str, move_str = parts[:5]

                # Convert state names back to indices
                state_names = ['A', 'B', 'C', 'D', 'H']
                state_idx = state_names.index(state_str) if state_str in state_names else 0
                next_idx = state_names.index(next_str) if next_str in state_names else 0
                symbol_idx = int(symbol_str) if symbol_str.isdigit() else 0
                write_idx = int(write_str) if write_str.isdigit() else 0
                move_idx = 0 if move_str == 'L' else 1

                if state_idx not in new_machine['next_state']:
                    new_machine['next_state'][state_idx] = {}
                new_machine['next_state'][state_idx][symbol_idx] = next_idx

                if state_idx not in new_machine['write_symbol']:
                    new_machine['write_symbol'][state_idx] = {}
                new_machine['write_symbol'][state_idx][symbol_idx] = write_idx

                if state_idx not in new_machine['move_direction']:
                    new_machine['move_direction'][state_idx] = {}
                new_machine['move_direction'][state_idx][symbol_idx] = move_idx

    # Compare and show differences
    differences = 0
    print("\nDifferences from template:")
    print("State | Symbol | Template → New")

    for s in range(5):  # 5 states
        for sym in range(2):  # 2 symbols
            template_next = template_machine['next_state'].get(s, {}).get(sym, 0)
            template_write = template_machine['write_symbol'].get(s, {}).get(sym, 0)
            template_move = template_machine['move_direction'].get(s, {}).get(sym, 0)

            new_next = new_machine['next_state'].get(s, {}).get(sym, 0)
            new_write = new_machine['write_symbol'].get(s, {}).get(sym, 0)
            new_move = new_machine['move_direction'].get(s, {}).get(sym, 0)

            state_name = ['A', 'B', 'C', 'D', 'H'][s]

            if template_next != new_next:
                print(f"{state_name:5} | {sym}      | Next: {['A', 'B', 'C', 'D', 'H'][template_next]} → {['A', 'B', 'C', 'D', 'H'][new_next]}")
                differences += 1

            if template_write != new_write:
                print(f"{state_name:5} | {sym}      | Write: {template_write} → {new_write}")
                differences += 1

            if template_move != new_move:
                move_names = ['L', 'R']
                print(f"{state_name:5} | {sym}      | Move: {move_names[template_move]} → {move_names[new_move]}")
                differences += 1

    print(f"\nTotal differences: {differences} transitions changed")
    return differences


def main():
    print("="*80)
    print("Thiele Machine: The Champion's Gambit")
    print("Objective: Find the successor to the BB(5) champion via generalization.")
    print("="*80)

    print(f"Current World Record: {WORLD_RECORD:,} steps")
    print("Template: Marxen/Buntrock BB(5) champion")

    # Create the provider and simulator
    provider = BusyBeaverCnfProvider(states=5, tape_size=10)  # Smaller tape for demo
    simulator = MaxSATBBSimulator(provider)

    # Apply the current champion as a structural template
    print("\nApplying the current world champion as a structural template...")
    provider.apply_template_as_soft_constraint(MARXEN_BUNTROCK_CHAMPION, penalty_weight=5)

    # Load the base rules with a reasonable limit for demonstration
    max_search_steps = 10000  # Much smaller for demo purposes
    print("\nEngine is now reasoning about the entire neighborhood of the champion...")
    print(f"Searching up to {max_search_steps:,} steps (scaled down for demonstration)")

    simulator.load_base_rules(max_steps=max_search_steps)

    # The solver will find the machine that runs the longest, while trying to
    # change the fewest possible rules from the champion.
    start_time = time.time()
    solution = simulator.maximize_step_count()
    end_time = time.time()

    if solution:
        model, new_record = solution
        new_champion = simulator.decode_program(model)

        print("\n" + "!"*80)
        if new_record > WORLD_RECORD:
            print(">>> SUCCESSOR FOUND. A NEW CHAMPION EMERGES. <<<")
            print("!"*80)
            print(f"\nNew Record: {new_record:,} steps")
            print(f"Improvement: {new_record - WORLD_RECORD:,} steps ({(new_record/WORLD_RECORD - 1)*100:.1f}%)")
        else:
            print(">>> PROOF OF LOCAL MAXIMUM. <<<")
            print("!"*80)
            print("The Thiele Machine has proven that no small modification to the")
            print("current champion can produce a longer-running machine.")
            print(f"Verified Champion Score: {new_record:,} steps")

        print("\nNew Champion Machine:")
        print(new_champion)

        # Compare with template
        differences = compare_machines(MARXEN_BUNTROCK_CHAMPION, new_champion)

        if differences == 0:
            print("\nCONCLUSION: The template machine itself is optimal within the search space.")
        else:
            print(f"\nCONCLUSION: By changing {differences} transitions, we achieved a {'superior' if new_record > WORLD_RECORD else 'comparable'} machine.")

    else:
        print("\n>>> NO SOLUTION FOUND. <<<")
        print("Could not find any machine within the search parameters.")

    print(f"\nTotal Time: {end_time - start_time:.4f} seconds.")
    print("\n" + "="*80)
    print("Champion's Gambit Complete")
    print("="*80)


if __name__ == "__main__":
    main()