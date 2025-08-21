# find_best_paradox.py
# This is not a linter. It is a strategic analysis instrument.
# It ingests a raw paradox report and identifies the single, highest-leverage
# target for a strategic attack.

import ast
import sys
import os

# --- The Strategic Scoring Heuristic ---
# We are not looking for the most complex bug. We are looking for the most
# elegant, embarrassing, and undeniable one. The score is a proxy for this.
SCORING_WEIGHTS = {
    'verdict': {
        'IMPLEMENTATION_FAILURE': 500, # A direct conflict between promise and reality.
        'CONTRACT_VIOLATION': 400,   # A subtle failure to meet the contract.
        'VACUOUS': 100,              # Interesting, but harder to explain.
    },
    'simplicity': 1000, # We heavily reward short, simple functions.
    'impact': {         # Keywords that indicate a high-value target.
        'assert': 300, 'error': 200, 'verify': 200, 'core': 150,
        'truth': 250, 'rewrite': 250, 'check': 150, 'test': 100,
    }
}

def get_function_loc(file_path, function_name):
    """Finds a function in a file and returns its start/end line numbers."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            source = f.read()
        tree = ast.parse(source)
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef) and node.name == function_name:
                return (node.lineno, node.end_lineno)
    except Exception:
        return None, None
    return None, None

def calculate_score(paradox):
    """Applies the heuristic to a single discovered paradox."""
    score = 0
    
    # 1. Score by Verdict Clarity
    score += SCORING_WEIGHTS['verdict'].get(paradox['verdict'], 0)
    
    # 2. Score by Simplicity (inversely proportional to function length)
    start_line, end_line = get_function_loc(paradox['file'], paradox['function'])
    if start_line and end_line:
        line_count = end_line - start_line + 1
        if line_count > 0:
            score += SCORING_WEIGHTS['simplicity'] / line_count
        paradox['lines'] = line_count # Store for reporting
    
    # 3. Score by Impact (damning keywords in path or name)
    search_string = (paradox['file'] + paradox['function']).lower()
    for keyword, value in SCORING_WEIGHTS['impact'].items():
        if keyword in search_string:
            score += value
            
    paradox['score'] = score
    return score

def find_best_paradox(report_path):
    """Parses the report file and returns the highest-scoring paradox."""
    if not os.path.exists(report_path):
        print(f"Error: Report file not found at '{report_path}'")
        print("Please run the hunter first: python3 find_paradox.py ../pytest > pytest_paradox_report.txt")
        return None

    with open(report_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    paradoxes = []
    current_paradox = None
    for line in lines:
        line = line.strip()
        if line.startswith("--- PARADOX DISCOVERED ---"):
            if current_paradox:
                paradoxes.append(current_paradox)
            current_paradox = {}
        elif current_paradox is not None:
            if line.startswith("FILE:"):
                current_paradox['file'] = line.split(":", 1)[1].strip()
            elif line.startswith("FUNCTION:"):
                current_paradox['function'] = line.split(":", 1)[1].strip()
            elif line.startswith("VERDICT:"):
                current_paradox['verdict'] = line.split(":", 1)[1].strip()
            elif line.startswith("EVIDENCE:"):
                current_paradox['evidence'] = line.split(":", 1)[1].strip()
            elif line.startswith("--- END REPORT ---"):
                if current_paradox:
                    paradoxes.append(current_paradox)
                current_paradox = None
            elif current_paradox.get('evidence'): # Append multi-line evidence
                current_paradox['evidence'] += "\n" + line
    
    if not paradoxes:
        return None
        
    best_paradox = max(paradoxes, key=calculate_score)
    return best_paradox

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 find_best_paradox.py <path_to_paradox_report.txt>")
        sys.exit(1)

    report_file = sys.argv[1]
    
    print(f"Analyzing report file: {report_file}...")
    
    best_target = find_best_paradox(report_file)
    
    if best_target:
        print("\n--- PRIME TARGET IDENTIFIED ---")
        print(f"\nSCORE: {best_target.get('score', 'N/A'):.2f}")
        print(f"FILE: {best_target.get('file', 'N/A')}")
        print(f"FUNCTION: {best_target.get('function', 'N/A')}")
        print(f"FUNCTION LENGTH: {best_target.get('lines', 'N/A')} lines")
        print(f"VERDICT: {best_target.get('verdict', 'N/A')}")
        print(f"EVIDENCE:\n{best_target.get('evidence', 'N/A')}")
        print("\n--- MISSION DIRECTIVE ---")
        print("This is your target. This is your proof.")
        print("Craft the Pull Request. Use this evidence.")
        print("The war begins now.")
    else:
        print("\n--- ANALYSIS COMPLETE ---")
        print("No paradoxes found in the provided report.")