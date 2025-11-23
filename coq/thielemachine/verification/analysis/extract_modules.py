#!/usr/bin/env python3
"""
Script to extract modules from ThieleUniversalBridge.v
Breaks the large proof file into logical, manageable modules
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple, Dict

class CoqModule:
    def __init__(self, name: str, start_line: int, end_line: int, content: str):
        self.name = name
        self.start_line = start_line
        self.end_line = end_line
        self.content = content
        self.dependencies = []
        
    def __repr__(self):
        return f"CoqModule({self.name}, lines {self.start_line}-{self.end_line})"

def parse_bridge_file(filepath: Path) -> Tuple[List[str], List[CoqModule]]:
    """Parse the ThieleUniversalBridge.v file and identify logical sections"""
    
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    modules = []
    
    # Define section boundaries based on comments and logical structure
    sections = [
        # (start_pattern, end_pattern, module_name, description)
        (1, 50, "BridgeHeader", "File header and documentation"),
        (51, 200, "BridgeCore", "Core definitions: run1, run_n, state_eqb"),
        (201, 350, "ProgramEncoding", "Program encoding and padding helpers"),
        (351, 530, "SetupState", "Setup state and tape window definitions"),
        (531, 700, "Invariants", "Core invariants and helper lemmas"),
        (701, 900, "BasicLemmas", "Basic helper lemmas (nth, firstn, skipn)"),
        (901, 920, "LengthPreservation", "CRITICAL: length_run_n_eq_bounded lemma"),
        (921, 1200, "RegisterLemmas", "Register tracking infrastructure"),
        (1201, 1400, "StepLemmas", "Individual instruction step lemmas"),
        (1401, 1650, "TransitionFetch", "Fetch to FindRule transition"),
        (1651, 1950, "TransitionFindRuleNext", "FindRule loop - non-match case"),
        (1951, 2100, "LoopIterationNoMatch", "Loop iteration when no match"),
        (2101, 2300, "LoopExitMatch", "Loop exit when match found"),
        (2301, 2876, "MainTheorem", "Main transition theorem"),
    ]
    
    for start, end, name, desc in sections:
        # Adjust for 0-indexed lists
        start_idx = start - 1
        end_idx = min(end, len(lines))
        
        content = ''.join(lines[start_idx:end_idx])
        # Use the original end line number (not end_idx) in the module
        modules.append(CoqModule(name, start, end, content))
    
    return lines, modules

def count_proofs(content: str) -> Dict[str, int]:
    """Count different types of proof constructs"""
    stats = {
        'definitions': len(re.findall(r'^Definition|^Fixpoint', content, re.MULTILINE)),
        'lemmas': len(re.findall(r'^Lemma|^Time Lemma', content, re.MULTILINE)),
        'theorems': len(re.findall(r'^Theorem|^Time Theorem', content, re.MULTILINE)),
        'admitted': len(re.findall(r'Admitted\.', content)),
        'qed': len(re.findall(r'Qed\.', content)),
        'todo': len(re.findall(r'TODO|admit\.', content, re.IGNORECASE)),
    }
    return stats

def analyze_dependencies(module: CoqModule, all_modules: List[CoqModule]) -> List[str]:
    """Analyze what other modules this one depends on"""
    deps = []
    
    # Look for references to definitions from other modules
    for other in all_modules:
        if other.name != module.name:
            # Simple heuristic: check if other module's name appears in requires
            if other.name.lower() in module.content.lower():
                deps.append(other.name)
    
    return deps

def generate_module_file(module: CoqModule, base_imports: List[str], output_dir: Path):
    """Generate a standalone .v file for a module"""
    
    filename = output_dir / f"Bridge_{module.name}.v"
    
    with open(filename, 'w') as f:
        # Write header
        f.write(f"(* ================================================================= *)\n")
        f.write(f"(* ThieleUniversalBridge Module: {module.name} *)\n")
        f.write(f"(* Extracted from lines {module.start_line}-{module.end_line} *)\n")
        f.write(f"(* NOTE: This is a standalone extraction for analysis purposes. *)\n")
        f.write(f"(*       It may not compile independently due to dependencies. *)\n")
        f.write(f"(*       Use the original ThieleUniversalBridge.v for actual compilation. *)\n")
        f.write(f"(* ================================================================= *)\n\n")
        
        # Write imports
        for imp in base_imports:
            f.write(f"{imp}\n")
        
        f.write("\n")
        
        # Note dependencies but don't import them (to avoid circularity)
        if module.dependencies:
            f.write(f"(* Dependencies noted for reference: {', '.join(module.dependencies)} *)\n")
            f.write(f"(* These are NOT imported to keep modules standalone for analysis *)\n\n")
        
        # Write content
        f.write(module.content)
        
        # Ensure it ends properly
        if not module.content.endswith('\n'):
            f.write('\n')
    
    print(f"Generated: {filename}")

def main():
    """Main extraction logic"""
    
    # Paths
    script_dir = Path(__file__).parent
    verification_dir = script_dir.parent
    bridge_file = verification_dir / "ThieleUniversalBridge.v"
    output_dir = verification_dir / "modular"
    
    print("=== ThieleUniversalBridge Module Extraction ===")
    print(f"Source: {bridge_file}")
    print(f"Output: {output_dir}")
    print()
    
    if not bridge_file.exists():
        print(f"Error: Bridge file not found: {bridge_file}")
        return 1
    
    output_dir.mkdir(exist_ok=True)
    
    # Parse the file
    print("Parsing bridge file...")
    lines, modules = parse_bridge_file(bridge_file)
    print(f"Identified {len(modules)} modules")
    print()
    
    # Base imports that all modules need
    base_imports = [
        "From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.",
        "From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.",
        "Import ListNotations.",
        "Local Open Scope nat_scope.",
        "Local Notation length := List.length.",
    ]
    
    # Analyze each module
    print("=== Module Analysis ===")
    for module in modules:
        stats = count_proofs(module.content)
        deps = analyze_dependencies(module, modules)
        module.dependencies = deps
        
        print(f"\n{module.name} (lines {module.start_line}-{module.end_line}):")
        print(f"  Size: {len(module.content)} chars, {module.end_line - module.start_line + 1} lines")
        print(f"  Definitions: {stats['definitions']}")
        print(f"  Lemmas: {stats['lemmas']}")
        print(f"  Theorems: {stats['theorems']}")
        print(f"  Completed (Qed): {stats['qed']}")
        print(f"  Admitted: {stats['admitted']}")
        print(f"  TODOs: {stats['todo']}")
        if stats['admitted'] > 0 or stats['todo'] > 0:
            print(f"  ⚠ ATTENTION NEEDED")
    
    print("\n=== Generating Module Files ===")
    for module in modules:
        generate_module_file(module, base_imports, output_dir)
    
    # Generate a master index file
    index_file = output_dir / "README.md"
    with open(index_file, 'w') as f:
        f.write("# ThieleUniversalBridge Modular Breakdown\n\n")
        f.write("This directory contains the modularized version of ThieleUniversalBridge.v\n\n")
        f.write("## Modules\n\n")
        
        for module in modules:
            stats = count_proofs(module.content)
            f.write(f"### {module.name}\n")
            f.write(f"- **File**: `Bridge_{module.name}.v`\n")
            f.write(f"- **Original lines**: {module.start_line}-{module.end_line}\n")
            f.write(f"- **Stats**: {stats['definitions']} defs, {stats['lemmas']} lemmas, ")
            f.write(f"{stats['qed']} completed, {stats['admitted']} admitted\n")
            if stats['admitted'] > 0:
                f.write(f"- ⚠ **Status**: Needs work ({stats['admitted']} admitted proofs)\n")
            else:
                f.write(f"- ✓ **Status**: Complete\n")
            f.write("\n")
        
        f.write("## Compilation Order\n\n")
        f.write("Modules should be compiled in this order (respecting dependencies):\n\n")
        for i, module in enumerate(modules, 1):
            f.write(f"{i}. {module.name}\n")
    
    print(f"\nGenerated index: {index_file}")
    print("\n=== Extraction Complete ===")
    return 0

if __name__ == "__main__":
    sys.exit(main())
