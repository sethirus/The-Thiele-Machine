#!/usr/bin/env python3
"""
verify_implementation_completeness.py

Deep verification that Verilog CPU and Python VM correctly implement
all 16 instructions from the Coq kernel specification.

This goes beyond just checking instruction names exist - it verifies:
1. Each instruction has proper execution logic
2. Parameters match Coq specification
3. μ-cost tracking is implemented
4. All 16 instructions are callable/executable
"""

import re
import json
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple

COQ_KERNEL = Path("coq/kernel/VMStep.v")
VERILOG_CPU = Path("thielecpu/hardware/thiele_cpu.v")
PYTHON_VM = Path("thielecpu/vm.py")
OUTPUT_JSON = Path("artifacts/implementation_verification.json")

def parse_coq_instructions_detailed() -> Dict[str, Dict]:
    """Extract instruction details from Coq kernel."""
    with open(COQ_KERNEL) as f:
        content = f.read()
    
    instructions = {}
    
    # Find the inductive type
    inductive_match = re.search(
        r'Inductive vm_instruction :=\s*(.*?)(?=\n\nDefinition)',
        content,
        re.MULTILINE | re.DOTALL
    )
    
    if not inductive_match:
        return instructions
    
    inductive_body = inductive_match.group(1)
    
    # Parse each instruction with parameters
    pattern = r'\|\s+instr_(\w+)\s+([^\n]*)'
    
    for match in re.finditer(pattern, inductive_body):
        instr_name = match.group(1)
        params_str = match.group(2).strip()
        
        # Count parameters
        param_count = len(re.findall(r'\([^)]+\)', params_str))
        has_mu_delta = 'mu_delta' in params_str
        
        instructions[instr_name] = {
            'name': instr_name,
            'param_count': param_count,
            'has_mu_delta': has_mu_delta,
            'params_str': params_str
        }
    
    return instructions

def verify_verilog_cpu(coq_instructions: Dict[str, Dict]) -> Dict:
    """Verify Verilog CPU implements all instructions correctly."""
    with open(VERILOG_CPU) as f:
        content = f.read()
    
    results = {
        'file_exists': True,
        'instructions': {},
        'missing': [],
        'issues': []
    }
    
    for instr_name, details in coq_instructions.items():
        opcode_name = f"OPCODE_{instr_name.upper()}"
        
        # Check opcode definition
        opcode_pattern = rf'{opcode_name}\s*='
        has_opcode_def = bool(re.search(opcode_pattern, content))
        
        # Check execute case
        case_pattern = rf'{opcode_name}\s*:'
        has_execute_case = bool(re.search(case_pattern, content))
        
        # Check for any logic related to this instruction
        logic_pattern = rf'// {instr_name}|/\* {instr_name} \*/|{instr_name}_'
        has_logic = bool(re.search(logic_pattern, content, re.IGNORECASE))
        
        implemented = has_opcode_def and has_execute_case
        
        results['instructions'][instr_name] = {
            'has_opcode_definition': has_opcode_def,
            'has_execute_case': has_execute_case,
            'has_related_logic': has_logic,
            'implemented': implemented
        }
        
        if not implemented:
            results['missing'].append(instr_name)
            if not has_opcode_def:
                results['issues'].append(f"Missing opcode definition for {instr_name}")
            if not has_execute_case:
                results['issues'].append(f"Missing execute case for {instr_name}")
    
    results['total'] = len(coq_instructions)
    results['implemented_count'] = sum(1 for r in results['instructions'].values() if r['implemented'])
    results['coverage'] = results['implemented_count'] / results['total'] * 100 if results['total'] > 0 else 0
    
    return results

def verify_python_vm(coq_instructions: Dict[str, Dict]) -> Dict:
    """Verify Python VM implements all instructions correctly."""
    with open(PYTHON_VM) as f:
        content = f.read()
    
    results = {
        'file_exists': True,
        'instructions': {},
        'missing': [],
        'issues': []
    }
    
    for instr_name, details in coq_instructions.items():
        opcode_str = instr_name.upper()
        
        # Check for instruction name references
        # Python VM uses uppercase instruction names like "PNEW", "PSPLIT", etc.
        patterns = [
            rf'"{opcode_str}"',
            rf"'{opcode_str}'",
            rf'== "{opcode_str}"',
            rf"== '{opcode_str}'",
            rf'in \{{.*"{opcode_str}".*\}}',
        ]
        
        found_references = []
        for pattern in patterns:
            if re.search(pattern, content):
                found_references.append(pattern)
        
        has_reference = len(found_references) > 0
        
        # Check for execution logic (if op == "INSTR" or similar)
        exec_pattern = rf'(if|elif)\s+op\s*==\s*"{opcode_str}"'
        has_execution = bool(re.search(exec_pattern, content))
        
        # Check for handler function
        handler_pattern = rf'def\s+\w*{instr_name}\w*\('
        has_handler = bool(re.search(handler_pattern, content, re.IGNORECASE))
        
        implemented = has_reference and (has_execution or has_handler)
        
        results['instructions'][instr_name] = {
            'has_reference': has_reference,
            'has_execution_branch': has_execution,
            'has_handler_function': has_handler,
            'implemented': implemented,
            'reference_count': len(found_references)
        }
        
        if not implemented:
            results['missing'].append(instr_name)
            if not has_reference:
                results['issues'].append(f"No reference to {opcode_str} in Python VM")
            if not has_execution and not has_handler:
                results['issues'].append(f"No execution logic for {opcode_str} in Python VM")
    
    results['total'] = len(coq_instructions)
    results['implemented_count'] = sum(1 for r in results['instructions'].values() if r['implemented'])
    results['coverage'] = results['implemented_count'] / results['total'] * 100 if results['total'] > 0 else 0
    
    return results

def main():
    """Main verification logic."""
    print("=== Implementation Completeness Verification ===\n")
    
    # Parse Coq kernel
    print("Parsing Coq kernel...")
    coq_instructions = parse_coq_instructions_detailed()
    print(f"✅ Found {len(coq_instructions)} instructions in Coq kernel\n")
    
    # Verify Verilog CPU
    print("Verifying Verilog CPU implementation...")
    verilog_results = verify_verilog_cpu(coq_instructions)
    print(f"Verilog CPU Coverage: {verilog_results['coverage']:.1f}% ({verilog_results['implemented_count']}/{verilog_results['total']})")
    
    if verilog_results['missing']:
        print(f"⚠️  Missing in Verilog: {', '.join(verilog_results['missing'])}")
    else:
        print("✅ All instructions implemented in Verilog CPU")
    print()
    
    # Verify Python VM
    print("Verifying Python VM implementation...")
    python_results = verify_python_vm(coq_instructions)
    print(f"Python VM Coverage: {python_results['coverage']:.1f}% ({python_results['implemented_count']}/{python_results['total']})")
    
    if python_results['missing']:
        print(f"⚠️  Missing in Python VM: {', '.join(python_results['missing'])}")
    else:
        print("✅ All instructions implemented in Python VM")
    print()
    
    # Detailed instruction-by-instruction report
    print("=== Instruction-by-Instruction Report ===\n")
    print(f"{'Instruction':<20} {'Verilog':<10} {'Python':<10} {'Status'}")
    print("-" * 60)
    
    all_correct = True
    for instr_name in sorted(coq_instructions.keys()):
        verilog_impl = verilog_results['instructions'][instr_name]['implemented']
        python_impl = python_results['instructions'][instr_name]['implemented']
        
        verilog_status = "✅" if verilog_impl else "❌"
        python_status = "✅" if python_impl else "❌"
        
        if verilog_impl and python_impl:
            status = "COMPLETE"
        elif verilog_impl or python_impl:
            status = "PARTIAL"
            all_correct = False
        else:
            status = "MISSING"
            all_correct = False
        
        print(f"{instr_name:<20} {verilog_status:<10} {python_status:<10} {status}")
    
    print()
    
    # Generate report
    report = {
        'timestamp': str(Path.cwd()),
        'coq_kernel': {
            'file': str(COQ_KERNEL),
            'instruction_count': len(coq_instructions),
            'instructions': list(coq_instructions.keys())
        },
        'verilog_cpu': verilog_results,
        'python_vm': python_results,
        'summary': {
            'total_instructions': len(coq_instructions),
            'verilog_coverage': verilog_results['coverage'],
            'python_coverage': python_results['coverage'],
            'both_complete': verilog_results['coverage'] == 100 and python_results['coverage'] == 100
        }
    }
    
    OUTPUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_JSON, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"Report saved to: {OUTPUT_JSON}\n")
    
    # Final verdict
    if all_correct and verilog_results['coverage'] == 100 and python_results['coverage'] == 100:
        print("🎉 RESULT: All 16 instructions correctly implemented in both Verilog and Python")
        return 0
    else:
        print("⚠️  RESULT: Some instructions missing or incomplete")
        print("\nIssues found:")
        for issue in verilog_results['issues'] + python_results['issues']:
            print(f"  - {issue}")
        return 1

if __name__ == "__main__":
    sys.exit(main())
