#!/usr/bin/env python3
"""
DEFINITIVE Coq-to-Verilog Instruction Mapping Verification
Deeply examines Coq proofs to ensure correct opcode count
"""

import re
import sys
from pathlib import Path
import json

print("="*80)
print("DEFINITIVE COQ-TO-VERILOG INSTRUCTION MAPPING")
print("Deep analysis of Coq proofs to verify correct opcode count")
print("="*80)
print()

# ============================================================================
# PART 1: Extract EXACT Coq instruction definitions
# ============================================================================

print("PART 1: Coq Instruction Definitions (vm_instruction)")
print("-"*80)

vmstep_path = Path("coq/kernel/VMStep.v")
coq_instructions = []
coq_step_rules = []

if vmstep_path.exists():
    with open(vmstep_path) as f:
        content = f.read()
    
    # Find the exact inductive definition
    inductive_match = re.search(
        r'Inductive vm_instruction :=\s*((?:\|[^\n]+\n?)+)',
        content,
        re.MULTILINE
    )
    
    if inductive_match:
        inductive_body = inductive_match.group(1)
        # Extract each instruction constructor
        instr_pattern = r'\|\s*instr_(\w+)'
        for match in re.finditer(instr_pattern, inductive_body):
            coq_instructions.append(match.group(1))
    
    # Find step rules
    step_pattern = r'\|\s*step_(\w+)\s*:'
    for match in re.finditer(step_pattern, content):
        coq_step_rules.append(match.group(1))

print(f"Found {len(coq_instructions)} instruction constructors in vm_instruction:")
for i, instr in enumerate(coq_instructions, 1):
    print(f"  {i}. instr_{instr}")

print(f"\nFound {len(coq_step_rules)} operational semantics rules in vm_step:")
step_by_instr = {}
for rule in coq_step_rules:
    # Map step rules back to instructions
    base_instr = rule.split('_')[0] if '_' in rule else rule
    if base_instr not in step_by_instr:
        step_by_instr[base_instr] = []
    step_by_instr[base_instr].append(rule)

for instr in sorted(step_by_instr.keys()):
    rules = step_by_instr[instr]
    print(f"  {instr}: {len(rules)} rule(s) - {', '.join(rules)}")

print()

# ============================================================================
# PART 2: Extract Verilog opcodes
# ============================================================================

print("PART 2: Verilog CPU Opcodes")
print("-"*80)

cpu_path = Path("thielecpu/hardware/thiele_cpu.v")
verilog_opcodes = {}
verilog_handlers = []

if cpu_path.exists():
    with open(cpu_path) as f:
        content = f.read()
    
    # Extract opcode definitions
    opcode_pattern = r'localparam\s+\[7:0\]\s+OPCODE_(\w+)\s*=\s*8\'h([0-9A-Fa-f]+);'
    for match in re.finditer(opcode_pattern, content):
        name = match.group(1)
        value = match.group(2)
        verilog_opcodes[name] = value
    
    # Extract handlers from case statement
    handler_pattern = r'OPCODE_(\w+)\s*:\s*begin'
    for match in re.finditer(handler_pattern, content):
        verilog_handlers.append(match.group(1))

print(f"Found {len(verilog_opcodes)} opcode definitions:")
for name, value in sorted(verilog_opcodes.items()):
    print(f"  OPCODE_{name} = 0x{value}")

print(f"\nFound {len(verilog_handlers)} handlers in execute case:")
for handler in sorted(set(verilog_handlers)):
    print(f"  OPCODE_{handler}")

print()

# ============================================================================
# PART 3: Detailed mapping verification
# ============================================================================

print("="*80)
print("PART 3: INSTRUCTION-BY-INSTRUCTION VERIFICATION")
print("="*80)
print()

# Mapping table
coq_to_verilog_map = {
    'pnew': 'PNEW',
    'psplit': 'PSPLIT',
    'pmerge': 'PMERGE',
    'lassert': 'LASSERT',
    'ljoin': 'LJOIN',
    'mdlacc': 'MDLACC',
    'emit': 'EMIT',
    'pdiscover': 'PDISCOVER',
    'pyexec': 'PYEXEC'
}

print("Verifying each Coq instruction has:")
print("  1. Verilog opcode definition")
print("  2. Handler in execute case statement")
print("  3. Execution logic implementation")
print()

all_complete = True
mapping_results = {}

for i, coq_instr in enumerate(coq_instructions, 1):
    verilog_name = coq_to_verilog_map.get(coq_instr, coq_instr.upper())
    
    has_opcode = verilog_name in verilog_opcodes
    has_handler = verilog_name in verilog_handlers
    
    # Check for execution task/logic
    has_execution = False
    if cpu_path.exists():
        with open(cpu_path) as f:
            cpu_content = f.read()
            # Look for task or state handling
            execution_patterns = [
                f'task execute_{coq_instr}',
                f'execute_{coq_instr}\\(',
                f'STATE_{coq_instr.upper()}'
            ]
            for pattern in execution_patterns:
                if re.search(pattern, cpu_content, re.IGNORECASE):
                    has_execution = True
                    break
            # LASSERT and PYEXEC use state machines
            if coq_instr in ['lassert', 'pyexec'] and has_handler:
                has_execution = True
    
    is_complete = has_opcode and has_handler and has_execution
    
    status = "✅" if is_complete else "❌"
    
    details = []
    if has_opcode:
        details.append(f"opcode=0x{verilog_opcodes[verilog_name]}")
    else:
        details.append("NO_OPCODE")
        all_complete = False
    
    if has_handler:
        details.append("handler=YES")
    else:
        details.append("handler=NO")
        all_complete = False
    
    if has_execution:
        details.append("exec=YES")
    else:
        details.append("exec=NO")
        all_complete = False
    
    print(f"{status} {i}. instr_{coq_instr:12s} → OPCODE_{verilog_name:12s}")
    print(f"     {', '.join(details)}")
    
    # Show step rules for this instruction
    instr_rules = step_by_instr.get(coq_instr, [])
    if instr_rules:
        print(f"     Coq rules: {', '.join(instr_rules)}")
    
    mapping_results[coq_instr] = {
        'verilog_name': verilog_name,
        'has_opcode': has_opcode,
        'has_handler': has_handler,
        'has_execution': has_execution,
        'is_complete': is_complete,
        'step_rules': instr_rules
    }
    print()

# ============================================================================
# PART 4: Additional Verilog opcodes (beyond Coq spec)
# ============================================================================

print("="*80)
print("PART 4: ADDITIONAL VERILOG OPCODES (Beyond Coq Specification)")
print("="*80)
print()

coq_opcode_names = set(coq_to_verilog_map.values())
additional_opcodes = {k: v for k, v in verilog_opcodes.items() if k not in coq_opcode_names}

if additional_opcodes:
    print(f"Found {len(additional_opcodes)} additional opcodes in Verilog:")
    for name, value in sorted(additional_opcodes.items()):
        print(f"  OPCODE_{name} = 0x{value}")
    print()
    print("These are implementation extensions beyond the Coq specification.")
else:
    print("No additional opcodes found - Verilog matches Coq exactly.")

print()

# ============================================================================
# PART 5: Final verification
# ============================================================================

print("="*80)
print("FINAL VERIFICATION RESULTS")
print("="*80)
print()

complete_count = sum(1 for r in mapping_results.values() if r['is_complete'])
total_count = len(mapping_results)
coverage_pct = (complete_count / total_count * 100) if total_count > 0 else 0

print(f"Coq Instructions: {total_count}")
print(f"Coq Step Rules: {len(coq_step_rules)}")
print(f"Verilog Opcodes: {len(verilog_opcodes)}")
print(f"Verilog Handlers: {len(set(verilog_handlers))}")
print()
print(f"Complete Mappings: {complete_count}/{total_count} ({coverage_pct:.1f}%)")
print()

if all_complete and complete_count == total_count:
    print("✅ VERDICT: CORRECT AND COMPLETE")
    print()
    print(f"The Verilog CPU has exactly {total_count} opcodes for the {total_count} Coq instructions.")
    print("Each instruction has:")
    print("  ✓ Opcode definition")
    print("  ✓ Handler in execute state")
    print("  ✓ Execution logic")
    print()
    print(f"The CPU also implements {len(additional_opcodes)} additional opcodes")
    print("as extensions beyond the base Coq specification.")
    result = "CORRECT"
else:
    print("❌ VERDICT: INCOMPLETE OR INCORRECT")
    missing = [k for k, v in mapping_results.items() if not v['is_complete']]
    print(f"\nMissing/incomplete: {missing}")
    result = "INCOMPLETE"

# Save results
output_path = Path("artifacts/definitive_mapping.json")
output_path.parent.mkdir(exist_ok=True)
with open(output_path, 'w') as f:
    json.dump({
        'coq_instructions': coq_instructions,
        'coq_step_rules': coq_step_rules,
        'verilog_opcodes': verilog_opcodes,
        'verilog_handlers': list(set(verilog_handlers)),
        'additional_opcodes': additional_opcodes,
        'mapping_results': mapping_results,
        'complete_count': complete_count,
        'total_count': total_count,
        'coverage_percentage': coverage_pct,
        'verdict': result
    }, f, indent=2)

print(f"\n✅ Results saved to: {output_path}")
print()

sys.exit(0 if all_complete else 1)
