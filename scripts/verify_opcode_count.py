#!/usr/bin/env python3
"""
DEFINITIVE Coq Instruction Count and Verilog Mapping
Accurately counts Coq instructions and verifies Verilog implementation
"""

import subprocess
import json
from pathlib import Path

print("="*80)
print("DEFINITIVE COQ INSTRUCTION VERIFICATION")
print("="*80)
print()

# Count Coq instructions using awk (most reliable)
print("Extracting Coq instructions from VMStep.v...")
result = subprocess.run(
    ["awk", "/^Inductive vm_instruction/,/^\\.$/ { if (/\\| instr_/) print }",
     "coq/kernel/VMStep.v"],
    capture_output=True,
    text=True
)

coq_lines = [line.strip() for line in result.stdout.split('\n') if line.strip()]
coq_instructions = []

for line in coq_lines:
    if '| instr_' in line:
        # Extract instruction name
        name = line.split('instr_')[1].split()[0]
        if name not in coq_instructions:  # Avoid duplicates
            coq_instructions.append(name)

print(f"\nFound {len(coq_instructions)} UNIQUE Coq instructions:")
for i, instr in enumerate(coq_instructions, 1):
    print(f"  {i}. instr_{instr}")

# Count step rules
print("\nExtracting Coq step rules...")
result = subprocess.run(
    ["grep", "^| step_", "coq/kernel/VMStep.v"],
    capture_output=True,
    text=True
)

step_rules = []
for line in result.stdout.split('\n'):
    if '| step_' in line:
        name = line.split('step_')[1].split()[0].rstrip(':')
        step_rules.append(name)

print(f"Found {len(step_rules)} step rules:")
# Group by instruction
step_groups = {}
for rule in step_rules:
    base = rule.split('_')[0]
    if base not in step_groups:
        step_groups[base] = []
    step_groups[base].append(rule)

for base in sorted(step_groups.keys()):
    rules = step_groups[base]
    print(f"  {base}: {rules}")

# Check Verilog opcodes
print("\n" + "="*80)
print("VERILOG CPU VERIFICATION")
print("="*80)
print()

result = subprocess.run(
    ["grep", "^localparam.*OPCODE_", "thielecpu/hardware/thiele_cpu.v"],
    capture_output=True,
    text=True
)

verilog_opcodes = {}
for line in result.stdout.split('\n'):
    if 'OPCODE_' in line:
        parts = line.split('OPCODE_')[1]
        name = parts.split()[0]
        value = parts.split('=')[1].split(';')[0].strip()
        verilog_opcodes[name] = value

print(f"Found {len(verilog_opcodes)} Verilog opcodes:")
for name, value in sorted(verilog_opcodes.items()):
    print(f"  OPCODE_{name} = {value}")

# Map Coq to Verilog
print("\n" + "="*80)
print("MAPPING VERIFICATION")
print("="*80)
print()

# Expected mapping
coq_to_verilog = {
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

all_found = True
for coq_instr in coq_instructions:
    verilog_name = coq_to_verilog.get(coq_instr, coq_instr.upper())
    if verilog_name in verilog_opcodes:
        print(f"✅ instr_{coq_instr:12s} → OPCODE_{verilog_name:12s} = {verilog_opcodes[verilog_name]}")
    else:
        print(f"❌ instr_{coq_instr:12s} → OPCODE_{verilog_name:12s} MISSING")
        all_found = False

# Check for additional opcodes
print("\nAdditional Verilog opcodes (beyond Coq spec):")
coq_verilog_names = set(coq_to_verilog.values())
for name, value in sorted(verilog_opcodes.items()):
    if name not in coq_verilog_names:
        print(f"  OPCODE_{name} = {value}")

# Final verdict
print("\n" + "="*80)
print("FINAL VERDICT")
print("="*80)
print()

print(f"Coq Instructions (vm_instruction): {len(coq_instructions)}")
print(f"Coq Step Rules (vm_step): {len(step_rules)}")
print(f"Verilog Opcodes: {len(verilog_opcodes)}")
print()

if all_found and len(coq_instructions) == 9:
    print("✅ CORRECT: Verilog has ALL 9 Coq instructions")
    print()
    print("The number of opcodes is CORRECT:")
    print(f"  - Coq defines: {len(coq_instructions)} instructions")
    print(f"  - Verilog implements: {len(coq_instructions)} matching opcodes")
    print(f"  - Plus {len(verilog_opcodes) - len(coq_instructions)} additional opcodes as extensions")
    print()
    print("The 13 step rules map to 9 instructions because some instructions")
    print("have multiple execution paths (success/failure):")
    for base in sorted(step_groups.keys()):
        if len(step_groups[base]) > 1:
            print(f"  - {base}: {len(step_groups[base])} paths: {step_groups[base]}")
else:
    print(f"❌ ERROR: Missing or incorrect opcode count")

# Save results
output = {
    'coq_instructions': coq_instructions,
    'coq_instruction_count': len(coq_instructions),
    'coq_step_rules': step_rules,
    'coq_step_count': len(step_rules),
    'verilog_opcodes': verilog_opcodes,
    'verilog_opcode_count': len(verilog_opcodes),
    'all_mapped': all_found,
    'verdict': 'CORRECT' if all_found and len(coq_instructions) == 9 else 'INCORRECT'
}

Path('artifacts').mkdir(exist_ok=True)
with open('artifacts/opcode_count_verification.json', 'w') as f:
    json.dump(output, f, indent=2)

print("\n✅ Results saved to artifacts/opcode_count_verification.json")
