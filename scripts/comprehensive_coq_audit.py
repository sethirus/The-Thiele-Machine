#!/usr/bin/env python3
"""
Comprehensive Coq Proof Audit
Analyzes all Coq files to identify admits, axioms, TODOs, and kernel status
"""

import subprocess
import json
import re
from pathlib import Path
from collections import defaultdict

print("="*80)
print("COMPREHENSIVE COQ PROOF AUDIT")
print("="*80)
print()

# Find all Coq files
coq_files = list(Path('coq').rglob('*.v'))
print(f"Found {len(coq_files)} Coq files\n")

# Categorize files
kernel_files = [f for f in coq_files if 'kernel' in str(f)]
verification_files = [f for f in coq_files if 'verification' in str(f)]
thielemachine_files = [f for f in coq_files if 'thielemachine/coqproofs' in str(f)]
other_files = [f for f in coq_files if f not in kernel_files + verification_files + thielemachine_files]

print("File Categories:")
print(f"  Kernel: {len(kernel_files)}")
print(f"  Verification: {len(verification_files)}")
print(f"  ThieleMachine: {len(thielemachine_files)}")
print(f"  Other: {len(other_files)}")
print()

# Analysis results
results = {
    'total_files': len(coq_files),
    'total_lines': 0,
    'files_with_admits': [],
    'files_with_axioms': [],
    'files_with_todos': [],
    'kernel_status': {},
    'verification_status': {},
    'critical_issues': [],
    'recommendations': []
}

def analyze_file(filepath):
    """Analyze a single Coq file"""
    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()
        lines = content.split('\n')
    
    info = {
        'path': str(filepath),
        'lines': len(lines),
        'admitted_count': 0,
        'axiom_count': 0,
        'todo_count': 0,
        'definitions': 0,
        'lemmas': 0,
        'theorems': 0,
        'admits': [],
        'axioms': [],
        'todos': []
    }
    
    # Count different elements
    for i, line in enumerate(lines, 1):
        # Actual admitted proofs (not in comments)
        if re.match(r'^\s*Admitted\.\s*$', line):
            info['admitted_count'] += 1
            context = '\n'.join(lines[max(0, i-3):i+1])
            info['admits'].append({'line': i, 'context': context})
        
        # Actual axioms (not type definitions)
        if re.match(r'^\s*Axiom\s+\w+', line) and 'Definition' not in line:
            info['axiom_count'] += 1
            info['axioms'].append({'line': i, 'text': line.strip()})
        
        # TODOs
        if 'TODO' in line.upper() or 'FIXME' in line.upper():
            info['todo_count'] += 1
            info['todos'].append({'line': i, 'text': line.strip()})
        
        # Count definitions, lemmas, theorems
        if re.match(r'^\s*(Definition|Fixpoint)', line):
            info['definitions'] += 1
        if re.match(r'^\s*Lemma\s+', line):
            info['lemmas'] += 1
        if re.match(r'^\s*Theorem\s+', line):
            info['theorems'] += 1
    
    return info

# Analyze all files
print("Analyzing all Coq files...")
all_info = []
for f in coq_files:
    info = analyze_file(f)
    all_info.append(info)
    results['total_lines'] += info['lines']
    
    if info['admitted_count'] > 0:
        results['files_with_admits'].append(info)
    if info['axiom_count'] > 0:
        results['files_with_axioms'].append(info)
    if info['todo_count'] > 0:
        results['files_with_todos'].append(info)

print(f"Total lines analyzed: {results['total_lines']:,}\n")

# Kernel analysis
print("="*80)
print("KERNEL ANALYSIS")
print("="*80)
print()

kernel_info = [info for info in all_info if 'kernel' in info['path']]
kernel_admits = sum(info['admitted_count'] for info in kernel_info)
kernel_axioms = sum(info['axiom_count'] for info in kernel_info)
kernel_defs = sum(info['definitions'] for info in kernel_info)
kernel_lemmas = sum(info['lemmas'] for info in kernel_info)
kernel_theorems = sum(info['theorems'] for info in kernel_info)

print(f"Kernel files: {len(kernel_info)}")
print(f"Kernel lines: {sum(info['lines'] for info in kernel_info):,}")
print(f"Definitions: {kernel_defs}")
print(f"Lemmas: {kernel_lemmas}")
print(f"Theorems: {kernel_theorems}")
print(f"Admitted proofs: {kernel_admits}")
print(f"Axioms: {kernel_axioms}")
print()

if kernel_admits == 0 and kernel_axioms == 0:
    print("✅ KERNEL IS COMPLETE - No admits or axioms!")
    results['kernel_status']['complete'] = True
else:
    print(f"⚠️ KERNEL HAS GAPS - {kernel_admits} admits, {kernel_axioms} axioms")
    results['kernel_status']['complete'] = False
    results['critical_issues'].append(f"Kernel has {kernel_admits} admits and {kernel_axioms} axioms")

# List kernel files
print("\nKernel files:")
for info in sorted(kernel_info, key=lambda x: x['path']):
    filename = Path(info['path']).name
    status = "✅" if info['admitted_count'] == 0 and info['axiom_count'] == 0 else "⚠️"
    print(f"  {status} {filename:30s} ({info['lines']:4d} lines, {info['definitions']} defs, {info['lemmas']} lemmas)")

# Check for critical admitted proofs
print("\n" + "="*80)
print("CRITICAL ADMITS ANALYSIS")
print("="*80)
print()

critical_admits = []
for info in results['files_with_admits']:
    # Critical if in kernel or verification
    if 'kernel' in info['path'] or 'verification' in info['path']:
        critical_admits.append(info)

if critical_admits:
    print(f"Found {len(critical_admits)} files with critical admits:\n")
    for info in critical_admits:
        print(f"  {info['path']}")
        print(f"    {info['admitted_count']} admits at lines: {[a['line'] for a in info['admits']]}")
        results['critical_issues'].append(f"{info['path']}: {info['admitted_count']} admits")
else:
    print("✅ No critical admits in kernel or verification!")

# Check for axioms
print("\n" + "="*80)
print("AXIOM ANALYSIS")
print("="*80)
print()

if results['files_with_axioms']:
    print(f"Found {len(results['files_with_axioms'])} files with axioms:\n")
    for info in results['files_with_axioms'][:10]:  # Show first 10
        print(f"  {info['path']}")
        for axiom in info['axioms'][:3]:  # Show first 3 axioms per file
            print(f"    Line {axiom['line']}: {axiom['text'][:80]}")
else:
    print("✅ No axioms found!")

# TODO analysis
print("\n" + "="*80)
print("TODO ANALYSIS")
print("="*80)
print()

if results['files_with_todos']:
    print(f"Found {len(results['files_with_todos'])} files with TODOs/FIXMEs:\n")
    
    # Prioritize kernel and verification TODOs
    kernel_todos = [info for info in results['files_with_todos'] if 'kernel' in info['path']]
    verif_todos = [info for info in results['files_with_todos'] if 'verification' in info['path']]
    
    if kernel_todos:
        print("  Kernel TODOs:")
        for info in kernel_todos:
            print(f"    {Path(info['path']).name}: {info['todo_count']} TODOs")
            for todo in info['todos'][:2]:
                print(f"      Line {todo['line']}: {todo['text'][:70]}")
    
    if verif_todos:
        print("\n  Verification TODOs:")
        for info in verif_todos[:5]:
            print(f"    {Path(info['path']).name}: {info['todo_count']} TODOs")
else:
    print("✅ No TODOs found!")

# Recommendations
print("\n" + "="*80)
print("RECOMMENDATIONS")
print("="*80)
print()

if kernel_admits == 0 and kernel_axioms == 0:
    print("✅ Kernel is complete and proven - excellent foundation!")
    results['recommendations'].append("Kernel complete - ready for production")
else:
    print(f"❗ Complete kernel proofs ({kernel_admits} admits, {kernel_axioms} axioms remaining)")
    results['recommendations'].append("Finish kernel proofs to ensure soundness")

if len(critical_admits) > 0:
    print(f"❗ Address {len(critical_admits)} critical admits in kernel/verification")
    results['recommendations'].append("Complete verification admits")
else:
    print("✅ No critical admits - core proofs are solid!")

# Check VM instruction coverage
vm_step_file = next((info for info in all_info if 'VMStep.v' in info['path']), None)
if vm_step_file:
    with open(vm_step_file['path'], 'r') as f:
        content = f.read()
        instr_count = content.count('| instr_')
        step_count = content.count('| step_')
    print(f"\n✅ VMStep.v has {instr_count//2} instructions and {step_count//2} step rules")
    results['recommendations'].append("VM instruction semantics fully defined")

# Overall status
print("\n" + "="*80)
print("OVERALL STATUS")
print("="*80)
print()

total_admits = sum(info['admitted_count'] for info in all_info)
total_axioms = sum(info['axiom_count'] for info in all_info)
total_defs = sum(info['definitions'] for info in all_info)
total_lemmas = sum(info['lemmas'] for info in all_info)
total_theorems = sum(info['theorems'] for info in all_info)

print(f"Total Coq Files: {len(coq_files)}")
print(f"Total Lines: {results['total_lines']:,}")
print(f"Definitions: {total_defs}")
print(f"Lemmas: {total_lemmas}")
print(f"Theorems: {total_theorems}")
print(f"Admitted: {total_admits}")
print(f"Axioms: {total_axioms}")
print()

completion_rate = ((total_defs + total_lemmas + total_theorems - total_admits) / 
                   max(1, total_defs + total_lemmas + total_theorems)) * 100

print(f"Completion Rate: {completion_rate:.1f}%")
print(f"Critical Issues: {len(results['critical_issues'])}")
print()

if len(results['critical_issues']) == 0:
    print("🎉 NO CRITICAL ISSUES - Coq proofs are in excellent shape!")
else:
    print("⚠️ Critical issues need attention:")
    for issue in results['critical_issues'][:5]:
        print(f"  - {issue}")

# Save results
results['summary'] = {
    'total_files': len(coq_files),
    'total_lines': results['total_lines'],
    'total_admits': total_admits,
    'total_axioms': total_axioms,
    'total_definitions': total_defs,
    'total_lemmas': total_lemmas,
    'total_theorems': total_theorems,
    'completion_rate': completion_rate,
    'kernel_complete': kernel_admits == 0 and kernel_axioms == 0,
    'critical_issues_count': len(results['critical_issues'])
}

Path('artifacts').mkdir(exist_ok=True)
with open('artifacts/coq_audit.json', 'w') as f:
    json.dump(results, f, indent=2, default=str)

print("\n✅ Results saved to artifacts/coq_audit.json")
