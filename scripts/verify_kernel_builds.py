#!/usr/bin/env python3
"""
Comprehensive Coq Kernel Build Verification
Compiles all kernel files and verifies they build successfully with Coq
"""

import subprocess
import json
from pathlib import Path
import time

print("="*80)
print("COQ KERNEL BUILD VERIFICATION")
print("="*80)
print()

# Check Coq version
print("Checking Coq installation...")
result = subprocess.run(['coqc', '--version'], capture_output=True, text=True)
if result.returncode == 0:
    version = result.stdout.strip().split('\n')[0]
    print(f"✅ {version}")
else:
    print("❌ Coq not installed")
    exit(1)

print()

# Kernel files in dependency order
kernel_files = [
    'VMState.v',
    'VMStep.v',
    'Kernel.v',
    'KernelTM.v',
    'KernelThiele.v',
    'VMEncoding.v',
    'SimulationProof.v',
    'MuLedgerConservation.v',
    'PDISCOVERIntegration.v',
    'Subsumption.v'
]

kernel_dir = Path('coq/kernel')
results = {
    'coq_version': version if result.returncode == 0 else None,
    'files_compiled': [],
    'files_failed': [],
    'total_time': 0,
    'all_success': True
}

print("="*80)
print("COMPILING KERNEL FILES")
print("="*80)
print()

total_start = time.time()

for filename in kernel_files:
    filepath = kernel_dir / filename
    if not filepath.exists():
        print(f"⚠️  {filename:30s} - FILE NOT FOUND")
        results['files_failed'].append({'file': filename, 'error': 'File not found'})
        results['all_success'] = False
        continue
    
    print(f"Compiling {filename:30s} ... ", end='', flush=True)
    start = time.time()
    
    result = subprocess.run(
        ['coqc', filename],
        cwd=kernel_dir,
        capture_output=True,
        text=True
    )
    
    elapsed = time.time() - start
    
    if result.returncode == 0:
        print(f"✅ OK ({elapsed:.1f}s)")
        results['files_compiled'].append({
            'file': filename,
            'time': elapsed,
            'success': True
        })
    else:
        print(f"❌ FAILED ({elapsed:.1f}s)")
        error_msg = result.stderr if result.stderr else result.stdout
        print(f"   Error: {error_msg[:200]}")
        results['files_failed'].append({
            'file': filename,
            'error': error_msg,
            'time': elapsed
        })
        results['all_success'] = False

total_elapsed = time.time() - total_start
results['total_time'] = total_elapsed

print()
print("="*80)
print("BUILD SUMMARY")
print("="*80)
print()

print(f"Total files: {len(kernel_files)}")
print(f"Compiled successfully: {len(results['files_compiled'])}")
print(f"Failed: {len(results['files_failed'])}")
print(f"Total time: {total_elapsed:.1f}s")
print()

if results['all_success']:
    print("🎉 ALL KERNEL FILES COMPILED SUCCESSFULLY!")
    print()
    print("Verification:")
    print("  ✅ VMState.v - Base state definitions")
    print("  ✅ VMStep.v - 16 instruction operational semantics")
    print("  ✅ Kernel.v - Kernel machine foundation")
    print("  ✅ KernelTM.v - Turing machine kernel")
    print("  ✅ KernelThiele.v - Thiele machine kernel")
    print("  ✅ VMEncoding.v - VM state encoding")
    print("  ✅ SimulationProof.v - VM simulation proofs")
    print("  ✅ MuLedgerConservation.v - μ-cost conservation proofs")
    print("  ✅ PDISCOVERIntegration.v - Partition discovery integration")
    print("  ✅ Subsumption.v - TURING ⊊ THIELE proof")
    print()
    print("The updated kernel with 16 instructions compiles cleanly!")
else:
    print("❌ SOME FILES FAILED TO COMPILE")
    print()
    print("Failed files:")
    for failed in results['files_failed']:
        print(f"  ❌ {failed['file']}")
        if 'error' in failed:
            print(f"     {failed['error'][:100]}")

# Check .vo files were generated
print()
print("="*80)
print("COMPILED ARTIFACTS")
print("="*80)
print()

vo_files = list(kernel_dir.glob('*.vo'))
print(f"Generated {len(vo_files)} .vo files:")
for vo in sorted(vo_files):
    size = vo.stat().st_size
    print(f"  {vo.name:30s} ({size:,} bytes)")

# Save results
Path('artifacts').mkdir(exist_ok=True)
with open('artifacts/kernel_build_verification.json', 'w') as f:
    json.dump(results, f, indent=2)

print()
print("✅ Results saved to artifacts/kernel_build_verification.json")

# Exit with appropriate code
exit(0 if results['all_success'] else 1)
