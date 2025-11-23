#!/usr/bin/env python3
"""
Proof term size analyzer for Coq modules
Analyzes .vo files and compilation output to identify bottlenecks
"""

import os
import subprocess
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple
import re

class ProofProfiler:
    def __init__(self, coq_dir: Path):
        self.coq_dir = coq_dir
        self.results = {}
        
    def compile_with_timing(self, module_path: Path, timeout: int = 300) -> Dict:
        """Compile a module and collect timing information"""
        
        module_name = module_path.stem
        result = {
            'module': module_name,
            'path': str(module_path),
            'success': False,
            'compilation_time': 0,
            'vo_size': 0,
            'warnings': [],
            'errors': [],
            'proof_times': {},
        }
        
        start_time = time.time()
        
        try:
            # Compile with timing flags
            cmd = [
                'coqc',
                '-time',
                '-Q', str(self.coq_dir), '',
                str(module_path)
            ]
            
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=self.coq_dir
            )
            
            end_time = time.time()
            result['compilation_time'] = end_time - start_time
            
            # Parse output for timing information
            output = proc.stdout + proc.stderr
            
            # Look for timing lines
            timing_pattern = r'(\w+)\s+\(([^)]+)\)\s+(\d+\.\d+)\s+secs'
            for match in re.finditer(timing_pattern, output):
                lemma_name = match.group(1)
                proof_type = match.group(2)
                proof_time = float(match.group(3))
                result['proof_times'][lemma_name] = {
                    'type': proof_type,
                    'time': proof_time
                }
            
            # Check for warnings
            if 'Warning' in output:
                result['warnings'] = re.findall(r'Warning:.*', output)
            
            if proc.returncode == 0:
                result['success'] = True
                
                # Get .vo file size
                vo_path = module_path.with_suffix('.vo')
                if vo_path.exists():
                    result['vo_size'] = vo_path.stat().st_size
            else:
                result['errors'] = re.findall(r'Error:.*', output)
                
        except subprocess.TimeoutExpired:
            result['errors'] = ['Compilation timeout']
            result['compilation_time'] = timeout
        except Exception as e:
            result['errors'] = [str(e)]
            
        return result
    
    def analyze_module_dependencies(self, module_path: Path) -> List[str]:
        """Extract dependencies from a module"""
        
        with open(module_path, 'r') as f:
            content = f.read()
        
        # Look for Require Import statements
        imports = re.findall(r'Require\s+Import\s+([^\.]+)\.', content)
        return imports
    
    def profile_all_modules(self, module_dir: Path) -> Dict:
        """Profile all modules in a directory"""
        
        modules = sorted(module_dir.glob('Bridge_*.v'))
        
        results = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'coq_version': self._get_coq_version(),
            'modules': []
        }
        
        print(f"Profiling {len(modules)} modules...")
        print()
        
        for i, module in enumerate(modules, 1):
            print(f"[{i}/{len(modules)}] Profiling {module.name}...")
            
            result = self.compile_with_timing(module)
            results['modules'].append(result)
            
            # Print summary
            if result['success']:
                print(f"  ✓ Compiled in {result['compilation_time']:.2f}s")
                print(f"  .vo size: {result['vo_size']} bytes")
                
                # Show slowest proofs
                if result['proof_times']:
                    sorted_proofs = sorted(
                        result['proof_times'].items(),
                        key=lambda x: x[1]['time'],
                        reverse=True
                    )[:3]
                    
                    if sorted_proofs:
                        print("  Slowest proofs:")
                        for name, info in sorted_proofs:
                            print(f"    - {name}: {info['time']:.2f}s")
            else:
                print(f"  ✗ Failed after {result['compilation_time']:.2f}s")
                if result['errors']:
                    print(f"  Errors: {result['errors'][0][:100]}")
            
            if result['warnings']:
                print(f"  ⚠ {len(result['warnings'])} warning(s)")
            
            print()
        
        return results
    
    def _get_coq_version(self) -> str:
        """Get Coq version"""
        try:
            result = subprocess.run(
                ['coqc', '--version'],
                capture_output=True,
                text=True
            )
            return result.stdout.split('\n')[0]
        except:
            return "unknown"
    
    def generate_report(self, results: Dict, output_path: Path):
        """Generate a detailed report"""
        
        with open(output_path, 'w') as f:
            f.write("# ThieleUniversalBridge Proof Profiling Report\n\n")
            f.write(f"**Generated**: {results['timestamp']}\n\n")
            f.write(f"**Coq Version**: {results['coq_version']}\n\n")
            
            f.write("## Summary\n\n")
            
            total_time = sum(m['compilation_time'] for m in results['modules'])
            total_size = sum(m['vo_size'] for m in results['modules'])
            success_count = sum(1 for m in results['modules'] if m['success'])
            
            f.write(f"- **Total modules**: {len(results['modules'])}\n")
            f.write(f"- **Successful**: {success_count}\n")
            f.write(f"- **Failed**: {len(results['modules']) - success_count}\n")
            f.write(f"- **Total compilation time**: {total_time:.2f}s\n")
            f.write(f"- **Total .vo size**: {total_size} bytes ({total_size / 1024:.2f} KB)\n\n")
            
            f.write("## Module Details\n\n")
            
            for module in results['modules']:
                status = "✓" if module['success'] else "✗"
                f.write(f"### {status} {module['module']}\n\n")
                f.write(f"- **Compilation time**: {module['compilation_time']:.2f}s\n")
                f.write(f"- **Size**: {module['vo_size']} bytes\n")
                
                if module['warnings']:
                    f.write(f"- **Warnings**: {len(module['warnings'])}\n")
                
                if module['errors']:
                    f.write(f"- **Errors**:\n")
                    for error in module['errors'][:3]:
                        f.write(f"  - {error}\n")
                
                if module['proof_times']:
                    f.write(f"- **Proof times** (top 5):\n")
                    sorted_proofs = sorted(
                        module['proof_times'].items(),
                        key=lambda x: x[1]['time'],
                        reverse=True
                    )[:5]
                    
                    for name, info in sorted_proofs:
                        f.write(f"  - `{name}`: {info['time']:.2f}s\n")
                
                f.write("\n")
            
            f.write("## Recommendations\n\n")
            
            # Identify problematic modules
            slow_modules = [
                m for m in results['modules']
                if m['compilation_time'] > 10 and m['success']
            ]
            
            if slow_modules:
                f.write("### Slow Modules (>10s)\n\n")
                for module in sorted(slow_modules, key=lambda x: x['compilation_time'], reverse=True):
                    f.write(f"- **{module['module']}**: {module['compilation_time']:.2f}s\n")
                    if module['proof_times']:
                        slowest = max(module['proof_times'].items(), key=lambda x: x[1]['time'])
                        f.write(f"  - Slowest proof: `{slowest[0]}` ({slowest[1]['time']:.2f}s)\n")
                f.write("\n")
            
            failed_modules = [m for m in results['modules'] if not m['success']]
            if failed_modules:
                f.write("### Failed Modules\n\n")
                for module in failed_modules:
                    f.write(f"- **{module['module']}**: {module['errors'][0] if module['errors'] else 'Unknown error'}\n")
                f.write("\n")

def main():
    script_dir = Path(__file__).parent
    verification_dir = script_dir.parent
    coq_dir = verification_dir.parent.parent
    module_dir = verification_dir / "modular"
    
    print("=== ThieleUniversalBridge Proof Profiler ===")
    print(f"Module directory: {module_dir}")
    print()
    
    if not module_dir.exists():
        print("Error: Module directory not found. Run extract_modules.py first.")
        return 1
    
    profiler = ProofProfiler(coq_dir)
    results = profiler.profile_all_modules(module_dir)
    
    # Save results
    json_path = script_dir / "profiling_results.json"
    with open(json_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"Saved detailed results to: {json_path}")
    
    # Generate report
    report_path = script_dir / "PROFILING_REPORT.md"
    profiler.generate_report(results, report_path)
    print(f"Generated report: {report_path}")
    
    print("\n=== Profiling Complete ===")
    return 0

if __name__ == "__main__":
    import sys
    sys.exit(main())
