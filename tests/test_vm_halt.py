# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import json
import os
import sys
import tempfile
from pathlib import Path

# Add parent dir for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from thielecpu.assemble import parse
from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.isa import CSR

def test_lassert_unsat():
    with tempfile.TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir)
        
        # Create unsat CNF and LRAT proof
        cnf_path = outdir / "unsat.cnf"
        cnf_path.write_text("p cnf 1 2\n1 0\n-1 0\n", encoding="utf-8")
        proof_path = outdir / "unsat.lrat"
        proof_path.write_text("3 0 1 2 0\n", encoding="utf-8")
        config_path = outdir / "unsat.json"
        config_path.write_text(
            json.dumps(
                {
                    "cnf": str(cnf_path),
                    "proof_type": "LRAT",
                    "proof": str(proof_path),
                }
            ),
            encoding="utf-8",
        )

        # Create thm program
        thm_content = f'''
PNEW {{1,2}}
LASSERT "{config_path.absolute()}"
MDLACC
EMIT "Should not reach here"
'''
        thm_path = outdir / "test_unsat.thm"
        thm_path.write_text(thm_content, encoding='utf-8')
        
        # Parse and run
        program = parse(thm_path.read_text(encoding='utf-8').splitlines(), outdir)
        vm = VM(State())
        vm.run(program, outdir)
        
        # Check trace for halt
        trace_path = outdir / "trace.log"
        trace = trace_path.read_text(encoding='utf-8')
        assert "LASSERT unsat - halting VM" in trace
        assert "EMIT" not in trace  # Should not execute
        assert vm.state.csr[CSR.ERR] == 1
        print("LASSERT unsat test: PASSED")

def test_pyexec_error():
    with tempfile.TemporaryDirectory() as tmpdir:
        outdir = Path(tmpdir)
        
        # Create error py
        error_py = outdir / "error.py"
        error_py.write_text("print('Running')\nassert False, 'Intentional error'", encoding='utf-8')
        
        # Create thm
        thm_content = f'''
PNEW {{1,2}}
PYEXEC "{error_py.absolute()}"
MDLACC
EMIT "Should not reach here"
'''
        thm_path = outdir / "test_error.thm"
        thm_path.write_text(thm_content, encoding='utf-8')
        
        # Parse and run
        program = parse(thm_path.read_text(encoding='utf-8').splitlines(), outdir)
        vm = VM(State())
        vm.run(program, outdir)
        
        # Check trace
        trace_path = outdir / "trace.log"
        trace = trace_path.read_text(encoding='utf-8')
        assert "PYEXEC output: Running" in trace
        assert "PYEXEC error detected - halting VM" in trace
        assert "EMIT" not in trace
        assert vm.state.csr[CSR.ERR] == 1
        print("PYEXEC error test: PASSED")

if __name__ == "__main__":
    test_lassert_unsat()
    test_pyexec_error()
    print("All VM halt tests passed!")