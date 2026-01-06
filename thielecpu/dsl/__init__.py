"""
Thiele DSL - A Domain Specific Language that compiles Python AST to Thiele VM opcodes.

This module provides TRUE compilation of Python code to the Thiele Machine instruction set,
with bidirectional source mapping and proper μ-cost tracking at the instruction level.

Key Components:
- ir.py: Intermediate Representation (Thiele IR)
- compiler.py: Python AST → Thiele IR compiler
- executor.py: Thiele IR → VM opcode executor
- sourcemap.py: Bidirectional AST ↔ IR linkage

The DSL bridges the gap between high-level Python code and low-level Thiele opcodes,
enabling true verification where the μ-cost of every operation is tracked.
"""

from .ir import (
    ThieleIR,
    IRInstruction,
    IROpcode,
    SourceLocation,
    IRModule,
)

from .compiler import (
    compile_python_to_ir,
    PythonToThieleCompiler,
)

from .executor import (
    execute_ir,
    IRExecutor,
)

from .sourcemap import (
    SourceMap,
    create_sourcemap,
)

from .verify import (
    verify_python_code,
    compile_and_disassemble,
    get_mu_cost_estimate,
    DSLVerifier,
    VerificationResult,
)

__all__ = [
    # IR types
    'ThieleIR',
    'IRInstruction',
    'IROpcode',
    'SourceLocation',
    'IRModule',
    # Compiler
    'compile_python_to_ir',
    'PythonToThieleCompiler',
    # Executor
    'execute_ir',
    'IRExecutor',
    # Source mapping
    'SourceMap',
    'create_sourcemap',
    # Verification
    'verify_python_code',
    'compile_and_disassemble',
    'get_mu_cost_estimate',
    'DSLVerifier',
    'VerificationResult',
]
