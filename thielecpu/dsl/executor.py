"""
Thiele IR Executor

Executes Thiele IR on the virtual machine with real μ-cost tracking.
This is TRUE execution - not exec(), but interpretation of IR opcodes
with precise μ-ledger accounting per instruction.

The executor maintains:
1. A value stack for computation
2. A call stack for function calls
3. A μ-ledger that tracks discovery and execution costs
4. Source locations for debugging and verification
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Tuple, Callable
import math

from .ir import (
    IRModule,
    IRInstruction,
    IROpcode,
    estimate_mu_cost,
)


@dataclass
class ExecutionFrame:
    """A call frame on the execution stack."""
    return_address: int
    local_vars: Dict[str, Any]
    stack_base: int


@dataclass
class MuLedger:
    """
    μ-cost ledger that tracks execution costs per the thesis specification.
    
    μ_total = μ_discovery + μ_execution
    
    Discovery: Cost of learning partition structure
    Execution: Cost of performing computation
    """
    mu_discovery: int = 0
    mu_execution: int = 0
    landauer_entropy: int = 0  # Irreversible bits erased
    
    # Instruction-level tracking
    instructions_executed: int = 0
    
    @property
    def total(self) -> int:
        return self.mu_discovery + self.mu_execution
    
    def charge_discovery(self, bits: int) -> None:
        """Charge for discovering structure."""
        self.mu_discovery = (self.mu_discovery + bits) & 0xFFFFFFFF
    
    def charge_execution(self, bits: int) -> None:
        """Charge for executing computation."""
        self.mu_execution = (self.mu_execution + bits) & 0xFFFFFFFF
    
    def charge_landauer(self, bits: int) -> None:
        """Charge for irreversible erasure (thermodynamic cost)."""
        self.landauer_entropy = (self.landauer_entropy + bits) & 0xFFFFFFFF
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'mu_discovery': self.mu_discovery,
            'mu_execution': self.mu_execution,
            'mu_total': self.total,
            'landauer_entropy': self.landauer_entropy,
            'instructions_executed': self.instructions_executed,
        }


@dataclass
class ExecutionTrace:
    """
    Trace of IR execution for debugging and verification.
    Each entry records the instruction, its μ-cost, and the stack state.
    """
    entries: List[Dict[str, Any]] = field(default_factory=list)
    
    def add(self, pc: int, instr: IRInstruction, 
            mu_before: int, mu_after: int,
            stack_depth: int,
            result: Any = None) -> None:
        self.entries.append({
            'pc': pc,
            'opcode': instr.opcode.name,
            'operands': instr.operands,
            'source_line': instr.source.lineno if instr.source else None,
            'mu_before': mu_before,
            'mu_after': mu_after,
            'mu_delta': mu_after - mu_before,
            'stack_depth': stack_depth,
            'result': repr(result)[:50] if result is not None else None,
        })


@dataclass
class ExecutionResult:
    """Result of IR execution."""
    value: Any = None
    mu_ledger: MuLedger = field(default_factory=MuLedger)
    trace: ExecutionTrace = field(default_factory=ExecutionTrace)
    halted: bool = False
    error: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'value': repr(self.value),
            'mu_ledger': self.mu_ledger.to_dict(),
            'trace_length': len(self.trace.entries),
            'halted': self.halted,
            'error': self.error,
        }


class IRExecutor:
    """
    Executes Thiele IR with real μ-cost tracking.
    
    This is the TRUE execution engine - no Python exec() involved.
    Every operation is interpreted and charged against the μ-ledger.
    """
    
    # Maximum instructions to prevent infinite loops
    MAX_INSTRUCTIONS = 1_000_000
    
    def __init__(self, module: IRModule, builtins: Optional[Dict[str, Any]] = None):
        self.module = module
        self.builtins = builtins or self._default_builtins()
        
        # Execution state
        self.pc = 0  # Program counter
        self.stack: List[Any] = []  # Value stack
        self.call_stack: List[ExecutionFrame] = []
        
        # Variable storage
        self.globals: Dict[str, Any] = {}
        self.locals: Dict[str, Any] = {}
        
        # μ-ledger
        self.mu_ledger = MuLedger()
        
        # Execution trace
        self.trace = ExecutionTrace()
        
        # Halted flag
        self.halted = False
        self.error: Optional[str] = None
    
    def _default_builtins(self) -> Dict[str, Callable]:
        """Default builtin functions available in IR execution."""
        return {
            'print': self._builtin_print,
            'len': len,
            'range': range,
            'int': int,
            'float': float,
            'str': str,
            'bool': bool,
            'list': list,
            'tuple': tuple,
            'set': set,
            'dict': dict,
            'abs': abs,
            'min': min,
            'max': max,
            'sum': sum,
            'sorted': sorted,
            'enumerate': enumerate,
            'zip': zip,
            'map': map,
            'filter': filter,
            'pow': pow,
            'divmod': divmod,
            'round': round,
        }
    
    def _builtin_print(self, *args, **kwargs) -> None:
        """Built-in print that tracks output."""
        # μ-cost: bits of output
        output = ' '.join(str(a) for a in args)
        self.mu_ledger.charge_execution(len(output) * 8)
        print(*args, **kwargs)
    
    def execute(self) -> ExecutionResult:
        """Execute the IR module and return the result."""
        instructions = self.module.instructions
        
        if not instructions:
            return ExecutionResult(mu_ledger=self.mu_ledger, trace=self.trace)
        
        while not self.halted and self.pc < len(instructions):
            if self.mu_ledger.instructions_executed >= self.MAX_INSTRUCTIONS:
                self.error = f"Execution limit exceeded: {self.MAX_INSTRUCTIONS} instructions"
                self.halted = True
                break
            
            instr = instructions[self.pc]
            mu_before = self.mu_ledger.total
            
            try:
                self._execute_instruction(instr)
            except Exception as e:
                self.error = f"Error at PC={self.pc}: {e}"
                self.halted = True
                break
            
            mu_after = self.mu_ledger.total
            
            # Record trace
            self.trace.add(
                pc=self.pc - 1,  # PC was incremented
                instr=instr,
                mu_before=mu_before,
                mu_after=mu_after,
                stack_depth=len(self.stack),
                result=self.stack[-1] if self.stack else None,
            )
            
            self.mu_ledger.instructions_executed += 1
        
        # Get result (top of stack)
        result_value = self.stack[-1] if self.stack else None
        
        return ExecutionResult(
            value=result_value,
            mu_ledger=self.mu_ledger,
            trace=self.trace,
            halted=self.halted,
            error=self.error,
        )
    
    def _execute_instruction(self, instr: IRInstruction) -> None:
        """Execute a single IR instruction."""
        opcode = instr.opcode
        operands = instr.operands
        
        # Charge μ-cost
        discovery, execution = estimate_mu_cost(opcode, operands)
        self.mu_ledger.charge_discovery(discovery)
        self.mu_ledger.charge_execution(execution)
        
        # Dispatch by opcode
        handler = getattr(self, f'_exec_{opcode.name}', None)
        if handler:
            handler(instr)
        else:
            raise NotImplementedError(f"Opcode not implemented: {opcode.name}")
        
        # Default: advance PC
        if opcode not in (IROpcode.JUMP, IROpcode.JUMP_IF_TRUE, IROpcode.JUMP_IF_FALSE,
                          IROpcode.RETURN, IROpcode.HALT):
            self.pc += 1
    
    # ═══════════════════════════════════════════════════════════════════
    # INSTRUCTION IMPLEMENTATIONS
    # ═══════════════════════════════════════════════════════════════════
    
    def _exec_NOP(self, instr: IRInstruction) -> None:
        """No operation."""
        pass
    
    def _exec_HALT(self, instr: IRInstruction) -> None:
        """Halt execution."""
        self.halted = True
    
    def _exec_LOAD_CONST(self, instr: IRInstruction) -> None:
        """Push constant to stack."""
        value = instr.operands[0] if instr.operands else None
        self.stack.append(value)
    
    def _exec_LOAD_VAR(self, instr: IRInstruction) -> None:
        """Load variable to stack."""
        name = instr.operands[0]
        if name in self.locals:
            value = self.locals[name]
        elif name in self.globals:
            value = self.globals[name]
        elif name in self.builtins:
            value = self.builtins[name]
        else:
            raise NameError(f"Undefined variable: {name}")
        self.stack.append(value)
    
    def _exec_STORE_VAR(self, instr: IRInstruction) -> None:
        """Store stack top to variable."""
        name = instr.operands[0]
        value = self.stack[-1]  # Keep on stack
        self.locals[name] = value
    
    # Arithmetic
    def _exec_ADD(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a + b)
    
    def _exec_SUB(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a - b)
    
    def _exec_MUL(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a * b)
    
    def _exec_DIV(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a / b)
    
    def _exec_MOD(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a % b)
    
    def _exec_POW(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a ** b)
    
    def _exec_NEG(self, instr: IRInstruction) -> None:
        a = self.stack.pop()
        self.stack.append(-a)
    
    # Bitwise
    def _exec_BIT_AND(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a & b)
    
    def _exec_BIT_OR(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a | b)
    
    def _exec_BIT_XOR(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a ^ b)
    
    def _exec_BIT_NOT(self, instr: IRInstruction) -> None:
        a = self.stack.pop()
        self.stack.append(~a)
    
    def _exec_LSHIFT(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a << b)
    
    def _exec_RSHIFT(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a >> b)
    
    # Comparison
    def _exec_EQ(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a == b)
    
    def _exec_NE(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a != b)
    
    def _exec_LT(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a < b)
    
    def _exec_LE(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a <= b)
    
    def _exec_GT(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a > b)
    
    def _exec_GE(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a >= b)
    
    # Logical
    def _exec_BOOL_AND(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a and b)
    
    def _exec_BOOL_OR(self, instr: IRInstruction) -> None:
        b = self.stack.pop()
        a = self.stack.pop()
        self.stack.append(a or b)
    
    def _exec_BOOL_NOT(self, instr: IRInstruction) -> None:
        a = self.stack.pop()
        self.stack.append(not a)
    
    # Control flow
    def _exec_JUMP(self, instr: IRInstruction) -> None:
        target = instr.operands[0]
        self.pc = target
    
    def _exec_JUMP_IF_TRUE(self, instr: IRInstruction) -> None:
        target = instr.operands[0]
        cond = self.stack.pop()
        if cond:
            self.pc = target
        else:
            self.pc += 1
    
    def _exec_JUMP_IF_FALSE(self, instr: IRInstruction) -> None:
        target = instr.operands[0]
        cond = self.stack.pop()
        if not cond:
            self.pc = target
        else:
            self.pc += 1
    
    # Function calls
    def _exec_CALL(self, instr: IRInstruction) -> None:
        func_name = instr.operands[0]
        arg_count = instr.operands[1] if len(instr.operands) > 1 else 0
        
        # Pop arguments
        args = [self.stack.pop() for _ in range(arg_count)]
        args.reverse()
        
        # Check for builtin
        if func_name in self.builtins:
            result = self.builtins[func_name](*args)
            self.stack.append(result)
            self.pc += 1
            return
        
        # Check for user-defined function
        label = f"func_{func_name}"
        if label in self.module.labels:
            # Create call frame
            frame = ExecutionFrame(
                return_address=self.pc + 1,
                local_vars=self.locals.copy(),
                stack_base=len(self.stack),
            )
            self.call_stack.append(frame)
            
            # Set up new locals with arguments
            self.locals = {}
            # TODO: Map arguments to parameter names
            
            # Jump to function
            self.pc = self.module.labels[label]
        else:
            # Try to find in globals
            if func_name in self.globals:
                func = self.globals[func_name]
                if callable(func):
                    result = func(*args)
                    self.stack.append(result)
                    self.pc += 1
                    return
            
            raise NameError(f"Undefined function: {func_name}")
    
    def _exec_RETURN(self, instr: IRInstruction) -> None:
        if not self.call_stack:
            # Top-level return - halt
            self.halted = True
            return
        
        # Get return value
        return_value = self.stack.pop() if self.stack else None
        
        # Restore call frame
        frame = self.call_stack.pop()
        self.locals = frame.local_vars
        
        # Clear stack to base
        while len(self.stack) > frame.stack_base:
            self.stack.pop()
        
        # Push return value
        self.stack.append(return_value)
        
        # Jump to return address
        self.pc = frame.return_address
    
    # Collections
    def _exec_BUILD_LIST(self, instr: IRInstruction) -> None:
        count = instr.operands[0] if instr.operands else 0
        items = [self.stack.pop() for _ in range(count)]
        items.reverse()
        self.stack.append(items)
    
    def _exec_BUILD_TUPLE(self, instr: IRInstruction) -> None:
        count = instr.operands[0] if instr.operands else 0
        items = [self.stack.pop() for _ in range(count)]
        items.reverse()
        self.stack.append(tuple(items))
    
    def _exec_BUILD_SET(self, instr: IRInstruction) -> None:
        count = instr.operands[0] if instr.operands else 0
        items = [self.stack.pop() for _ in range(count)]
        self.stack.append(set(items))
    
    def _exec_BUILD_DICT(self, instr: IRInstruction) -> None:
        count = instr.operands[0] if instr.operands else 0
        d = {}
        for _ in range(count):
            value = self.stack.pop()
            key = self.stack.pop()
            d[key] = value
        self.stack.append(d)
    
    def _exec_SUBSCRIPT(self, instr: IRInstruction) -> None:
        index = self.stack.pop()
        obj = self.stack.pop()
        self.stack.append(obj[index])
    
    def _exec_STORE_SUBSCRIPT(self, instr: IRInstruction) -> None:
        obj = self.stack.pop()
        index = self.stack.pop()
        value = self.stack.pop()
        obj[index] = value
        self.stack.append(obj)
    
    # Iteration
    def _exec_GET_ITER(self, instr: IRInstruction) -> None:
        obj = self.stack.pop()
        self.stack.append(iter(obj))
    
    def _exec_FOR_ITER(self, instr: IRInstruction) -> None:
        it = self.stack.pop()
        try:
            value = next(it)
            self.stack.append(it)  # Put iterator back
            self.stack.append(value)
            self.stack.append(True)  # Continue flag
        except StopIteration:
            self.stack.append(False)  # Stop flag
    
    # Assertions
    def _exec_ASSERT(self, instr: IRInstruction) -> None:
        axiom = instr.operands[0] if instr.operands else ""
        cond = self.stack.pop()
        if not cond:
            raise AssertionError(f"Assertion failed: {axiom}")
    
    def _exec_LASSERT(self, instr: IRInstruction) -> None:
        # Logical assert - same as ASSERT for now
        self._exec_ASSERT(instr)
    
    # Information revelation
    def _exec_EMIT(self, instr: IRInstruction) -> None:
        value = self.stack[-1] if self.stack else None
        # μ-cost charged in estimate_mu_cost
        print(f"EMIT: {value}")
    
    def _exec_REVEAL(self, instr: IRInstruction) -> None:
        value = self.stack[-1] if self.stack else None
        # μ-cost charged in estimate_mu_cost (information bits)
        print(f"REVEAL: {value}")
    
    # Partition operations (delegated to VM state)
    def _exec_PARTITION_NEW(self, instr: IRInstruction) -> None:
        region = instr.operands[0] if instr.operands else {1}
        self.stack.append(region)
    
    def _exec_PARTITION_SPLIT(self, instr: IRInstruction) -> None:
        # TODO: Integrate with VM partition state
        self.stack.append((set(), set()))
    
    def _exec_PARTITION_MERGE(self, instr: IRInstruction) -> None:
        # TODO: Integrate with VM partition state
        p2 = self.stack.pop()
        p1 = self.stack.pop()
        self.stack.append(p1 | p2 if isinstance(p1, set) and isinstance(p2, set) else p1)


def execute_ir(module: IRModule, builtins: Optional[Dict[str, Any]] = None) -> ExecutionResult:
    """
    Execute an IR module and return the result with μ-cost tracking.
    
    This is the main entry point for IR execution.
    """
    executor = IRExecutor(module, builtins)
    return executor.execute()
