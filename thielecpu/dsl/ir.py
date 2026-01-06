"""
Thiele DSL Intermediate Representation (IR)

The IR serves as the bridge between Python AST and Thiele VM opcodes.
Each IR instruction maps to one or more VM operations with tracked μ-cost.

Design Principles:
1. Every Python operation has a μ-cost (no free lunches)
2. Source locations are preserved for bidirectional mapping
3. IR can be serialized for inspection/debugging
4. IR encodes information theory - description bits + entropy bits
"""

from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Dict, Any, Optional, Tuple, Union
import ast
import math


class IROpcode(Enum):
    """
    Thiele IR Opcodes - a semantic layer above the raw VM opcodes.
    
    These opcodes capture Python semantics while being directly mappable
    to Thiele VM instructions. Each opcode has an associated μ-cost formula.
    """
    # ═══════════════════════════════════════════════════════════════════
    # PARTITION OPERATIONS (discovery μ-cost: popcount of mask)
    # ═══════════════════════════════════════════════════════════════════
    PARTITION_NEW = auto()      # Create new module/partition
    PARTITION_SPLIT = auto()    # Split partition by predicate
    PARTITION_MERGE = auto()    # Merge two partitions
    
    # ═══════════════════════════════════════════════════════════════════
    # DATA OPERATIONS (execution μ-cost: log2(domain_size))
    # ═══════════════════════════════════════════════════════════════════
    LOAD_CONST = auto()         # Push constant to stack
    LOAD_VAR = auto()           # Load variable from scope
    STORE_VAR = auto()          # Store value to variable
    
    # ═══════════════════════════════════════════════════════════════════
    # ARITHMETIC (execution μ-cost: bit_length of operands)
    # ═══════════════════════════════════════════════════════════════════
    ADD = auto()
    SUB = auto()
    MUL = auto()
    DIV = auto()
    MOD = auto()
    POW = auto()
    NEG = auto()
    
    # ═══════════════════════════════════════════════════════════════════
    # BITWISE (execution μ-cost: max bit_length)
    # ═══════════════════════════════════════════════════════════════════
    BIT_AND = auto()
    BIT_OR = auto()
    BIT_XOR = auto()
    BIT_NOT = auto()
    LSHIFT = auto()
    RSHIFT = auto()
    
    # ═══════════════════════════════════════════════════════════════════
    # COMPARISON (execution μ-cost: comparison bits)
    # ═══════════════════════════════════════════════════════════════════
    EQ = auto()
    NE = auto()
    LT = auto()
    LE = auto()
    GT = auto()
    GE = auto()
    
    # ═══════════════════════════════════════════════════════════════════
    # LOGICAL (execution μ-cost: 1 bit per operand)
    # ═══════════════════════════════════════════════════════════════════
    BOOL_AND = auto()
    BOOL_OR = auto()
    BOOL_NOT = auto()
    
    # ═══════════════════════════════════════════════════════════════════
    # CONTROL FLOW (execution μ-cost: log2(branches) per decision)
    # ═══════════════════════════════════════════════════════════════════
    JUMP = auto()               # Unconditional jump
    JUMP_IF_TRUE = auto()       # Conditional branch
    JUMP_IF_FALSE = auto()      # Conditional branch
    
    # ═══════════════════════════════════════════════════════════════════
    # FUNCTION OPERATIONS (mixed μ-cost)
    # ═══════════════════════════════════════════════════════════════════
    CALL = auto()               # Call function (μ = arg_count + return_bits)
    RETURN = auto()             # Return from function (μ = return_bits)
    
    # ═══════════════════════════════════════════════════════════════════
    # COLLECTION OPERATIONS (μ-cost: size * element_bits)
    # ═══════════════════════════════════════════════════════════════════
    BUILD_LIST = auto()         # Build list from stack items
    BUILD_TUPLE = auto()        # Build tuple from stack items
    BUILD_SET = auto()          # Build set from stack items
    BUILD_DICT = auto()         # Build dict from stack items
    SUBSCRIPT = auto()          # Get item by index
    STORE_SUBSCRIPT = auto()    # Set item by index
    
    # ═══════════════════════════════════════════════════════════════════
    # ITERATION (μ-cost: log2(collection_size) per iteration)
    # ═══════════════════════════════════════════════════════════════════
    GET_ITER = auto()           # Get iterator from iterable
    FOR_ITER = auto()           # Advance iterator
    
    # ═══════════════════════════════════════════════════════════════════
    # ASSERTION & PROOF (discovery μ-cost: axiom_bitlength)
    # ═══════════════════════════════════════════════════════════════════
    ASSERT = auto()             # Assert condition (creates axiom)
    LASSERT = auto()            # Logical assert with SAT check
    
    # ═══════════════════════════════════════════════════════════════════
    # INFORMATION REVELATION (information μ-cost: revealed bits)
    # ═══════════════════════════════════════════════════════════════════
    EMIT = auto()               # Emit value to output
    REVEAL = auto()             # Explicitly reveal information
    
    # ═══════════════════════════════════════════════════════════════════
    # SPECIAL
    # ═══════════════════════════════════════════════════════════════════
    NOP = auto()                # No operation (μ = 0)
    HALT = auto()               # Halt execution


@dataclass(frozen=True)
class SourceLocation:
    """
    Location in Python source code for bidirectional mapping.
    
    This enables tracing from Thiele execution back to Python code
    and vice versa.
    """
    filename: str
    lineno: int
    col_offset: int
    end_lineno: int
    end_col_offset: int
    
    @classmethod
    def from_ast_node(cls, node: ast.AST, filename: str = "<source>") -> SourceLocation:
        """Create SourceLocation from an AST node."""
        return cls(
            filename=filename,
            lineno=getattr(node, 'lineno', 0),
            col_offset=getattr(node, 'col_offset', 0),
            end_lineno=getattr(node, 'end_lineno', getattr(node, 'lineno', 0)),
            end_col_offset=getattr(node, 'end_col_offset', getattr(node, 'col_offset', 0)),
        )
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'filename': self.filename,
            'lineno': self.lineno,
            'col_offset': self.col_offset,
            'end_lineno': self.end_lineno,
            'end_col_offset': self.end_col_offset,
        }


@dataclass
class IRInstruction:
    """
    A single IR instruction with source mapping and μ-cost annotation.
    
    The μ-cost is split into:
    - discovery_cost: Cost of learning structure (popcount-based)
    - execution_cost: Cost of performing computation (bit-based)
    """
    opcode: IROpcode
    operands: Tuple[Any, ...] = field(default_factory=tuple)
    source: Optional[SourceLocation] = None
    
    # Computed μ-costs (set during execution or estimation)
    discovery_cost: int = 0
    execution_cost: int = 0
    
    # Additional metadata
    comment: str = ""
    
    @property
    def total_mu_cost(self) -> int:
        """Total μ-cost = discovery + execution"""
        return self.discovery_cost + self.execution_cost
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'opcode': self.opcode.name,
            'operands': list(self.operands),
            'source': self.source.to_dict() if self.source else None,
            'discovery_cost': self.discovery_cost,
            'execution_cost': self.execution_cost,
            'comment': self.comment,
        }
    
    def __repr__(self) -> str:
        ops = ', '.join(str(o) for o in self.operands)
        cost = f"μ={self.total_mu_cost}" if self.total_mu_cost else ""
        loc = f"@L{self.source.lineno}" if self.source else ""
        return f"IRInstruction({self.opcode.name} {ops} {cost}{loc})"


def estimate_mu_cost(opcode: IROpcode, operands: Tuple[Any, ...]) -> Tuple[int, int]:
    """
    Estimate μ-cost for an opcode before execution.
    
    Returns (discovery_cost, execution_cost).
    
    This implements the thesis cost model:
    - Discovery μ = popcount of partition mask (PNEW)
    - Execution μ = log2(domain_before / domain_after) bits
    """
    discovery = 0
    execution = 0
    
    # Partition operations
    if opcode == IROpcode.PARTITION_NEW:
        # Discovery cost is popcount of the region mask
        region = operands[0] if operands else {1}
        if isinstance(region, set):
            discovery = len(region)
        else:
            discovery = bin(int(region)).count('1')
    
    elif opcode == IROpcode.PARTITION_SPLIT:
        # Execution cost depends on partition size
        # TODO: Get from actual partition
        execution = 8  # Default: log2(256) bits
    
    elif opcode == IROpcode.PARTITION_MERGE:
        execution = 1  # Merge is cheap
    
    # Arithmetic - cost based on operand bit lengths
    elif opcode in (IROpcode.ADD, IROpcode.SUB):
        for op in operands:
            if isinstance(op, int):
                execution += max(1, op.bit_length())
            else:
                execution += 32  # Default 32-bit cost
    
    elif opcode == IROpcode.MUL:
        # Multiplication is quadratic in bit length
        bits = [max(1, op.bit_length()) if isinstance(op, int) else 32 for op in operands]
        if len(bits) >= 2:
            execution = bits[0] * bits[1]
        else:
            execution = 32
    
    elif opcode == IROpcode.DIV:
        # Division is similar to multiplication
        bits = [max(1, op.bit_length()) if isinstance(op, int) else 32 for op in operands]
        if len(bits) >= 2:
            execution = bits[0] * bits[1]
        else:
            execution = 32
    
    elif opcode == IROpcode.POW:
        # Exponentiation: base^exp requires exp * log2(base) bits
        if len(operands) >= 2:
            base, exp = operands[0], operands[1]
            base_bits = max(1, base.bit_length()) if isinstance(base, int) else 32
            exp_val = exp if isinstance(exp, int) else 32
            execution = min(base_bits * exp_val, 2**20)  # Cap at 1M
        else:
            execution = 64
    
    # Bitwise - max bit length
    elif opcode in (IROpcode.BIT_AND, IROpcode.BIT_OR, IROpcode.BIT_XOR):
        max_bits = 0
        for op in operands:
            if isinstance(op, int):
                max_bits = max(max_bits, op.bit_length())
            else:
                max_bits = max(max_bits, 32)
        execution = max_bits if max_bits > 0 else 32
    
    # Comparison - 1 bit result
    elif opcode in (IROpcode.EQ, IROpcode.NE, IROpcode.LT, IROpcode.LE, IROpcode.GT, IROpcode.GE):
        execution = 1  # Boolean result
    
    # Logical - 1 bit per operand
    elif opcode in (IROpcode.BOOL_AND, IROpcode.BOOL_OR, IROpcode.BOOL_NOT):
        execution = len(operands) if operands else 1
    
    # Control flow - log2(branches)
    elif opcode in (IROpcode.JUMP_IF_TRUE, IROpcode.JUMP_IF_FALSE):
        execution = 1  # 1 bit for binary branch
    
    elif opcode == IROpcode.JUMP:
        execution = 0  # Unconditional is free
    
    # Function calls
    elif opcode == IROpcode.CALL:
        # Cost = arg count + overhead
        arg_count = operands[1] if len(operands) > 1 else 0
        execution = 8 + arg_count  # Base overhead + args
    
    elif opcode == IROpcode.RETURN:
        execution = 8  # Return value encoding
    
    # Collections - size * element estimate
    elif opcode in (IROpcode.BUILD_LIST, IROpcode.BUILD_TUPLE, IROpcode.BUILD_SET):
        size = operands[0] if operands else 0
        execution = size * 8  # 8 bits per element average
    
    elif opcode == IROpcode.BUILD_DICT:
        size = operands[0] if operands else 0
        execution = size * 16  # Key + value
    
    # Load/Store
    elif opcode in (IROpcode.LOAD_CONST, IROpcode.LOAD_VAR):
        value = operands[0] if operands else 0
        if isinstance(value, int):
            execution = max(1, value.bit_length())
        elif isinstance(value, str):
            execution = len(value) * 8
        else:
            execution = 32
    
    elif opcode == IROpcode.STORE_VAR:
        execution = 8  # Storage overhead
    
    # Information revelation
    elif opcode in (IROpcode.EMIT, IROpcode.REVEAL):
        # Cost is the revealed information
        if operands:
            value = operands[0]
            if isinstance(value, int):
                execution = max(1, value.bit_length())
            elif isinstance(value, str):
                execution = len(value) * 8
            else:
                execution = 32
        else:
            execution = 8
    
    # Assert - discovery cost
    elif opcode in (IROpcode.ASSERT, IROpcode.LASSERT):
        # Assertion creates an axiom
        if operands and isinstance(operands[0], str):
            discovery = len(operands[0].encode('utf-8')) * 8
        else:
            discovery = 64
    
    return discovery, execution


@dataclass
class IRModule:
    """
    A compiled IR module containing instructions and metadata.
    
    This is the output of Python → IR compilation.
    """
    instructions: List[IRInstruction] = field(default_factory=list)
    source_code: str = ""
    filename: str = "<source>"
    
    # Symbol table for variables
    local_vars: Dict[str, int] = field(default_factory=dict)
    global_vars: Dict[str, int] = field(default_factory=dict)
    
    # Jump targets (label → instruction index)
    labels: Dict[str, int] = field(default_factory=dict)
    
    # Total estimated μ-cost
    estimated_discovery_cost: int = 0
    estimated_execution_cost: int = 0
    
    def add_instruction(self, instr: IRInstruction) -> int:
        """Add instruction and return its index."""
        idx = len(self.instructions)
        self.instructions.append(instr)
        
        # Update cost estimates
        d, e = estimate_mu_cost(instr.opcode, instr.operands)
        instr.discovery_cost = d
        instr.execution_cost = e
        self.estimated_discovery_cost += d
        self.estimated_execution_cost += e
        
        return idx
    
    def add_label(self, name: str) -> None:
        """Mark current position as a jump target."""
        self.labels[name] = len(self.instructions)
    
    def patch_jump(self, instr_idx: int, target_label: str) -> None:
        """Patch a jump instruction with the resolved target."""
        if target_label in self.labels:
            target = self.labels[target_label]
            instr = self.instructions[instr_idx]
            # Replace target placeholder with actual index
            self.instructions[instr_idx] = IRInstruction(
                opcode=instr.opcode,
                operands=(target,),
                source=instr.source,
                discovery_cost=instr.discovery_cost,
                execution_cost=instr.execution_cost,
                comment=instr.comment,
            )
    
    @property
    def total_estimated_mu_cost(self) -> int:
        return self.estimated_discovery_cost + self.estimated_execution_cost
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'source_code': self.source_code,
            'filename': self.filename,
            'instructions': [i.to_dict() for i in self.instructions],
            'local_vars': self.local_vars,
            'global_vars': self.global_vars,
            'labels': self.labels,
            'estimated_discovery_cost': self.estimated_discovery_cost,
            'estimated_execution_cost': self.estimated_execution_cost,
        }
    
    def disassemble(self) -> str:
        """Generate human-readable disassembly."""
        lines = [
            f"# Thiele IR Module: {self.filename}",
            f"# Estimated μ-cost: {self.total_estimated_mu_cost} "
            f"(discovery={self.estimated_discovery_cost}, execution={self.estimated_execution_cost})",
            f"# Instructions: {len(self.instructions)}",
            "",
        ]
        
        # Create label index for display
        label_at = {v: k for k, v in self.labels.items()}
        
        for i, instr in enumerate(self.instructions):
            # Check for label
            if i in label_at:
                lines.append(f"{label_at[i]}:")
            
            # Format instruction
            ops = ', '.join(repr(o) if isinstance(o, str) else str(o) for o in instr.operands)
            cost = f"  ; μ={instr.total_mu_cost}" if instr.total_mu_cost else ""
            loc = f" @L{instr.source.lineno}" if instr.source else ""
            comment = f"  # {instr.comment}" if instr.comment else ""
            
            lines.append(f"  {i:4d}: {instr.opcode.name:20s} {ops}{cost}{loc}{comment}")
        
        return "\n".join(lines)


# Type alias for the full IR
ThieleIR = IRModule
