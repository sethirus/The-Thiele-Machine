"""
Source Mapping for Thiele DSL

Provides bidirectional mapping between Python AST and Thiele IR.
This enables:
1. Tracing from IR execution back to Python source code
2. Mapping Python errors to IR instruction locations
3. Debugging IR execution with source context
4. Verifying that IR semantics match Python semantics
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Tuple, Set
import ast

from .ir import IRModule, IRInstruction, SourceLocation


@dataclass
class SourceSpan:
    """A span in source code with start and end positions."""
    filename: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    
    def contains(self, line: int, col: int) -> bool:
        """Check if a position is within this span."""
        if line < self.start_line or line > self.end_line:
            return False
        if line == self.start_line and col < self.start_col:
            return False
        if line == self.end_line and col > self.end_col:
            return False
        return True
    
    def overlaps(self, other: SourceSpan) -> bool:
        """Check if this span overlaps with another."""
        if self.filename != other.filename:
            return False
        # No overlap if one ends before other starts
        if self.end_line < other.start_line:
            return False
        if other.end_line < self.start_line:
            return False
        return True
    
    @classmethod
    def from_location(cls, loc: SourceLocation) -> SourceSpan:
        return cls(
            filename=loc.filename,
            start_line=loc.lineno,
            start_col=loc.col_offset,
            end_line=loc.end_lineno,
            end_col=loc.end_col_offset,
        )


@dataclass
class SourceMapping:
    """Maps a single IR instruction to its source location."""
    ir_index: int
    source_span: SourceSpan
    ast_node_type: str  # e.g., "BinOp", "Call", "Name"
    comment: str = ""


@dataclass
class SourceMap:
    """
    Bidirectional mapping between Python source and Thiele IR.
    
    This is the key component for verification - it allows tracing
    from any IR instruction back to the Python code that generated it,
    and vice versa.
    """
    source_code: str
    filename: str
    
    # IR index → source mapping
    ir_to_source: Dict[int, SourceMapping] = field(default_factory=dict)
    
    # Source line → IR indices (one line can map to multiple instructions)
    source_to_ir: Dict[int, List[int]] = field(default_factory=dict)
    
    # AST node ID → IR indices
    ast_to_ir: Dict[int, List[int]] = field(default_factory=dict)
    
    def add_mapping(self, ir_index: int, source: SourceLocation, ast_node_type: str, comment: str = "") -> None:
        """Add a mapping from IR instruction to source."""
        span = SourceSpan.from_location(source)
        mapping = SourceMapping(
            ir_index=ir_index,
            source_span=span,
            ast_node_type=ast_node_type,
            comment=comment,
        )
        
        self.ir_to_source[ir_index] = mapping
        
        # Add reverse mapping for all lines in span
        for line in range(span.start_line, span.end_line + 1):
            if line not in self.source_to_ir:
                self.source_to_ir[line] = []
            self.source_to_ir[line].append(ir_index)
    
    def get_source_for_ir(self, ir_index: int) -> Optional[SourceMapping]:
        """Get source mapping for an IR instruction."""
        return self.ir_to_source.get(ir_index)
    
    def get_ir_for_line(self, line: int) -> List[int]:
        """Get IR instruction indices for a source line."""
        return self.source_to_ir.get(line, [])
    
    def get_source_text(self, span: SourceSpan) -> str:
        """Extract source text for a span."""
        lines = self.source_code.split('\n')
        if span.start_line == span.end_line:
            if 0 <= span.start_line - 1 < len(lines):
                return lines[span.start_line - 1][span.start_col:span.end_col]
        
        result = []
        for i in range(span.start_line - 1, min(span.end_line, len(lines))):
            line = lines[i]
            if i == span.start_line - 1:
                result.append(line[span.start_col:])
            elif i == span.end_line - 1:
                result.append(line[:span.end_col])
            else:
                result.append(line)
        return '\n'.join(result)
    
    def format_trace_entry(self, ir_index: int, instr: IRInstruction) -> str:
        """Format a trace entry with source context."""
        mapping = self.get_source_for_ir(ir_index)
        if not mapping:
            return f"  {ir_index:4d}: {instr.opcode.name} (no source)"
        
        source_text = self.get_source_text(mapping.source_span)
        if len(source_text) > 40:
            source_text = source_text[:37] + "..."
        
        return (
            f"  {ir_index:4d}: {instr.opcode.name:15s} "
            f"L{mapping.source_span.start_line}: {source_text!r}"
        )
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'filename': self.filename,
            'mappings': {
                str(k): {
                    'ir_index': v.ir_index,
                    'span': {
                        'start_line': v.source_span.start_line,
                        'start_col': v.source_span.start_col,
                        'end_line': v.source_span.end_line,
                        'end_col': v.source_span.end_col,
                    },
                    'ast_type': v.ast_node_type,
                    'comment': v.comment,
                }
                for k, v in self.ir_to_source.items()
            },
        }


def create_sourcemap(module: IRModule) -> SourceMap:
    """
    Create a source map from a compiled IR module.
    
    Extracts source locations from IR instructions and builds
    the bidirectional mapping.
    """
    sourcemap = SourceMap(
        source_code=module.source_code,
        filename=module.filename,
    )
    
    for idx, instr in enumerate(module.instructions):
        if instr.source:
            # Determine AST node type from opcode
            ast_type = _opcode_to_ast_type(instr.opcode)
            sourcemap.add_mapping(
                ir_index=idx,
                source=instr.source,
                ast_node_type=ast_type,
                comment=instr.comment,
            )
    
    return sourcemap


def _opcode_to_ast_type(opcode) -> str:
    """Map IR opcode to likely AST node type."""
    from .ir import IROpcode
    
    mapping = {
        IROpcode.LOAD_CONST: "Constant",
        IROpcode.LOAD_VAR: "Name",
        IROpcode.STORE_VAR: "Assign",
        IROpcode.ADD: "BinOp",
        IROpcode.SUB: "BinOp",
        IROpcode.MUL: "BinOp",
        IROpcode.DIV: "BinOp",
        IROpcode.MOD: "BinOp",
        IROpcode.POW: "BinOp",
        IROpcode.BIT_AND: "BinOp",
        IROpcode.BIT_OR: "BinOp",
        IROpcode.BIT_XOR: "BinOp",
        IROpcode.EQ: "Compare",
        IROpcode.NE: "Compare",
        IROpcode.LT: "Compare",
        IROpcode.LE: "Compare",
        IROpcode.GT: "Compare",
        IROpcode.GE: "Compare",
        IROpcode.BOOL_AND: "BoolOp",
        IROpcode.BOOL_OR: "BoolOp",
        IROpcode.BOOL_NOT: "UnaryOp",
        IROpcode.CALL: "Call",
        IROpcode.RETURN: "Return",
        IROpcode.JUMP_IF_TRUE: "If",
        IROpcode.JUMP_IF_FALSE: "If",
        IROpcode.BUILD_LIST: "List",
        IROpcode.BUILD_TUPLE: "Tuple",
        IROpcode.BUILD_DICT: "Dict",
        IROpcode.BUILD_SET: "Set",
        IROpcode.SUBSCRIPT: "Subscript",
        IROpcode.ASSERT: "Assert",
    }
    return mapping.get(opcode, "Unknown")


@dataclass
class VerificationLink:
    """
    Link between Python semantics and IR execution.
    
    This is used to verify that IR execution produces the same
    results as Python execution for the same source code.
    """
    source_span: SourceSpan
    ir_indices: List[int]
    python_value: Any = None
    ir_value: Any = None
    verified: bool = False
    error: Optional[str] = None


class BidirectionalLinker:
    """
    Creates bidirectional links between Python and IR execution.
    
    This enables verification by running both Python and IR, then
    comparing results at each link point.
    """
    
    def __init__(self, source_code: str, module: IRModule):
        self.source_code = source_code
        self.module = module
        self.sourcemap = create_sourcemap(module)
        self.links: List[VerificationLink] = []
    
    def create_verification_points(self) -> List[VerificationLink]:
        """
        Create verification points at significant locations.
        
        A verification point is where Python and IR execution
        should produce equivalent values.
        """
        links = []
        
        # Find all assignments (these are verification points)
        for idx, instr in enumerate(self.module.instructions):
            from .ir import IROpcode
            if instr.opcode == IROpcode.STORE_VAR and instr.source:
                span = SourceSpan.from_location(instr.source)
                link = VerificationLink(
                    source_span=span,
                    ir_indices=[idx],
                )
                links.append(link)
        
        self.links = links
        return links
    
    def verify_link(self, link: VerificationLink, python_value: Any, ir_value: Any) -> bool:
        """Verify that Python and IR values match at a link point."""
        link.python_value = python_value
        link.ir_value = ir_value
        
        try:
            # Handle special cases for comparison
            if python_value == ir_value:
                link.verified = True
            elif isinstance(python_value, float) and isinstance(ir_value, float):
                # Float tolerance
                link.verified = abs(python_value - ir_value) < 1e-10
            else:
                link.verified = False
                link.error = f"Value mismatch: Python={python_value}, IR={ir_value}"
        except Exception as e:
            link.verified = False
            link.error = str(e)
        
        return link.verified
    
    def get_verification_report(self) -> Dict[str, Any]:
        """Generate a report of verification status."""
        total = len(self.links)
        verified = sum(1 for link in self.links if link.verified)
        failed = sum(1 for link in self.links if not link.verified and link.python_value is not None)
        pending = total - verified - failed
        
        return {
            'total_links': total,
            'verified': verified,
            'failed': failed,
            'pending': pending,
            'failures': [
                {
                    'line': link.source_span.start_line,
                    'python_value': repr(link.python_value),
                    'ir_value': repr(link.ir_value),
                    'error': link.error,
                }
                for link in self.links
                if not link.verified and link.error
            ],
        }
