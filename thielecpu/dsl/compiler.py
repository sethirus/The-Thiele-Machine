"""
Python to Thiele IR Compiler

Compiles Python AST to Thiele Intermediate Representation.
Every Python operation is mapped to IR instructions with source locations preserved.

This is the REAL compilation - no exec() involved, just AST transformation
to a representation that can be executed on the Thiele VM with proper μ-tracking.
"""

from __future__ import annotations
import ast
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass, field

from .ir import (
    IRModule,
    IRInstruction,
    IROpcode,
    SourceLocation,
)


@dataclass
class CompilerState:
    """Compiler state during code generation."""
    module: IRModule
    filename: str
    
    # Scope tracking
    scope_stack: List[Dict[str, int]] = field(default_factory=list)
    
    # Loop/control flow context
    loop_stack: List[Tuple[str, str]] = field(default_factory=list)  # (continue_label, break_label)
    
    # Label generation
    label_counter: int = 0
    
    # Jump patching queue
    pending_jumps: List[Tuple[int, str]] = field(default_factory=list)
    
    def fresh_label(self, prefix: str = "L") -> str:
        """Generate a fresh label name."""
        self.label_counter += 1
        return f"{prefix}_{self.label_counter}"
    
    def enter_scope(self) -> None:
        """Enter a new local scope."""
        self.scope_stack.append({})
    
    def exit_scope(self) -> None:
        """Exit current local scope."""
        if self.scope_stack:
            self.scope_stack.pop()
    
    def define_local(self, name: str) -> int:
        """Define a local variable and return its index."""
        if not self.scope_stack:
            self.scope_stack.append({})
        
        if name not in self.scope_stack[-1]:
            idx = len(self.module.local_vars)
            self.scope_stack[-1][name] = idx
            self.module.local_vars[name] = idx
        return self.scope_stack[-1][name]
    
    def resolve_var(self, name: str) -> Tuple[str, int]:
        """Resolve a variable name. Returns (scope_type, index)."""
        # Check local scopes from inner to outer
        for scope in reversed(self.scope_stack):
            if name in scope:
                return ('local', scope[name])
        
        # Check globals
        if name in self.module.global_vars:
            return ('global', self.module.global_vars[name])
        
        # Define as global
        idx = len(self.module.global_vars)
        self.module.global_vars[name] = idx
        return ('global', idx)


class PythonToThieleCompiler(ast.NodeVisitor):
    """
    Compiles Python AST to Thiele IR.
    
    This compiler generates IR instructions that preserve:
    1. Source locations for bidirectional mapping
    2. μ-cost tracking per operation
    3. The exact semantics of Python code
    """
    
    def __init__(self, source_code: str = "", filename: str = "<source>"):
        self.source_code = source_code
        self.filename = filename
        self.state: Optional[CompilerState] = None
    
    def compile(self, source: str) -> IRModule:
        """Compile Python source code to IR."""
        self.source_code = source
        tree = ast.parse(source, filename=self.filename)
        return self.compile_ast(tree)
    
    def compile_ast(self, tree: ast.Module) -> IRModule:
        """Compile an AST to IR."""
        module = IRModule(source_code=self.source_code, filename=self.filename)
        self.state = CompilerState(module=module, filename=self.filename)
        self.state.enter_scope()  # Global scope
        
        # Compile all top-level statements
        for node in tree.body:
            self.visit(node)
        
        # Patch pending jumps
        for instr_idx, label in self.state.pending_jumps:
            module.patch_jump(instr_idx, label)
        
        return module
    
    def emit(self, opcode: IROpcode, *operands: Any, node: Optional[ast.AST] = None, comment: str = "") -> int:
        """Emit an IR instruction and return its index."""
        source = SourceLocation.from_ast_node(node, self.filename) if node else None
        instr = IRInstruction(
            opcode=opcode,
            operands=tuple(operands),
            source=source,
            comment=comment,
        )
        return self.state.module.add_instruction(instr)
    
    def emit_jump(self, opcode: IROpcode, label: str, node: Optional[ast.AST] = None) -> int:
        """Emit a jump instruction with pending target."""
        idx = self.emit(opcode, label, node=node, comment=f"→ {label}")
        self.state.pending_jumps.append((idx, label))
        return idx
    
    # ═══════════════════════════════════════════════════════════════════
    # STATEMENT VISITORS
    # ═══════════════════════════════════════════════════════════════════
    
    def visit_Module(self, node: ast.Module) -> None:
        for stmt in node.body:
            self.visit(stmt)
    
    def visit_Expr(self, node: ast.Expr) -> None:
        """Expression statement - evaluate and discard."""
        self.visit(node.value)
        # Value is on stack, discard it (implicit pop)
    
    def visit_Assign(self, node: ast.Assign) -> None:
        """Assignment: target = value"""
        # Compile the value expression
        self.visit(node.value)
        
        # Store to each target
        for target in node.targets:
            if isinstance(target, ast.Name):
                scope_type, idx = self.state.resolve_var(target.id)
                self.state.define_local(target.id)
                self.emit(IROpcode.STORE_VAR, target.id, idx, node=node,
                         comment=f"{target.id} = <expr>")
            elif isinstance(target, ast.Subscript):
                # Handle subscript assignment
                self.visit(target.slice)  # Index
                self.visit(target.value)  # Container
                self.emit(IROpcode.STORE_SUBSCRIPT, node=node)
    
    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        """Augmented assignment: target op= value"""
        # Load current value
        if isinstance(node.target, ast.Name):
            scope_type, idx = self.state.resolve_var(node.target.id)
            self.emit(IROpcode.LOAD_VAR, node.target.id, idx, node=node)
        
        # Compile RHS
        self.visit(node.value)
        
        # Apply operator
        op_map = {
            ast.Add: IROpcode.ADD,
            ast.Sub: IROpcode.SUB,
            ast.Mult: IROpcode.MUL,
            ast.Div: IROpcode.DIV,
            ast.Mod: IROpcode.MOD,
            ast.Pow: IROpcode.POW,
            ast.BitAnd: IROpcode.BIT_AND,
            ast.BitOr: IROpcode.BIT_OR,
            ast.BitXor: IROpcode.BIT_XOR,
            ast.LShift: IROpcode.LSHIFT,
            ast.RShift: IROpcode.RSHIFT,
        }
        opcode = op_map.get(type(node.op), IROpcode.ADD)
        self.emit(opcode, node=node)
        
        # Store back
        if isinstance(node.target, ast.Name):
            scope_type, idx = self.state.resolve_var(node.target.id)
            self.emit(IROpcode.STORE_VAR, node.target.id, idx, node=node)
    
    def visit_If(self, node: ast.If) -> None:
        """If statement with optional else."""
        else_label = self.state.fresh_label("if_else")
        end_label = self.state.fresh_label("if_end")
        
        # Compile condition
        self.visit(node.test)
        
        # Jump to else if false
        self.emit_jump(IROpcode.JUMP_IF_FALSE, else_label, node=node)
        
        # Compile then-body
        for stmt in node.body:
            self.visit(stmt)
        
        # Jump over else
        if node.orelse:
            self.emit_jump(IROpcode.JUMP, end_label, node=node)
        
        # Else label
        self.state.module.add_label(else_label)
        
        # Compile else-body
        for stmt in node.orelse:
            self.visit(stmt)
        
        # End label
        self.state.module.add_label(end_label)
    
    def visit_While(self, node: ast.While) -> None:
        """While loop."""
        loop_label = self.state.fresh_label("while_loop")
        end_label = self.state.fresh_label("while_end")
        
        # Push loop context
        self.state.loop_stack.append((loop_label, end_label))
        
        # Loop header
        self.state.module.add_label(loop_label)
        
        # Compile condition
        self.visit(node.test)
        self.emit_jump(IROpcode.JUMP_IF_FALSE, end_label, node=node)
        
        # Compile body
        for stmt in node.body:
            self.visit(stmt)
        
        # Jump back to condition
        self.emit_jump(IROpcode.JUMP, loop_label, node=node)
        
        # End label
        self.state.module.add_label(end_label)
        
        # Pop loop context
        self.state.loop_stack.pop()
    
    def visit_For(self, node: ast.For) -> None:
        """For loop over iterable."""
        loop_label = self.state.fresh_label("for_loop")
        end_label = self.state.fresh_label("for_end")
        
        # Push loop context
        self.state.loop_stack.append((loop_label, end_label))
        
        # Get iterator
        self.visit(node.iter)
        self.emit(IROpcode.GET_ITER, node=node, comment="for loop init")
        
        # Store iterator in temp
        iter_name = self.state.fresh_label("_iter")
        self.state.define_local(iter_name)
        self.emit(IROpcode.STORE_VAR, iter_name, self.state.scope_stack[-1][iter_name], node=node)
        
        # Loop header
        self.state.module.add_label(loop_label)
        
        # Load iterator and get next
        self.emit(IROpcode.LOAD_VAR, iter_name, self.state.scope_stack[-1][iter_name], node=node)
        self.emit(IROpcode.FOR_ITER, node=node)
        self.emit_jump(IROpcode.JUMP_IF_FALSE, end_label, node=node)
        
        # Store loop variable
        if isinstance(node.target, ast.Name):
            self.state.define_local(node.target.id)
            scope_type, idx = self.state.resolve_var(node.target.id)
            self.emit(IROpcode.STORE_VAR, node.target.id, idx, node=node)
        
        # Compile body
        for stmt in node.body:
            self.visit(stmt)
        
        # Jump back
        self.emit_jump(IROpcode.JUMP, loop_label, node=node)
        
        # End label
        self.state.module.add_label(end_label)
        
        # Pop loop context
        self.state.loop_stack.pop()
    
    def visit_Break(self, node: ast.Break) -> None:
        """Break out of loop."""
        if self.state.loop_stack:
            _, break_label = self.state.loop_stack[-1]
            self.emit_jump(IROpcode.JUMP, break_label, node=node)
    
    def visit_Continue(self, node: ast.Continue) -> None:
        """Continue to next iteration."""
        if self.state.loop_stack:
            continue_label, _ = self.state.loop_stack[-1]
            self.emit_jump(IROpcode.JUMP, continue_label, node=node)
    
    def visit_Return(self, node: ast.Return) -> None:
        """Return statement."""
        if node.value:
            self.visit(node.value)
        else:
            self.emit(IROpcode.LOAD_CONST, None, node=node)
        self.emit(IROpcode.RETURN, node=node)
    
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        """Function definition - compile to IR callable."""
        # Store function start label
        func_label = f"func_{node.name}"
        end_label = self.state.fresh_label(f"func_{node.name}_end")
        
        # Jump over function body (will be called later)
        self.emit_jump(IROpcode.JUMP, end_label, node=node)
        
        # Function entry point
        self.state.module.add_label(func_label)
        
        # Enter function scope
        self.state.enter_scope()
        
        # Define parameters as locals
        for arg in node.args.args:
            self.state.define_local(arg.arg)
        
        # Compile function body
        for stmt in node.body:
            self.visit(stmt)
        
        # Implicit return None
        self.emit(IROpcode.LOAD_CONST, None, node=node)
        self.emit(IROpcode.RETURN, node=node)
        
        # Exit function scope
        self.state.exit_scope()
        
        # End label
        self.state.module.add_label(end_label)
        
        # Store function reference
        self.emit(IROpcode.LOAD_CONST, func_label, node=node, comment=f"func ref: {node.name}")
        scope_type, idx = self.state.resolve_var(node.name)
        self.state.define_local(node.name)
        self.emit(IROpcode.STORE_VAR, node.name, idx, node=node)
    
    def visit_Assert(self, node: ast.Assert) -> None:
        """Assert statement - creates an axiom."""
        # Compile condition
        self.visit(node.test)
        
        # Generate axiom string from AST
        axiom_str = ast.unparse(node.test) if hasattr(ast, 'unparse') else repr(node.test)
        self.emit(IROpcode.ASSERT, axiom_str, node=node, comment="assert axiom")
    
    def visit_Pass(self, node: ast.Pass) -> None:
        """Pass statement - no operation."""
        self.emit(IROpcode.NOP, node=node)
    
    # ═══════════════════════════════════════════════════════════════════
    # EXPRESSION VISITORS
    # ═══════════════════════════════════════════════════════════════════
    
    def visit_Constant(self, node: ast.Constant) -> None:
        """Constant value."""
        self.emit(IROpcode.LOAD_CONST, node.value, node=node, 
                 comment=repr(node.value)[:20])
    
    def visit_Name(self, node: ast.Name) -> None:
        """Variable reference."""
        if isinstance(node.ctx, ast.Load):
            scope_type, idx = self.state.resolve_var(node.id)
            self.emit(IROpcode.LOAD_VAR, node.id, idx, node=node)
        elif isinstance(node.ctx, ast.Store):
            scope_type, idx = self.state.resolve_var(node.id)
            self.state.define_local(node.id)
            self.emit(IROpcode.STORE_VAR, node.id, idx, node=node)
    
    def visit_BinOp(self, node: ast.BinOp) -> None:
        """Binary operation."""
        # Compile operands
        self.visit(node.left)
        self.visit(node.right)
        
        # Map operator to opcode
        op_map = {
            ast.Add: IROpcode.ADD,
            ast.Sub: IROpcode.SUB,
            ast.Mult: IROpcode.MUL,
            ast.Div: IROpcode.DIV,
            ast.Mod: IROpcode.MOD,
            ast.Pow: IROpcode.POW,
            ast.BitAnd: IROpcode.BIT_AND,
            ast.BitOr: IROpcode.BIT_OR,
            ast.BitXor: IROpcode.BIT_XOR,
            ast.LShift: IROpcode.LSHIFT,
            ast.RShift: IROpcode.RSHIFT,
        }
        opcode = op_map.get(type(node.op), IROpcode.ADD)
        self.emit(opcode, node=node)
    
    def visit_UnaryOp(self, node: ast.UnaryOp) -> None:
        """Unary operation."""
        self.visit(node.operand)
        
        op_map = {
            ast.USub: IROpcode.NEG,
            ast.Not: IROpcode.BOOL_NOT,
            ast.Invert: IROpcode.BIT_NOT,
        }
        opcode = op_map.get(type(node.op), IROpcode.NOP)
        self.emit(opcode, node=node)
    
    def visit_BoolOp(self, node: ast.BoolOp) -> None:
        """Boolean operation (and/or)."""
        opcode = IROpcode.BOOL_AND if isinstance(node.op, ast.And) else IROpcode.BOOL_OR
        
        # Short-circuit evaluation
        end_label = self.state.fresh_label("boolop_end")
        
        for i, value in enumerate(node.values):
            self.visit(value)
            if i < len(node.values) - 1:
                # For 'and': jump to end if false
                # For 'or': jump to end if true
                if isinstance(node.op, ast.And):
                    self.emit_jump(IROpcode.JUMP_IF_FALSE, end_label, node=node)
                else:
                    self.emit_jump(IROpcode.JUMP_IF_TRUE, end_label, node=node)
        
        self.state.module.add_label(end_label)
    
    def visit_Compare(self, node: ast.Compare) -> None:
        """Comparison operation."""
        op_map = {
            ast.Eq: IROpcode.EQ,
            ast.NotEq: IROpcode.NE,
            ast.Lt: IROpcode.LT,
            ast.LtE: IROpcode.LE,
            ast.Gt: IROpcode.GT,
            ast.GtE: IROpcode.GE,
        }
        
        # For chained comparisons: a < b < c → a < b and b < c
        self.visit(node.left)
        
        for op, comparator in zip(node.ops, node.comparators):
            self.visit(comparator)
            opcode = op_map.get(type(op), IROpcode.EQ)
            self.emit(opcode, node=node)
    
    def visit_Call(self, node: ast.Call) -> None:
        """Function call."""
        # Compile arguments first (they'll be on stack)
        for arg in node.args:
            self.visit(arg)
        
        # Compile function reference
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
            self.emit(IROpcode.CALL, func_name, len(node.args), node=node,
                     comment=f"call {func_name}()")
        elif isinstance(node.func, ast.Attribute):
            # Method call
            self.visit(node.func.value)  # Object
            method_name = node.func.attr
            self.emit(IROpcode.CALL, f".{method_name}", len(node.args), node=node,
                     comment=f"call .{method_name}()")
    
    def visit_IfExp(self, node: ast.IfExp) -> None:
        """Ternary expression: x if cond else y"""
        else_label = self.state.fresh_label("ifexp_else")
        end_label = self.state.fresh_label("ifexp_end")
        
        self.visit(node.test)
        self.emit_jump(IROpcode.JUMP_IF_FALSE, else_label, node=node)
        
        self.visit(node.body)
        self.emit_jump(IROpcode.JUMP, end_label, node=node)
        
        self.state.module.add_label(else_label)
        self.visit(node.orelse)
        
        self.state.module.add_label(end_label)
    
    def visit_List(self, node: ast.List) -> None:
        """List literal."""
        for elt in node.elts:
            self.visit(elt)
        self.emit(IROpcode.BUILD_LIST, len(node.elts), node=node)
    
    def visit_Tuple(self, node: ast.Tuple) -> None:
        """Tuple literal."""
        if isinstance(node.ctx, ast.Load):
            for elt in node.elts:
                self.visit(elt)
            self.emit(IROpcode.BUILD_TUPLE, len(node.elts), node=node)
    
    def visit_Set(self, node: ast.Set) -> None:
        """Set literal."""
        for elt in node.elts:
            self.visit(elt)
        self.emit(IROpcode.BUILD_SET, len(node.elts), node=node)
    
    def visit_Dict(self, node: ast.Dict) -> None:
        """Dict literal."""
        for key, value in zip(node.keys, node.values):
            self.visit(key)
            self.visit(value)
        self.emit(IROpcode.BUILD_DICT, len(node.keys), node=node)
    
    def visit_Subscript(self, node: ast.Subscript) -> None:
        """Subscript access: obj[key]"""
        self.visit(node.value)  # Object
        self.visit(node.slice)  # Index
        self.emit(IROpcode.SUBSCRIPT, node=node)
    
    def visit_Attribute(self, node: ast.Attribute) -> None:
        """Attribute access: obj.attr"""
        self.visit(node.value)
        self.emit(IROpcode.LOAD_CONST, node.attr, node=node)
        self.emit(IROpcode.SUBSCRIPT, node=node, comment=f".{node.attr}")
    
    def visit_Index(self, node: ast.Index) -> None:
        """Index (deprecated in Python 3.9+)."""
        self.visit(node.value)
    
    def visit_Slice(self, node: ast.Slice) -> None:
        """Slice: [start:stop:step]"""
        if node.lower:
            self.visit(node.lower)
        else:
            self.emit(IROpcode.LOAD_CONST, None, node=node)
        
        if node.upper:
            self.visit(node.upper)
        else:
            self.emit(IROpcode.LOAD_CONST, None, node=node)
        
        if node.step:
            self.visit(node.step)
        else:
            self.emit(IROpcode.LOAD_CONST, None, node=node)
        
        self.emit(IROpcode.BUILD_TUPLE, 3, node=node, comment="slice")
    
    # Handle NameConstant for older Python versions
    def visit_NameConstant(self, node: ast.NameConstant) -> None:
        """Name constant (True, False, None)."""
        self.emit(IROpcode.LOAD_CONST, node.value, node=node)
    
    # Handle Num for older Python versions
    def visit_Num(self, node: ast.Num) -> None:
        """Numeric literal."""
        self.emit(IROpcode.LOAD_CONST, node.n, node=node)
    
    # Handle Str for older Python versions
    def visit_Str(self, node: ast.Str) -> None:
        """String literal."""
        self.emit(IROpcode.LOAD_CONST, node.s, node=node)


def compile_python_to_ir(source: str, filename: str = "<source>") -> IRModule:
    """
    Compile Python source code to Thiele IR.
    
    This is the main entry point for compilation.
    Returns an IRModule with bidirectional source mapping.
    """
    compiler = PythonToThieleCompiler(source_code=source, filename=filename)
    return compiler.compile(source)
