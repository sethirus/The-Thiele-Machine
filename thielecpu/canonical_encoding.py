"""Canonical state encoding and hashing (aligned with Coq CoreSemantics.v).

This module implements the authoritative state encoding that defines semantic equality.
Two states are equivalent iff their hashes match.

Coq source of truth:
  coq/thielemachine/coqproofs/CoreSemantics.v:236-245
  coq/thielemachine/coqproofs/Hash256.v:14-43
  
  Definition encode_state (s : State) : list Z :=
    encode_partition s.(partition)
    ++ [s.(mu_ledger).(mu_operational); s.(mu_ledger).(mu_information); s.(mu_ledger).(mu_total)]
    ++ [Z.of_nat s.(pc); bool_to_Z s.(halted)]
    ++ (match s.(result) with None => [0] | Some n => [1; Z.of_nat n] end)
    ++ [Z.of_nat (List.length s.(program))]
    ++ encode_program s.(program).
    
  Definition hash256 (xs : list Z) : list bool :=
    let acc := fold_mix xs 0 in
    bits_be 256%nat acc.
  
  Where fold_mix implements polynomial mixer:
    mix(acc, x) = (acc * 1315423911 + x + 2654435761) mod 2^256

Key invariant:
  s1 semantically equal to s2  <=>  hash_state(s1) == hash_state(s2)
  
CRITICAL DECISIONS:
1. Module IDs ARE SEMANTIC (included in hash)
2. μ-costs must be integers (no floats)
3. Hash function is polynomial mixer (NOT SHA-256)
4. Canonicalization must match Coq exactly
"""

from typing import List, Optional, Set, Tuple
from fractions import Fraction


def encode_region(region: Set[int]) -> List[int]:
    """Encode region as sorted list of variable IDs.
    
    Coq: Fixpoint encode_region (r : Region) : list Z := ...
    
    Args:
        region: Set of variable IDs (unsorted)
    
    Returns:
        Sorted list [x1, x2, ...] where x1 < x2 < ...
    """
    return sorted(region)


def encode_modules(modules: List[Tuple[int, frozenset[int]]]) -> List[int]:
    """Encode partition modules.
    
    Coq: Fixpoint encode_modules (ms : list (ModuleId * Region)) : list Z := ...
    
    Each module encoded as:
      [module_id, region_length, var1, var2, ...]
    
    Args:
        modules: List of (module_id, region) tuples (already sorted by module_id)
    
    Returns:
        Flat list of integers
    """
    result = []
    for mid, region in modules:
        encoded_region = encode_region(region)
        result.append(mid)
        result.append(len(encoded_region))
        result.extend(encoded_region)
    return result


def encode_partition(modules: List[Tuple[int, frozenset[int]]], next_module_id: int) -> List[int]:
    """Encode partition state.
    
    Coq: Definition encode_partition (p : Partition) : list Z :=
           encode_modules p.(modules) ++ [Z.of_nat p.(next_module_id)].
    
    Args:
        modules: List of (module_id, region) sorted by module_id
        next_module_id: Next available module ID
    
    Returns:
        Flat list: encoded_modules ++ [next_module_id]
    """
    return encode_modules(modules) + [next_module_id]


def encode_instruction(instr_tag: int, operands: List[int]) -> List[int]:
    """Encode single instruction.
    
    Coq: Fixpoint encode_instruction (i : Instruction) : list Z := ...
    
    Args:
        instr_tag: Opcode (0=PNEW, 1=PSPLIT, 2=PMERGE, ...)
        operands: Instruction-specific operands
    
    Returns:
        [instr_tag, operand1, operand2, ...]
    """
    return [instr_tag] + operands


def encode_program(program: List[Tuple[int, List[int]]]) -> List[int]:
    """Encode program as flat list.
    
    Coq: Fixpoint encode_program (p : Program) : list Z := ...
    
    Args:
        program: List of (instr_tag, operands) tuples
    
    Returns:
        Flat list of encoded instructions
    """
    result = []
    for instr_tag, operands in program:
        result.extend(encode_instruction(instr_tag, operands))
    return result


def encode_state(
    modules: List[Tuple[int, frozenset[int]]],
    next_module_id: int,
    mu_operational: Fraction,
    mu_information: Fraction,
    mu_total: Fraction,
    pc: int,
    halted: bool,
    result: Optional[int],
    program: List[Tuple[int, List[int]]]
) -> List[int]:
    """Canonical state encoding (Coq ground truth).
    
    Coq: Definition encode_state (s : State) : list Z := ...
    
    This is the **authoritative** representation. Anything not captured here
    does not exist semantically.
    
    Args:
        modules: Partition modules (sorted by module_id)
        next_module_id: Next available module ID
        mu_operational: μ_operational (exact rational)
        mu_information: μ_information (exact rational)
        mu_total: μ_total (exact rational)
        pc: Program counter
        halted: Halt flag
        result: Optional result value
        program: Instruction sequence
    
    Returns:
        Canonical encoding as list of integers
    """
    # Partition
    encoded = encode_partition(modules, next_module_id)
    
    # μ-ledger (convert Fraction to int - assumes integral μ-costs)
    # NOTE: Coq uses Z (integers), not rationals. If VM uses Fraction,
    # we must normalize first (e.g., require denominator=1 or scale)
    encoded.extend([
        int(mu_operational),
        int(mu_information),
        int(mu_total)
    ])
    
    # Control state
    encoded.append(pc)
    encoded.append(1 if halted else 0)
    
    # Result
    if result is None:
        encoded.append(0)
    else:
        encoded.extend([1, result])
    
    # Program
    encoded.append(len(program))
    encoded.extend(encode_program(program))
    
    return encoded


def hash256_coq(xs: List[int]) -> str:
    """Polynomial hash mixer matching Coq Hash256.hash256.
    
    Coq implementation:
      Definition mix (acc x : Z) : Z :=
        Z.modulo (acc * 1315423911 + x + 2654435761) modulus.
      
      Fixpoint fold_mix (xs : list Z) (acc : Z) : Z :=
        match xs with
        | [] => acc
        | x :: xs' => fold_mix xs' (mix acc x)
        end.
      
      Definition hash256 (xs : list Z) : list bool :=
        let acc := fold_mix xs 0 in
        bits_be 256%nat acc.
    
    Returns:
        256-bit hash as hex string (64 chars)
    """
    MODULUS = 2 ** 256
    
    # Polynomial mixer constants (from Coq)
    def mix(acc: int, x: int) -> int:
        return (acc * 1315423911 + x + 2654435761) % MODULUS
    
    # Fold over list
    acc = 0
    for x in xs:
        acc = mix(acc, x)
    
    # Convert to hex (256 bits = 64 hex chars)
    return hex(acc)[2:].zfill(64)


def hash_state(
    modules: List[Tuple[int, frozenset[int]]],
    next_module_id: int,
    mu_operational: Fraction,
    mu_information: Fraction,
    mu_total: Fraction,
    pc: int,
    halted: bool,
    result: Optional[int],
    program: List[Tuple[int, List[int]]]
) -> str:
    """Hash canonical state encoding using Coq's polynomial mixer.
    
    Coq: Definition hash_state (s : State) : StateHash := Hash256.hash256 (encode_state s).
    
    This is the **one true equivalence relation**.
    
    Two states are semantically equal iff their hashes match.
    
    CRITICAL: This uses Coq's polynomial mixer, NOT SHA-256.
    
    Args:
        (same as encode_state)
    
    Returns:
        Hex-encoded 256-bit hash (64 chars)
    """
    encoded = encode_state(
        modules, next_module_id,
        mu_operational, mu_information, mu_total,
        pc, halted, result, program
    )
    
    return hash256_coq(encoded)


def state_hash_from_vm(state) -> str:
    """Extract canonical hash from VM State object.
    
    Args:
        state: thielecpu.state.State instance
    
    Returns:
        Canonical hash (hex string)
    """
    # Extract partition as sorted (module_id, region) pairs
    modules = sorted(
        (mid, frozenset(state.regions.modules[mid]))
        for mid in state.regions.modules.keys()
    )
    
    # Extract next_module_id (VM uses regions.next_module_id)
    next_module_id = state.regions.next_module_id
    
    # Extract μ-ledger
    mu_operational = state.mu_ledger.operational
    mu_information = state.mu_ledger.informational
    mu_total = state.mu_ledger.total
    
    # Control state (VM doesn't have pc/halted/program - use defaults for now)
    # TODO: Extend State class to include these fields
    pc = 0
    halted = False
    result = None
    program = []  # Empty program for now
    
    return hash_state(
        modules, next_module_id,
        mu_operational, mu_information, mu_total,
        pc, halted, result, program
    )
