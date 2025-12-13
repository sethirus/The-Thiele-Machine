#!/usr/bin/env python3
"""
Receipt generation and Merkle tree chaining for The Thiele Machine.

This module provides cryptographically verifiable receipts for VM executions,
with Merkle tree chaining for compact proof-of-computation.
"""

import hashlib
import json
from typing import List, Tuple, Optional, Dict, Any
from dataclasses import dataclass, asdict


@dataclass
class ExecutionReceipt:
    """Receipt for a single VM operation."""
    operation: str
    mu_cost: int
    state_hash: str
    timestamp: Optional[float] = None
    metadata: Optional[Dict[str, Any]] = None
    
    def to_dict(self) -> dict:
        """Convert receipt to dictionary."""
        return asdict(self)
    
    def to_json(self) -> str:
        """Serialize receipt to JSON."""
        return json.dumps(self.to_dict(), indent=2)
    
    def hash(self) -> str:
        """Compute cryptographic hash of this receipt."""
        # Canonical JSON representation for hashing
        canonical = json.dumps(self.to_dict(), sort_keys=True, separators=(',', ':'))
        return hashlib.sha256(canonical.encode()).hexdigest()


class MerkleNode:
    """Node in a Merkle tree."""
    
    def __init__(self, left: Optional['MerkleNode'] = None,
                 right: Optional['MerkleNode'] = None,
                 value: Optional[str] = None):
        self.left = left
        self.right = right
        
        if value:
            # Leaf node
            self.value = value
        else:
            # Internal node: hash of children
            left_hash = left.value if left else ''
            right_hash = right.value if right else ''
            combined = left_hash + right_hash
            self.value = hashlib.sha256(combined.encode()).hexdigest()
    
    def is_leaf(self) -> bool:
        """Check if this is a leaf node."""
        return self.left is None and self.right is None


class MerkleTree:
    """Merkle tree for chaining execution receipts."""
    
    def __init__(self, receipt_hashes: List[str]):
        """
        Build Merkle tree from receipt hashes.
        
        Args:
            receipt_hashes: List of receipt hash values (leaf nodes)
        """
        if not receipt_hashes:
            raise ValueError("Cannot build Merkle tree from empty list")
        
        self.leaves = [MerkleNode(value=h) for h in receipt_hashes]
        self.root = self._build_tree(self.leaves)
    
    def _build_tree(self, nodes: List[MerkleNode]) -> MerkleNode:
        """
        Recursively build Merkle tree from leaf nodes.
        
        Args:
            nodes: List of nodes at current level
        
        Returns:
            Root node of the tree
        """
        if len(nodes) == 1:
            return nodes[0]
        
        # Pair up nodes and create parent nodes
        parents = []
        for i in range(0, len(nodes), 2):
            left = nodes[i]
            right = nodes[i + 1] if i + 1 < len(nodes) else nodes[i]  # Duplicate last if odd
            parents.append(MerkleNode(left, right))
        
        return self._build_tree(parents)
    
    def get_root_hash(self) -> str:
        """Get the root hash of the Merkle tree."""
        return self.root.value
    
    def get_proof(self, index: int) -> List[Tuple[str, str]]:
        """
        Generate Merkle proof for a specific receipt.
        
        Args:
            index: Index of the receipt (0-based)
        
        Returns:
            List of (hash, position) tuples forming the proof path
            position is 'left' or 'right' indicating sibling position
        """
        if index < 0 or index >= len(self.leaves):
            raise IndexError(f"Receipt index {index} out of range")
        
        proof = []
        nodes = self.leaves
        current_index = index
        
        while len(nodes) > 1:
            # Get sibling
            if current_index % 2 == 0:
                # We're on the left, sibling is on the right
                sibling_index = current_index + 1
                position = 'right'
            else:
                # We're on the right, sibling is on the left
                sibling_index = current_index - 1
                position = 'left'
            
            if sibling_index < len(nodes):
                proof.append((nodes[sibling_index].value, position))
            else:
                # Odd number of nodes, duplicate current
                proof.append((nodes[current_index].value, position))
            
            # Move to parent level
            parents = []
            for i in range(0, len(nodes), 2):
                left = nodes[i]
                right = nodes[i + 1] if i + 1 < len(nodes) else nodes[i]
                parents.append(MerkleNode(left, right))
            
            nodes = parents
            current_index = current_index // 2
        
        return proof
    
    def verify_proof(self, receipt_hash: str, index: int, proof: List[Tuple[str, str]]) -> bool:
        """
        Verify a Merkle proof.
        
        Args:
            receipt_hash: Hash of the receipt to verify
            index: Index of the receipt in the tree
            proof: Merkle proof path
        
        Returns:
            True if proof is valid, False otherwise
        """
        current_hash = receipt_hash
        
        for sibling_hash, position in proof:
            if position == 'left':
                combined = sibling_hash + current_hash
            else:
                combined = current_hash + sibling_hash
            current_hash = hashlib.sha256(combined.encode()).hexdigest()
        
        return current_hash == self.root.value


class ReceiptChain:
    """Chain of execution receipts with Merkle tree verification."""
    
    def __init__(self):
        self.receipts: List[ExecutionReceipt] = []
        self.merkle_tree: Optional[MerkleTree] = None
    
    def add_receipt(self, receipt: ExecutionReceipt):
        """Add a receipt to the chain."""
        self.receipts.append(receipt)
        # Invalidate Merkle tree (will be rebuilt on finalize)
        self.merkle_tree = None
    
    def finalize(self):
        """Finalize the chain by building the Merkle tree."""
        if not self.receipts:
            raise ValueError("Cannot finalize empty receipt chain")
        
        receipt_hashes = [r.hash() for r in self.receipts]
        self.merkle_tree = MerkleTree(receipt_hashes)
    
    def get_root_hash(self) -> str:
        """Get the Merkle root hash of the finalized chain."""
        if self.merkle_tree is None:
            raise ValueError("Chain not finalized. Call finalize() first.")
        return self.merkle_tree.get_root_hash()
    
    def get_proof(self, index: int) -> Dict[str, Any]:
        """
        Get compact proof for a specific receipt.
        
        Args:
            index: Index of the receipt
        
        Returns:
            Dictionary containing:
            - receipt: The receipt data
            - merkle_proof: The Merkle proof path
            - root_hash: The Merkle root hash
        """
        if self.merkle_tree is None:
            raise ValueError("Chain not finalized. Call finalize() first.")
        
        receipt = self.receipts[index]
        merkle_proof = self.merkle_tree.get_proof(index)
        
        return {
            'receipt': receipt.to_dict(),
            'merkle_proof': merkle_proof,
            'root_hash': self.merkle_tree.get_root_hash(),
            'index': index,
            'total_receipts': len(self.receipts)
        }
    
    def verify_receipt(self, proof_data: Dict[str, Any]) -> bool:
        """
        Verify a receipt proof.
        
        Args:
            proof_data: Proof data from get_proof()
        
        Returns:
            True if proof is valid, False otherwise
        """
        receipt = ExecutionReceipt(**proof_data['receipt'])
        receipt_hash = receipt.hash()
        index = proof_data['index']
        merkle_proof = proof_data['merkle_proof']
        claimed_root = proof_data['root_hash']
        
        # Rebuild hash from proof
        current_hash = receipt_hash
        for sibling_hash, position in merkle_proof:
            if position == 'left':
                combined = sibling_hash + current_hash
            else:
                combined = current_hash + sibling_hash
            current_hash = hashlib.sha256(combined.encode()).hexdigest()
        
        return current_hash == claimed_root
    
    def to_json(self) -> str:
        """Serialize the entire chain to JSON."""
        if self.merkle_tree is None:
            raise ValueError("Chain not finalized. Call finalize() first.")
        
        data = {
            'receipts': [r.to_dict() for r in self.receipts],
            'root_hash': self.merkle_tree.get_root_hash(),
            'total_receipts': len(self.receipts)
        }
        return json.dumps(data, indent=2)


def create_receipt(operation: str, mu_cost: int, state_hash: str,
                   timestamp: Optional[float] = None,
                   metadata: Optional[Dict[str, Any]] = None) -> ExecutionReceipt:
    """
    Create an execution receipt.
    
    Args:
        operation: Name of the operation (e.g., "pnew", "psplit")
        mu_cost: μ-cost charged for the operation
        state_hash: Hash of the VM state after the operation
        timestamp: Optional timestamp
        metadata: Optional metadata dictionary
    
    Returns:
        ExecutionReceipt instance
    """
    return ExecutionReceipt(
        operation=operation,
        mu_cost=mu_cost,
        state_hash=state_hash,
        timestamp=timestamp,
        metadata=metadata
    )
