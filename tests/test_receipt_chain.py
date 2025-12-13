#!/usr/bin/env python3
"""Tests for receipt generation and Merkle tree chaining."""

import pytest
import time
from thielecpu.receipt import (
    ExecutionReceipt,
    MerkleTree,
    ReceiptChain,
    create_receipt,
)


class TestExecutionReceipt:
    """Test receipt creation and serialization."""
    
    def test_create_basic_receipt(self):
        """Create a basic execution receipt."""
        receipt = create_receipt(
            operation="pnew",
            mu_cost=10,
            state_hash="abc123"
        )
        assert receipt.operation == "pnew"
        assert receipt.mu_cost == 10
        assert receipt.state_hash == "abc123"
    
    def test_receipt_with_metadata(self):
        """Create receipt with metadata."""
        receipt = create_receipt(
            operation="psplit",
            mu_cost=5,
            state_hash="def456",
            timestamp=time.time(),
            metadata={'partition_id': 42}
        )
        assert receipt.metadata['partition_id'] == 42
    
    def test_receipt_hashing(self):
        """Receipt hash is deterministic."""
        r1 = create_receipt("pnew", 10, "abc")
        r2 = create_receipt("pnew", 10, "abc")
        r3 = create_receipt("pnew", 11, "abc")  # Different cost
        
        assert r1.hash() == r2.hash()  # Same receipts, same hash
        assert r1.hash() != r3.hash()  # Different receipts, different hash
    
    def test_receipt_json_roundtrip(self):
        """Receipt can be serialized and contains all fields."""
        receipt = create_receipt("pmerge", 3, "xyz789")
        json_str = receipt.to_json()
        
        assert '"operation": "pmerge"' in json_str
        assert '"mu_cost": 3' in json_str
        assert '"state_hash": "xyz789"' in json_str


class TestMerkleTree:
    """Test Merkle tree construction and proof generation."""
    
    def test_build_single_node_tree(self):
        """Merkle tree with single node."""
        tree = MerkleTree(['hash1'])
        assert tree.get_root_hash() == 'hash1'
    
    def test_build_balanced_tree(self):
        """Merkle tree with power-of-2 nodes."""
        hashes = ['hash1', 'hash2', 'hash3', 'hash4']
        tree = MerkleTree(hashes)
        
        root = tree.get_root_hash()
        assert isinstance(root, str)
        assert len(root) == 64  # SHA-256 hex digest
    
    def test_build_unbalanced_tree(self):
        """Merkle tree with odd number of nodes."""
        hashes = ['hash1', 'hash2', 'hash3']
        tree = MerkleTree(hashes)
        
        root = tree.get_root_hash()
        assert isinstance(root, str)
        assert len(root) == 64
    
    def test_merkle_proof_generation(self):
        """Generate Merkle proof for a leaf."""
        hashes = ['a', 'b', 'c', 'd']
        tree = MerkleTree(hashes)
        
        proof = tree.get_proof(0)  # Proof for first element
        assert isinstance(proof, list)
        assert len(proof) > 0
    
    def test_merkle_proof_verification(self):
        """Verify a valid Merkle proof."""
        hashes = ['a', 'b', 'c', 'd']
        tree = MerkleTree(hashes)
        
        # Get proof for index 1
        proof = tree.get_proof(1)
        
        # Verify proof
        is_valid = tree.verify_proof(hashes[1], 1, proof)
        assert is_valid
    
    def test_merkle_proof_invalid(self):
        """Invalid Merkle proof is rejected."""
        hashes = ['a', 'b', 'c', 'd']
        tree = MerkleTree(hashes)
        
        # Get proof for index 1
        proof = tree.get_proof(1)
        
        # Try to verify with wrong hash
        is_valid = tree.verify_proof('wrong_hash', 1, proof)
        assert not is_valid
    
    def test_empty_tree_raises(self):
        """Building tree from empty list raises error."""
        with pytest.raises(ValueError, match="empty"):
            MerkleTree([])


class TestReceiptChain:
    """Test receipt chaining with Merkle trees."""
    
    def test_create_chain(self):
        """Create and finalize a receipt chain."""
        chain = ReceiptChain()
        
        chain.add_receipt(create_receipt("op1", 10, "hash1"))
        chain.add_receipt(create_receipt("op2", 20, "hash2"))
        chain.add_receipt(create_receipt("op3", 30, "hash3"))
        
        chain.finalize()
        
        root = chain.get_root_hash()
        assert len(root) == 64  # SHA-256
    
    def test_get_proof_from_chain(self):
        """Get compact proof for a receipt in the chain."""
        chain = ReceiptChain()
        
        chain.add_receipt(create_receipt("pnew", 10, "state1"))
        chain.add_receipt(create_receipt("psplit", 5, "state2"))
        chain.add_receipt(create_receipt("pmerge", 3, "state3"))
        
        chain.finalize()
        
        proof = chain.get_proof(1)  # Proof for second receipt
        
        assert 'receipt' in proof
        assert 'merkle_proof' in proof
        assert 'root_hash' in proof
        assert proof['index'] == 1
        assert proof['total_receipts'] == 3
    
    def test_verify_receipt_proof(self):
        """Verify a receipt proof from the chain."""
        chain = ReceiptChain()
        
        chain.add_receipt(create_receipt("pnew", 10, "state1"))
        chain.add_receipt(create_receipt("psplit", 5, "state2"))
        
        chain.finalize()
        
        proof = chain.get_proof(0)
        is_valid = chain.verify_receipt(proof)
        
        assert is_valid
    
    def test_invalid_proof_rejected(self):
        """Invalid proof is rejected."""
        chain = ReceiptChain()
        
        chain.add_receipt(create_receipt("pnew", 10, "state1"))
        chain.add_receipt(create_receipt("psplit", 5, "state2"))
        
        chain.finalize()
        
        proof = chain.get_proof(0)
        
        # Tamper with the receipt
        proof['receipt']['mu_cost'] = 999
        
        is_valid = chain.verify_receipt(proof)
        assert not is_valid
    
    def test_chain_json_export(self):
        """Export chain to JSON."""
        chain = ReceiptChain()
        
        chain.add_receipt(create_receipt("pnew", 10, "state1"))
        chain.add_receipt(create_receipt("psplit", 5, "state2"))
        
        chain.finalize()
        
        json_str = chain.to_json()
        assert '"root_hash"' in json_str
        assert '"total_receipts": 2' in json_str
    
    def test_unfinalized_chain_raises(self):
        """Accessing unfinalized chain raises error."""
        chain = ReceiptChain()
        chain.add_receipt(create_receipt("pnew", 10, "state1"))
        
        with pytest.raises(ValueError, match="not finalized"):
            chain.get_root_hash()
    
    def test_empty_chain_finalize_raises(self):
        """Finalizing empty chain raises error."""
        chain = ReceiptChain()
        
        with pytest.raises(ValueError, match="empty"):
            chain.finalize()


class TestMerkleProofCompactness:
    """Test that Merkle proofs are compact (O(log n))."""
    
    def test_proof_size_grows_logarithmically(self):
        """Proof size is O(log n) not O(n)."""
        # Create chain with 16 receipts
        chain = ReceiptChain()
        for i in range(16):
            chain.add_receipt(create_receipt(f"op{i}", i, f"hash{i}"))
        
        chain.finalize()
        
        proof = chain.get_proof(0)
        proof_size = len(proof['merkle_proof'])
        
        # For 16 elements, proof should be ~4 hashes (log2(16) = 4)
        # Not 16 hashes (full chain)
        assert proof_size <= 5  # Allow small overhead
        assert proof_size < 16  # Definitely compact


def test_integration_example():
    """Full integration test: build chain, get proof, verify."""
    chain = ReceiptChain()
    
    # Simulate a series of VM operations
    operations = [
        ("pnew", 10, "state_after_pnew"),
        ("psplit", 5, "state_after_psplit"),
        ("pmerge", 3, "state_after_pmerge"),
        ("pnew", 8, "state_after_pnew2"),
    ]
    
    for op, cost, state in operations:
        chain.add_receipt(create_receipt(op, cost, state))
    
    # Finalize to build Merkle tree
    chain.finalize()
    
    # Get root hash (compact summary of all receipts)
    root_hash = chain.get_root_hash()
    assert len(root_hash) == 64
    
    # Get proof for one receipt
    proof = chain.get_proof(2)  # Third operation
    
    # Verify proof without needing the full chain
    is_valid = chain.verify_receipt(proof)
    assert is_valid
    
    # Proof contains only O(log n) data, not O(n)
    assert len(proof['merkle_proof']) < len(operations)


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
