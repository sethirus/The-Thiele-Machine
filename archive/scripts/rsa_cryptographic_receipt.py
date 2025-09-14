import hashlib
import json
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
from thielecpu.state import State
from thielecpu.mdl import mdlacc

def hash_obj(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode("utf-8")).hexdigest()

def rsa_partition_example():
    """
    Express RSA-1024 composite factoring in partition language.
    This is a simplified example - real RSA factoring would be much more complex.
    """
    # Example RSA-1024 composite (simplified for demonstration)
    # In reality, this would be a 1024-bit number
    composite = 3233  # 53 * 61 for demonstration
    factors = [53, 61]

    # Create initial state
    state = State()
    state.mu = 0.0

    # Partition for factoring
    # Module 0: Trial division up to sqrt(n)
    # Module 1: Check if factor found
    # Module 2: Verify factors multiply to original

    # Simulate discovery cost (μ_discovery)
    discovery_cost = 0
    for i in range(2, int(composite**0.5) + 1):
        if composite % i == 0:
            discovery_cost += 1  # Each trial division check
            break

    # Simulate operational cost (μ_operational)
    operational_cost = len(str(composite))  # Bit length approximation

    # Create partition modules using pnew
    module1 = state.pnew(set(range(10)))  # Trial division module
    module2 = state.pnew(set(range(10, 20)))  # Factor verification
    module3 = state.pnew(set(range(20, 30)))  # Product verification

    modules = [module1, module2, module3]

    # Simulate audits with auditor contract
    for module in modules:
        mdlacc(state, module, consistent=True)

    # Generate cryptographic receipt
    receipt = {
        "composite": composite,
        "factors": factors,
        "mu_discovery": discovery_cost,
        "mu_operational": operational_cost,
        "mu_total": state.mu,
        "partition_modules": {module: len(state.regions[module]) for module in modules},
        "audit_trail": [
            {"module": modules[0], "size": len(state.regions[modules[0]]), "consistent": True},
            {"module": modules[1], "size": len(state.regions[modules[1]]), "consistent": True},
            {"module": modules[2], "size": len(state.regions[modules[2]]), "consistent": True}
        ]
    }

    # Hash the receipt for cryptographic integrity
    receipt_hash = hash_obj(receipt)

    return {
        "receipt": receipt,
        "hash": receipt_hash,
        "verification": f"Hash: {receipt_hash[:16]}... (verify with sha256)"
    }

if __name__ == "__main__":
    result = rsa_partition_example()
    print("RSA Cryptographic Receipt:")
    print(json.dumps(result["receipt"], indent=2))
    print(f"\nReceipt Hash: {result['hash']}")
    print(f"Verification: {result['verification']}")

    # Save to file
    with open("rsa_receipt.json", "w") as f:
        json.dump(result, f, indent=2)
    print("\nSaved to rsa_receipt.json")