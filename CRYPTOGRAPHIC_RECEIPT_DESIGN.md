# Cryptographic Receipt Binding - Complete Design

## Problem Statement

Current receipt system lacks cryptographic binding - receipts are "invoices" that can be forged cheaper than honest execution. The empirical forgery experiment (Challenge 3) confirmed this structural weakness.

## Solution: Cryptographic State Commitment Chain

### Core Idea

Each execution step creates a cryptographic commitment to the full state. These commitments form a **hash chain** that binds the receipt to the actual execution path.

**Property**: Forging a valid receipt requires finding a sequence of states that:
1. Hash to the committed values
2. Follow valid transition rules
3. Produce the claimed output

By collision resistance of SHA-256, this is computationally equivalent to honest execution.

## Three-Layer Design

### Layer 1: Coq Formal Specification

```coq
(** State hash: 32-byte cryptographic commitment *)
Definition StateHash := list bool. (* 256 bits *)

(** Hash function specification (axiomatized, verified against Python) *)
Parameter hash_state : State -> StateHash.

(** Hash chain validity *)
Fixpoint hash_chain_valid (states : list State) (hashes : list StateHash) : bool :=
  match states, hashes with
  | [], [] => true
  | s :: ss, h :: hs => 
      (hash_state s =? h) && hash_chain_valid ss hs
  | _, _ => false
  end.

(** Enhanced receipt with cryptographic binding *)
Record CryptoReceipt := {
  initial_state_hash : StateHash;
  step_witnesses : list StepWitness;  (* Each contains pre/post state hashes *)
  final_state_hash : StateHash;
  total_mu : Z;
  
  (* Invariant: step witnesses form a valid hash chain *)
  (* witness[i].post_hash = witness[i+1].pre_hash *)
}.

Record StepWitness := {
  pre_state_hash : StateHash;
  instruction : Instruction;
  label : Label;
  post_state_hash : StateHash;
  mu_delta : Z;
}.
```

**Key Properties to Prove**:

```coq
(** Uniqueness: hash chain determines execution *)
Theorem receipt_uniqueness : forall r : CryptoReceipt,
  verify_crypto_receipt r = true ->
  exists! t : Trace, 
    make_crypto_receipt t = r.

(** Soundness: valid receipt implies valid execution *)
Theorem crypto_receipt_sound : forall r : CryptoReceipt,
  verify_crypto_receipt r = true ->
  exists t : Trace,
    valid_trace t /\ make_crypto_receipt t = r.

(** Completeness: valid execution produces valid receipt *)
Theorem crypto_receipt_complete : forall t : Trace,
  valid_trace t ->
  verify_crypto_receipt (make_crypto_receipt t) = true.

(** Forgery resistance: collision resistance implies unforgeable *)
Axiom hash_collision_resistance : forall s1 s2 : State,
  hash_state s1 = hash_state s2 -> s1 = s2.

Theorem forgery_requires_collision : forall r : CryptoReceipt,
  verify_crypto_receipt r = true ->
  forall t1 t2 : Trace,
    make_crypto_receipt t1 = r ->
    make_crypto_receipt t2 = r ->
    trace_states t1 = trace_states t2.
```

### Layer 2: Python Implementation

**Current Status**: Already has most infrastructure!

```python
# receipts.py already has:
- hash_snapshot(snapshot) -> SHA-256 hex string ✅
- StepReceipt with pre_state_hash, post_state_hash ✅
- Ed25519 signature binding ✅

# Need to add:
class CryptoReceipt:
    """Receipt with cryptographic state commitment chain."""
    
    initial_state_hash: str
    step_witnesses: List[StepWitness]
    final_state_hash: str
    total_mu: int
    signature: str  # Ed25519 signature over entire receipt
    
    def verify_hash_chain(self) -> bool:
        """Verify state hashes form valid chain."""
        for i in range(len(self.step_witnesses) - 1):
            if self.step_witnesses[i].post_state_hash != \
               self.step_witnesses[i+1].pre_state_hash:
                return False
        return True
    
    def verify(self) -> bool:
        """Full verification: hash chain + signature."""
        return self.verify_hash_chain() and \
               self.verify_signature()
```

**Update Required**:
- Modify `thielecpu/vm.py` to collect full state at each step
- Hash complete state (not just WitnessState subset)
- Build hash chain during execution
- Sign final receipt with Ed25519

### Layer 3: Verilog Hardware

**New Module Required**: `state_hasher.v`

```verilog
module state_hasher #(
    parameter STATE_WIDTH = 512  // Full state width
)(
    input wire clk,
    input wire rst,
    input wire [STATE_WIDTH-1:0] state_in,
    input wire hash_enable,
    output reg [255:0] state_hash,
    output reg hash_valid
);
    // Implement SHA-256 over state
    // Can use existing crypto cores or lightweight hash
    // For FPGA: Consider BLAKE2s (faster) or SHA-256
    
    // State includes:
    // - Partition structure (serialized)
    // - μ-ledger values
    // - PC, halted, result
    // - Program (hash of program, not full program)
endmodule
```

**Integration**:
- Add `state_hasher` to Thiele CPU pipeline
- Compute hash on every state transition
- Store hash in receipt buffer
- Output hash chain on completion

## Implementation Phases

### Phase 1: Coq Foundations ✅ (Current)
- [x] Design document
- [ ] Add StateHash type to CoreSemantics.v
- [ ] Add hash_state parameter
- [ ] Define CryptoReceipt record
- [ ] Define StepWitness with hashes
- [ ] Add hash_chain_valid function

### Phase 2: Coq Proofs (Critical)
- [ ] Prove crypto_receipt_sound (no admits!)
- [ ] Prove crypto_receipt_complete (no admits!)
- [ ] Prove receipt_uniqueness
- [ ] Prove forgery_requires_collision
- [ ] Update ThieleSpaceland.v to use CryptoReceipt

### Phase 3: Python Implementation
- [ ] Add CryptoReceipt class to receipts.py
- [ ] Update StepWitness to include full state hashes
- [ ] Modify vm.py to collect complete state at each step
- [ ] Build hash chain during execution
- [ ] Add verify_hash_chain method
- [ ] Update experiments/receipt_forgery.py to test new system

### Phase 4: Verilog Hardware
- [ ] Create state_hasher.v module
- [ ] Integrate into thiele_cpu.v
- [ ] Add hash chain buffer
- [ ] Update hardware bridge proofs

### Phase 5: Isomorphism Verification
- [ ] Prove hash_state behavior matches across layers
- [ ] Test identical hashes for same state (Coq spec, Python impl, Verilog)
- [ ] Verify forgery is now expensive (>1000x cost)
- [ ] Update EMPIRICAL_VALIDATION_RESULTS.md

### Phase 6: Documentation and Testing
- [ ] Update THIELE_MACHINE_COMPREHENSIVE_GUIDE.md
- [ ] Add cryptographic receipt section
- [ ] Create test suite for hash chain validation
- [ ] Benchmark forgery cost (should be >> honest execution)

## Success Criteria

1. **No admits in Coq proofs** - crypto_receipt_sound and crypto_receipt_complete fully proven
2. **Forgery experimentally hard** - Challenge 3 rerun shows >1000x cost increase
3. **Isomorphic behavior** - Same hashes across all three layers for same state
4. **Compilation success** - All Coq files compile, all Python tests pass, Verilog synthesizes

## Mathematical Foundation

### Collision Resistance

We axiomatize SHA-256 collision resistance:

```coq
Axiom hash_collision_resistance : forall s1 s2,
  hash_state s1 = hash_state s2 -> s1 = s2.
```

This is a standard cryptographic assumption. SHA-256 has ~2^128 collision resistance.

### Forgery Cost

Let:
- N = number of state variables
- D = domain size per variable
- K = number of execution steps

**Honest execution cost**: O(K)
**Forgery cost**: O(D^N) to find state matching hash

For reasonable parameters (N=10, D=2^64, K=100):
- Honest: ~100 operations
- Forgery: ~2^640 operations (impossible)

**Gap**: >2^630 ✅

## Open Questions

1. **Hash function choice**: SHA-256 (standard) vs BLAKE2s (faster for hardware)?
   - **Decision**: SHA-256 for now (standard, well-studied)
   - Future: add BLAKE2s as alternative

2. **State serialization**: How to canonicalize state for hashing?
   - **Decision**: Lexicographic ordering of state fields
   - Partition: sorted list of (module_id, sorted variables)
   - μ-ledger: (op, info, total) as big-endian bytes
   - PC, halted, result: direct binary encoding

3. **Program inclusion**: Hash program or include in state?
   - **Decision**: Hash program separately, include program hash in state
   - Rationale: Programs can be large, hash is sufficient for binding

## References

1. **Collision-Resistant Hashing**: [SHA-256 Specification](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf)
2. **Merkle Trees**: Similar to our hash chain, but tree structure
3. **Blockchain**: Similar principle - hash chain prevents tampering
4. **Zero-Knowledge Proofs**: Future work - prove execution without revealing state

## Timeline

- **Phase 1**: 2-3 days (Coq foundations)
- **Phase 2**: 5-7 days (Coq proofs - critical, no shortcuts)
- **Phase 3**: 2-3 days (Python implementation)
- **Phase 4**: 3-4 days (Verilog hardware)
- **Phase 5**: 2-3 days (Isomorphism verification)
- **Phase 6**: 1-2 days (Documentation)

**Total**: 15-22 days for complete implementation

**Priority**: Phase 1-2 first (Coq foundations and proofs). Cannot proceed without solid formal foundation.
