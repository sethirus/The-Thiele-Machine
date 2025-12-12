# The Thiele Isomorphism Verification Plan

**Document Version:** 1.0  
**Date:** December 12, 2025  
**Purpose:** Strategic blueprint for independent auditing of the Thiele Machine's three-layer isomorphism claims

---

## Executive Summary

This document provides a **comprehensive investigation strategy** for verifying the central claim of The Thiele Machine project: that three independent implementations—formal proofs in Coq, synthesizable hardware in Verilog, and an executable virtual machine in Python—are **functionally isomorphic** at the instruction-level semantics.

**This is not a checklist.** This is a **strategic framework** that guides an auditor to:
1. **Discover** the canonical state representation from first principles
2. **Map** the instruction set architecture across all three pillars
3. **Extract** formal guarantees from the proof layer
4. **Design** adversarial tests to falsify isomorphism claims
5. **Synthesize** evidence into a definitive audit report

---

## Phase 1: Discovery and Canonical State Definition

### 1.1 Locate the Three Pillars

**Objective:** Independently identify the three core implementations without relying on documentation paths.

**Investigation Strategy:**

1. **Explore the repository structure** to identify three distinct implementation directories:
   - Look for a directory containing `.v` files (Coq formal proofs)
   - Look for a directory containing `.v` or `.sv` files (Verilog/SystemVerilog RTL)
   - Look for a directory containing `.py` files implementing a virtual machine

2. **Expected Discovery:**
   - **Formal Proof Pillar**: Search for directories with names like `coq/`, `proofs/`, `verification/`, or `formal/`
   - **Hardware Pillar**: Search for directories with names like `hardware/`, `rtl/`, `verilog/`, or `hdl/`
   - **Software VM Pillar**: Search for directories with names like `vm/`, `python/`, `interpreter/`, or module directories containing VM implementation

3. **Validation Criteria:**
   - Each pillar should contain a complete, independent implementation
   - Each should define the same instruction set (likely 10-20 instructions)
   - Each should implement state transition semantics

**Expected Evidence:**
```
Repository Structure:
├── coq/                          # Formal proof pillar
│   ├── kernel/                   # Core VM semantics
│   ├── thielemachine/           # Extended proofs
│   └── *.v files                # Coq proof files
├── thielecpu/hardware/           # Hardware pillar
│   ├── thiele_cpu.v             # Main CPU module
│   ├── mau.v                    # μ-ALU unit
│   └── *.v files                # Verilog modules
└── thielecpu/                    # Software VM pillar
    ├── vm.py                     # Virtual machine
    ├── state.py                  # State representation
    ├── isa.py                    # Instruction set
    └── *.py files               # Python implementation
```

### 1.2 Define the "Atom of Truth": The Canonical State

**Objective:** Extract the precise definition of the machine `State` from all three pillars and prove they are equivalent.

**Investigation Strategy:**

1. **In the Coq Proofs:**
   - Search for files with names like `State.v`, `VMState.v`, or `MachineState.v`
   - Look for `Record` or `Inductive` type definitions
   - Key search patterns: `Record.*State`, `Definition.*state`, `Inductive.*state`

2. **Expected Components:**
   ```coq
   Record VMState := {
     vm_graph: PartitionGraph;      (* Module/partition structure *)
     vm_csrs: CSRState;             (* Control/status registers *)
     vm_pc: nat;                    (* Program counter *)
     vm_mu: nat;                    (* μ-cost accumulator *)
     vm_err: bool                   (* Error flag *)
   }.
   ```

3. **In the Python VM:**
   - Search for files with names like `state.py`, `machine.py`, or `vm.py`
   - Look for `@dataclass` or `class State:` definitions
   - Key components should mirror Coq structure

4. **Expected Components:**
   ```python
   @dataclass
   class State:
       mu_ledger: MuLedger           # μ-cost tracking
       regions: RegionGraph          # Partition structure
       csr: dict[CSR, int]          # Control/status registers
       pc: int                       # Program counter (implicit or explicit)
       partition_masks: Dict[ModuleId, PartitionMask]  # Bitmask representation
   ```

5. **In the Verilog RTL:**
   - Search for the main CPU module (likely `thiele_cpu.v` or similar)
   - Look for `reg` declarations defining machine state
   - Key components: PC register, partition storage, μ-accumulator

6. **Expected Components:**
   ```verilog
   module thiele_cpu (
     // State registers
     reg [31:0] pc_reg;              // Program counter
     reg [31:0] mu_accumulator;      // μ-cost (Q16.16 format)
     reg [31:0] csr_cert_addr;       // CSR: Certificate address
     reg [31:0] csr_status;          // CSR: Status
     reg [31:0] csr_error;           // CSR: Error code
     // Partition structures (implementation-dependent)
   );
   ```

**Critical Analysis:**
- **Question 1:** Do all three define the same state components?
- **Question 2:** Are data types compatible (nat vs. int vs. reg[31:0])?
- **Question 3:** Are partition representations isomorphic (lists vs. bitmasks vs. arrays)?
- **Question 4:** Is the μ-ledger represented identically?

### 1.3 Find the Rosetta Stone: Canonical Serialization Format

**Objective:** Locate the specification that defines how to serialize state into a deterministic byte stream for comparison.

**Investigation Strategy:**

1. **Search for specification documents:**
   - Look in `docs/`, `spec/`, or repository root
   - Search for files with names like `*spec*.md`, `*canonical*.md`, `*serialization*.md`
   - Key patterns: "canonical serialization", "state encoding", "bit-exact representation"

2. **Expected Discovery:**
   - A document titled something like `thiele_machine_spec.md` or `canonical_state_spec.md`
   - Should define exact byte layout for state components
   - Should specify endianness, padding, alignment

3. **Key Questions to Answer:**
   - How is the program counter encoded (4 bytes? 8 bytes? little-endian? big-endian?)
   - How are partition masks serialized (fixed-width bitmasks? variable-length lists?)
   - How is the μ-ledger encoded (single 32-bit value? two separate counters?)
   - How are CSRs serialized (array? individual fields?)

4. **Look for Implementation:**
   - Search for Python functions with names like `serialize_state()`, `to_bytes()`, or `canonical_repr()`
   - Search for Verilog modules with names like `state_serializer.v` or similar
   - Search for Coq definitions like `state_to_bytes` or extraction code

**Critical Test:**
- Can you take the same logical state in all three implementations and produce bit-identical byte streams?
- If not, the isomorphism claim is **false** at the representation level.

---

## Phase 2: Instruction Set Architecture (ISA) Mapping

### 2.1 Enumerate the Opcodes

**Objective:** Create a complete table mapping symbolic instruction names to numerical opcodes across all three pillars.

**Investigation Strategy:**

1. **In Coq:**
   - Search for `Inductive vm_instruction` or `Inductive opcode`
   - Each constructor represents one instruction
   - Extract the complete list

2. **Expected Format:**
   ```coq
   Inductive vm_instruction :=
   | instr_pnew (region: list nat) (mu_delta: nat)
   | instr_psplit (module: ModuleID) ...
   | instr_pmerge (m1 m2: ModuleID) ...
   | instr_halt (mu_delta: nat).
   ```

3. **In Python:**
   - Search for `class Opcode(Enum)` or instruction dispatch tables
   - File likely named `isa.py` or `opcodes.py`

4. **Expected Format:**
   ```python
   class Opcode(Enum):
       PNEW = 0x00
       PSPLIT = 0x01
       PMERGE = 0x02
       ...
       HALT = 0xFF
   ```

5. **In Verilog:**
   - Search for `localparam [7:0] OPCODE_*` definitions
   - Usually in the main CPU module or a separate opcodes file

6. **Expected Format:**
   ```verilog
   localparam [7:0] OPCODE_PNEW   = 8'h00;
   localparam [7:0] OPCODE_PSPLIT = 8'h01;
   localparam [7:0] OPCODE_PMERGE = 8'h02;
   ...
   localparam [7:0] OPCODE_HALT   = 8'hFF;
   ```

**Create Verification Table:**

| Symbolic Name | Coq Constructor | Python Enum | Verilog Param | Numeric Value |
|---------------|----------------|-------------|---------------|---------------|
| PNEW          | instr_pnew     | Opcode.PNEW | OPCODE_PNEW   | 0x00          |
| PSPLIT        | instr_psplit   | Opcode.PSPLIT | OPCODE_PSPLIT | 0x01        |
| PMERGE        | instr_pmerge   | Opcode.PMERGE | OPCODE_PMERGE | 0x02        |
| ...           | ...            | ...         | ...           | ...           |
| HALT          | instr_halt     | Opcode.HALT | OPCODE_HALT   | 0xFF          |

**Verification Criterion:**
- All three pillars must define **exactly the same set** of instructions
- Opcodes must map to **identical numeric values**
- Any discrepancy invalidates the isomorphism claim

### 2.2 Map the State Transition Logic

**Objective:** For each instruction, verify that the state transition semantics are identical across all three implementations.

**Investigation Strategy:**

1. **Create Semantic Templates** for each instruction class:

   **Example: PNEW (Create New Partition)**
   ```
   Input: region (set of indices or bitmask)
   Precondition: num_modules < MAX_MODULES
   Effect:
     - Create new module with ID = next_id
     - Add region to module table
     - Increment next_id
     - Update μ-ledger: mu_discovery += popcount(region)
   Postcondition: num_modules increased by 1 (or existing module returned)
   ```

2. **In Coq - Extract Formal Semantics:**
   - Search for `vm_step` relation or similar
   - File likely named `VMStep.v` or `Semantics.v`
   - Look for inductive cases defining each instruction

3. **Expected Format:**
   ```coq
   | step_pnew : forall s region cost graph' mid,
       graph_pnew s.(vm_graph) region = (graph', mid) ->
       vm_step s (instr_pnew region cost)
         (advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err))
   ```

4. **In Python - Extract Implementation:**
   - Search for instruction handler functions or VM step logic
   - Likely in `vm.py` or method dispatch table

5. **Expected Pattern:**
   ```python
   def pnew(self, region: Set[int]) -> ModuleId:
       """Create new module for region."""
       if self.num_modules >= MAX_MODULES:
           raise ValueError("Max modules reached")
       mid = self._alloc(region, charge_discovery=True)
       self.mu_ledger.mu_discovery += popcount(region)
       return mid
   ```

6. **In Verilog - Extract Hardware Logic:**
   - Search for `case (opcode)` or instruction decode/execute logic
   - Likely in main CPU module's always block

7. **Expected Pattern:**
   ```verilog
   OPCODE_PNEW: begin
     // Create new module
     next_module_id = module_id_counter + 1;
     module_regions[next_module_id] = region_operand;
     // Update μ-ledger
     mu_accumulator = mu_accumulator + popcount(region_operand);
   end
   ```

**For Each Instruction, Verify:**
- **Inputs:** Same operand structure (register indices, immediate values, memory addresses)?
- **Preconditions:** Same validity checks (bounds, disjointness, etc.)?
- **State Updates:** Same components modified in same order?
- **μ-Cost:** Same cost formula applied?
- **Error Handling:** Same error conditions detected?

**Create Instruction Audit Matrix:**

| Instruction | Coq Semantics Match | Python Implementation Match | Verilog Logic Match | μ-Cost Consistent | Notes |
|-------------|---------------------|----------------------------|-------------------|------------------|-------|
| PNEW        | ✓ / ✗              | ✓ / ✗                     | ✓ / ✗            | ✓ / ✗           |       |
| PSPLIT      | ✓ / ✗              | ✓ / ✗                     | ✓ / ✗            | ✓ / ✗           |       |
| ...         | ...                 | ...                        | ...               | ...              |       |

---

## Phase 3: Formal Guarantees and Invariant Checking

### 3.1 Identify the Core Theorems

**Objective:** Extract the high-level theorems that define what the machine *guarantees* about its behavior.

**Investigation Strategy:**

1. **Search Coq Proof Files for Main Theorems:**
   - Use `grep -r "Theorem\|Lemma" coq/` to find all theorem statements
   - Focus on files with names like `Subsumption.v`, `Conservation.v`, `Separation.v`, `Security.v`

2. **Expected Theorem Classes:**

   **A. Subsumption (Turing Completeness)**
   ```coq
   Theorem thiele_simulates_turing :
     forall fuel prog st,
       program_is_turing prog ->
       run_tm fuel prog st = run_thiele fuel prog st.
   ```
   
   **Claim:** Every Turing machine program runs identically on Thiele (when restricted).

   **B. μ-Ledger Conservation**
   ```coq
   Theorem vm_step_respects_mu_ledger :
     forall s instr s',
       vm_step s instr s' ->
       s'.(vm_mu) = s.(vm_mu) + instruction_cost instr.
   ```
   
   **Claim:** μ-cost is monotonically non-decreasing and equals the sum of instruction costs.

   **C. Partition Modularity**
   ```coq
   Theorem partition_isolation :
     forall s m1 m2 op s',
       disjoint_modules s m1 m2 ->
       operates_on s op m1 s' ->
       unchanged_module s s' m2.
   ```
   
   **Claim:** Operations on one module don't affect disjoint modules.

   **D. Security Guarantees**
   ```coq
   Theorem receipt_uniqueness :
     forall s1 s2 prog r,
       s1 <> s2 ->
       produces_receipt s1 prog r ->
       produces_receipt s2 prog r ->
       False.
   ```
   
   **Claim:** Different computations cannot produce identical cryptographic receipts.

3. **Document Each Core Theorem:**
   - **Name:** Formal identifier
   - **Statement:** What it claims
   - **File Location:** Where to find the proof
   - **Status:** Proven / Admitted / Axiom
   - **Dependencies:** What other lemmas it relies on

### 3.2 Translate Proofs to Properties

**Objective:** Convert mathematical theorems into executable, falsifiable test properties.

**Translation Strategy:**

1. **Modularity → Property-Based Test**

   **Theorem:**
   ```coq
   Operations on Module A cannot modify the state of Module B if A ∩ B = ∅
   ```

   **Falsifiable Property:**
   ```python
   @given(
       region_a=st.sets(st.integers(0, 63), min_size=1, max_size=10),
       region_b=st.sets(st.integers(0, 63), min_size=1, max_size=10),
       operation=st.sampled_from([PNEW, PSPLIT, PMERGE, ...])
   )
   def test_partition_isolation(region_a, region_b, operation):
       assume(region_a.isdisjoint(region_b))  # Precondition
       
       state = State()
       module_a = state.pnew(region_a)
       module_b = state.pnew(region_b)
       
       snapshot_b_before = state.partition_masks[module_b]
       
       # Execute operation on module_a
       execute_operation(state, operation, module_a)
       
       snapshot_b_after = state.partition_masks[module_b]
       
       # Module B should be unchanged
       assert snapshot_b_before == snapshot_b_after
   ```

2. **Conservation → Invariant Check**

   **Theorem:**
   ```coq
   μ-ledger is monotonically non-decreasing
   ```

   **Falsifiable Property:**
   ```python
   def test_mu_conservation(program: List[Instruction]):
       state = State()
       vm = VM(state)
       
       mu_values = [state.mu_ledger.total]
       
       for instruction in program:
           vm.execute(instruction)
           mu_values.append(state.mu_ledger.total)
       
       # μ should never decrease
       for i in range(1, len(mu_values)):
           assert mu_values[i] >= mu_values[i-1], \
               f"μ decreased: {mu_values[i-1]} → {mu_values[i]}"
   ```

3. **Uniqueness → Collision Resistance Test**

   **Theorem:**
   ```coq
   Different computations → Different receipts
   ```

   **Falsifiable Property:**
   ```python
   def test_receipt_uniqueness():
       programs = generate_random_programs(count=10000)
       receipts = set()
       
       for program in programs:
           state = State()
           vm = VM(state)
           vm.execute_program(program)
           receipt = vm.generate_receipt()
           
           # Check for collision
           assert receipt not in receipts, \
               f"Receipt collision detected: {receipt}"
           receipts.add(receipt)
   ```

### 3.3 Design the Falsification Strategy

**Objective:** Create an adversarial testing framework to find counterexamples that break the isomorphism.

**Strategy Components:**

1. **Cross-Implementation Fuzzing**

   **Goal:** Find a program where Coq, Python, and Verilog produce different final states.

   **Approach:**
   ```python
   def fuzz_three_layer_isomorphism(iterations=10000):
       for i in range(iterations):
           # Generate random valid program
           program = generate_random_program(length=10)
           initial_state = generate_random_state()
           
           # Execute in all three implementations
           coq_state = execute_coq(program, initial_state)
           python_state = execute_python(program, initial_state)
           verilog_state = execute_verilog(program, initial_state)
           
           # Serialize all states
           coq_bytes = serialize_state(coq_state)
           python_bytes = serialize_state(python_state)
           verilog_bytes = serialize_state(verilog_state)
           
           # Check bit-exact equality
           if not (coq_bytes == python_bytes == verilog_bytes):
               raise IsomorphismViolation(
                   program=program,
                   coq_result=coq_bytes,
                   python_result=python_bytes,
                   verilog_result=verilog_bytes
               )
   ```

2. **Adversarial Program Generation**

   **Goal:** Generate programs specifically designed to expose corner cases.

   **Attack Vectors:**
   - **Boundary Conditions:** MAX_MODULES, maximum μ-cost, empty partitions
   - **Error Paths:** Invalid operations, precondition violations
   - **Complex Interactions:** PSPLIT followed by PMERGE, nested discoveries
   - **μ-Cost Edge Cases:** Operations with zero cost, overflow conditions

   **Example Generator:**
   ```python
   def generate_adversarial_program():
       attacks = [
           # Fill module table to capacity
           lambda: [PNEW(set(range(i, i+5))) for i in range(MAX_MODULES)],
           
           # Create and immediately split partition
           lambda: [PNEW({1,2,3,4}), PSPLIT(0, lambda x: x % 2 == 0)],
           
           # μ-cost overflow attempt
           lambda: [PNEW(set(range(64))) for _ in range(1000)],
           
           # Invalid module reference
           lambda: [PMERGE(999, 1000)],
       ]
       return random.choice(attacks)()
   ```

3. **Invariant Violation Detection**

   **Goal:** Monitor execution to detect invariant violations at any step.

   **Invariants to Check:**
   - **Partition Disjointness:** No two modules share elements
   - **μ-Monotonicity:** μ never decreases
   - **PC Validity:** PC always in bounds
   - **Module Count:** 0 ≤ num_modules ≤ MAX_MODULES
   - **Bitmask Consistency:** partition_masks and regions agree

   **Example Monitor:**
   ```python
   class InvariantMonitor:
       def check_all(self, state: State):
           self.check_partition_disjointness(state)
           self.check_mu_monotonicity(state)
           self.check_module_bounds(state)
           self.check_bitmask_consistency(state)
       
       def check_partition_disjointness(self, state: State):
           masks = list(state.partition_masks.values())
           for i in range(len(masks)):
               for j in range(i+1, len(masks)):
                   if masks[i] & masks[j] != 0:
                       raise InvariantViolation(
                           f"Modules {i} and {j} overlap: "
                           f"{bin(masks[i])} ∩ {bin(masks[j])} = "
                           f"{bin(masks[i] & masks[j])}"
                       )
   ```

4. **Differential Testing Framework**

   **Goal:** Systematically compare outputs across all three implementations.

   **Test Matrix:**
   ```
   For each instruction opcode:
     For each valid operand combination:
       For each initial state variation:
         Execute in Coq, Python, Verilog
         Compare:
           - Final PC
           - Final μ-ledger
           - Module table state
           - CSR values
           - Error flags
   ```

   **Expected Coverage:**
   - 16 instructions × 10 operand variations × 5 initial states = 800 test cases
   - Each test case executed in all 3 implementations = 2,400 executions
   - Any mismatch = **isomorphism falsified**

---

## Phase 4: Evidence Synthesis and Audit Report

### 4.1 Verification Checklist

**State Representation:**
- [ ] Coq `VMState` definition extracted
- [ ] Python `State` class definition extracted
- [ ] Verilog state registers identified
- [ ] Component-by-component correspondence verified
- [ ] Canonical serialization format documented
- [ ] Serialization functions implemented in all three layers

**Instruction Set:**
- [ ] Complete opcode table created (all 3 implementations)
- [ ] Numeric opcode values verified as identical
- [ ] Instruction count matches across all layers
- [ ] Semantic audit matrix completed (16 × 3 = 48 cells verified)

**Formal Guarantees:**
- [ ] Core theorems identified (Subsumption, Conservation, Modularity, Security)
- [ ] Proof status documented (Proven/Admitted/Axiom)
- [ ] Properties translated to executable tests
- [ ] Test suite executed with 0 failures

**Falsification Attempts:**
- [ ] Cross-layer fuzzing executed (10,000+ iterations)
- [ ] Adversarial programs generated and tested
- [ ] Invariant monitoring integrated
- [ ] Differential testing matrix completed
- [ ] No isomorphism violations discovered

### 4.2 Audit Report Template

```markdown
# Thiele Machine Isomorphism Audit Report

**Auditor:** [Name]
**Date:** [Date]
**Methodology:** Independent verification following The Thiele Isomorphism Verification Plan v1.0

## 1. State Representation Analysis

### 1.1 Coq Formal Definition
[Document extracted VMState structure]

### 1.2 Python Implementation
[Document State class structure]

### 1.3 Verilog Hardware Registers
[Document state registers]

### 1.4 Isomorphism Assessment
- Components match: ✓ / ✗
- Data types compatible: ✓ / ✗
- Serialization consistent: ✓ / ✗

## 2. Instruction Set Mapping

[Include opcode table]

### 2.1 Coverage Analysis
- Coq: [N] instructions
- Python: [N] instructions
- Verilog: [N] instructions
- Match: ✓ / ✗

### 2.2 Semantic Equivalence
[Include audit matrix with results]

## 3. Formal Guarantees

### 3.1 Core Theorems
[List theorems with proof status]

### 3.2 Property-Based Testing
- Tests written: [N]
- Tests passed: [N]
- Failures: [N]

## 4. Falsification Attempts

### 4.1 Fuzzing Results
- Iterations: [N]
- Violations found: [N]
- Details: [...]

### 4.2 Adversarial Testing
- Programs tested: [N]
- Violations found: [N]

## 5. Conclusion

**Isomorphism Verdict:** VERIFIED / PARTIALLY VERIFIED / FALSIFIED

**Critical Issues:**
[List any discrepancies or failures]

**Recommendations:**
[Suggest improvements or areas requiring attention]
```

---

## Phase 5: Continuous Verification

### 5.1 Regression Test Suite

After completing the initial audit, establish a regression test suite that runs on every code change:

1. **Compile All Three Layers:**
   ```bash
   make -C coq kernel
   iverilog -g2012 -tnull thielecpu/hardware/thiele_cpu.v
   python -m pytest tests/test_vm_basic.py
   ```

2. **Execute Cross-Layer Tests:**
   ```bash
   python scripts/test_three_layer_isomorphism.py
   ```

3. **Run Differential Fuzzing:**
   ```bash
   python scripts/fuzz_three_layer.py --iterations 10000
   ```

### 5.2 CI/CD Integration

**Recommended GitHub Actions Workflow:**
```yaml
name: Three-Layer Isomorphism Check

on: [push, pull_request]

jobs:
  isomorphism-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Coq
        run: sudo apt-get install -y coq
      
      - name: Install Verilog tools
        run: sudo apt-get install -y iverilog yosys
      
      - name: Install Python dependencies
        run: pip install -r requirements.txt
      
      - name: Compile Coq kernel
        run: make -C coq kernel
      
      - name: Validate Verilog syntax
        run: iverilog -g2012 -tnull thielecpu/hardware/thiele_cpu.v
      
      - name: Run isomorphism tests
        run: python scripts/test_three_layer_isomorphism.py
      
      - name: Run fuzzing suite
        run: python scripts/fuzz_three_layer.py --iterations 1000
```

---

## Appendix A: Search Patterns and Commands

### A.1 Finding State Definitions

**Coq:**
```bash
grep -r "Record.*State\|Inductive.*state" coq/ | grep -v ".vo"
find coq/ -name "*State*.v" -o -name "*state*.v"
```

**Python:**
```bash
grep -r "@dataclass" thielecpu/ | grep -i state
grep -r "class State" thielecpu/
```

**Verilog:**
```bash
grep -r "reg \[" thielecpu/hardware/*.v | grep -i "pc\|mu\|csr"
```

### A.2 Finding Instruction Definitions

**Coq:**
```bash
grep -r "Inductive.*instruction" coq/
grep -r "vm_instruction\|vm_step" coq/
```

**Python:**
```bash
grep -r "class Opcode" thielecpu/
grep -r "Enum" thielecpu/isa.py
```

**Verilog:**
```bash
grep -r "localparam.*OPCODE" thielecpu/hardware/
grep -r "case.*opcode" thielecpu/hardware/
```

### A.3 Finding Theorems

**Coq:**
```bash
find coq/ -name "*.v" -exec grep -l "Theorem\|Lemma" {} \;
grep -r "Theorem.*subsumption\|Theorem.*conservation" coq/
```

---

## Appendix B: Key Metrics for Isomorphism

### B.1 Quantitative Measures

**State Size:**
- Coq state: [N] components
- Python state: [N] components
- Verilog registers: [N] bits total

**Instruction Count:**
- Coq: [N] instruction constructors
- Python: [N] opcode enum values
- Verilog: [N] case statements

**Test Coverage:**
- Unit tests: [N] tests, [X]% pass
- Integration tests: [N] tests, [X]% pass
- Fuzzing: [N] iterations, [M] violations

### B.2 Qualitative Assessment

**Code Quality:**
- Documentation completeness: 1-5 rating
- Test thoroughness: 1-5 rating
- Proof rigor: 1-5 rating

**Isomorphism Strength:**
- Weak (structural similarity only)
- Moderate (functional equivalence on test cases)
- Strong (bit-exact equivalence, proven formally)

---

## Conclusion

This verification plan provides a **complete methodology** for independently auditing The Thiele Machine's isomorphism claims. By following this strategic framework, an auditor will:

1. **Discover** the canonical state representation from first principles
2. **Map** the complete instruction set architecture
3. **Extract** and test formal guarantees
4. **Execute** adversarial falsification attempts
5. **Synthesize** definitive evidence

**The isomorphism is verified if and only if:**
- All state components correspond exactly across all three implementations
- All instructions have identical semantics and μ-costs
- All core theorems are proven (not admitted or axiomatized)
- Zero violations are found in 10,000+ fuzzing iterations
- Differential testing shows bit-exact equivalence on all test cases

**Any single failure falsifies the isomorphism claim.**

This document serves as the **Rosetta Stone** for understanding and auditing The Thiele Machine's central technical achievement.

---

**Document History:**
- v1.0 (2025-12-12): Initial strategic framework
