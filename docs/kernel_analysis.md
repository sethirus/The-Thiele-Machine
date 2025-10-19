# Project Omega: A First-Principles Analysis of the Thiele Machine Kernel

## 1. Abstract
The kernel development formalises two machines that share a common tape-and-head substrate but diverge on a single, additional instruction. The Coq artefacts prove that when programs use only the classical instructions, both machines evolve identically, and they exhibit a concrete program where the Thiele kernel reaches a state the Turing kernel can never reach. This establishes a strict containment relationship driven by the additional claim operation, which carries an explicit \(\mu\)-cost.

## 2. The Formal Universe (`Kernel.v`)
### 2.1 State Components
The shared `state` record contains four fields: a Boolean tape, a natural-valued head position, a natural program counter for the Turing control state, and a natural accumulator for \(\mu\)-cost.【F:coq/kernel/Kernel.v†L4-L9】 The tape and head describe the writable workspace, `tm_state` selects the next instruction, and `mu_cost` records the non-classical expenditure that only one machine can change.

### 2.2 Instruction Vocabulary
Both machines operate over the same `instruction` datatype. It includes halting, writing a bit, moving the head left or right, and branching on the current cell, alongside a single instruction `H_ClaimTapeIsZero` that does not fit the usual Turing primitives.【F:coq/kernel/Kernel.v†L15-L20】 The helper predicate `turing_instruction` marks every instruction except the claim as classical, cleanly separating the tape/head manipulations from the lone geometric action.【F:coq/kernel/Kernel.v†L59-L66】

## 3. Analysis of the First Engine (`KernelTM.v`)
### 3.1 Step Semantics
`step_tm` pattern matches on the fetched instruction and updates the state accordingly. The write, move, and branch cases invoke the shared helpers to manipulate the tape and head while advancing the program counter; the halt case leaves everything unchanged.【F:coq/kernel/KernelTM.v†L12-L29】 Crucially, each branch returns `mu_cost` unchanged by feeding back `st.(mu_cost)` into `update_state`.

### 3.2 Structural Limitations
Because the write case can only set the addressed cell to the supplied bit, the machine is capable of toggling cells but never introduces the special claim behaviour. When the fetched instruction is `H_ClaimTapeIsZero`, `step_tm` ignores its semantics and merely increments `tm_state`, leaving the tape and `mu_cost` untouched.【F:coq/kernel/KernelTM.v†L24-L29】 Consequently, no execution path decreases a `true` to `false` without an explicit write, and no path increments `mu_cost`; the value is invariant under every branch of `step_tm`.

### 3.3 Characterisation
From these clauses we conclude that the first engine is a standard tape-manipulating automaton: it can read, write, and move across the tape, but it is blind to the `H_ClaimTapeIsZero` opcode and treats the \(\mu\)-ledger as a fixed parameter. Its evolution space is limited to what can be expressed through the classical instructions alone.

## 4. Analysis of the Second Engine (`KernelThiele.v`)
### 4.1 Shared Behaviour
`step_thiele` copies the classical behaviour verbatim. The clauses for halting, writing, moving, and branching are syntactically identical to those in `step_tm`, including the unchanged `mu_cost` in those cases.【F:coq/kernel/KernelThiele.v†L7-L22】 This ensures that for purely classical programs, both machines follow the same trajectory.

### 4.2 Claim Semantics
The final clause differs: when `H_ClaimTapeIsZero` executes, the tape is replaced with an all-zero vector whose length matches the prior tape, and the \(\mu\)-ledger increments by one.【F:coq/kernel/KernelThiele.v†L23-L25】 The transition does not inspect the current cell values; it unconditionally forces the tape and records the cost. This is the only place where `mu_cost` can change, and the change is tied to performing the claim.

### 4.3 Characterisation
The second engine therefore strictly extends the first: it retains every classical capability while adding a primitive that collapses the tape to zeros in constant control time at the price of one \(\mu\)-unit. This instruction embodies a non-time resource expenditure distinct from the step count that the Turing kernel cannot emulate.

## 5. The Subsumption Proof – A Formal Reckoning (`Subsumption.v`)
### 5.1 Simulation Theorem
`thiele_simulates_turing` states that, for any finite fuel and any program consisting solely of classical instructions, running either machine yields identical end states.【F:coq/kernel/Subsumption.v†L48-L76】 The proof applies induction on the fuel: the helper lemmas show that if the fetched instruction is classical, the single-step evolutions agree, so the recursion proceeds in lockstep. Thus, on the shared subset of programs, the machines are behaviourally indistinguishable.

### 5.2 Strict Containment Theorem
`turing_is_strictly_contained` produces a one-instruction program consisting of the claim, an initial state filled with `true`, and a target state with all zeros and a \(\mu\)-cost of one.【F:coq/kernel/Subsumption.v†L78-L110】 Evaluating the program for one step under the Turing machine leaves the tape unchanged and the \(\mu\)-ledger at zero, whereas the Thiele execution reaches the zeroed tape with cost one.【F:coq/kernel/Subsumption.v†L92-L105】 Because these resulting states differ, the theorem concludes that there exists a program whose result is unattainable by the Turing kernel but achieved by the Thiele kernel.【F:coq/kernel/Subsumption.v†L107-L118】

### 5.3 Consequence
Combining the two theorems yields a precise containment relation: the Thiele kernel realises every behaviour of the Turing kernel on classical programs and, thanks to the claim instruction, reaches additional states beyond the classical frontier. This formalises mechanical subsumption entirely within the shared kernel universe.

## 6. The Nature of the μ-bit
Within this kernel, the \(\mu\)-bit is concretely defined as the cost increment triggered exclusively by executing `H_ClaimTapeIsZero`. The state record exposes `mu_cost`, but only the Thiele step semantics ever increase it, and each claim adds exactly one unit.【F:coq/kernel/Kernel.v†L4-L9】【F:coq/kernel/KernelThiele.v†L23-L25】 Because the Turing kernel cannot change this field, the resource is orthogonal to clocked evolution: a single claim expends one \(\mu\)-bit to achieve a tape transformation that the Turing machine cannot accomplish regardless of step count. The kernel thus separates two dimensions of computation—classical work tracked by instruction steps and non-classical insight quantified by \(\mu\)-bits—within a minimalist, mechanically verified model.
