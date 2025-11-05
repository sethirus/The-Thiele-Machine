> **Status update (October 2025):** The authoritative kernel proof lives in `coq/kernel/`. This README is preserved for the archived `coq/thielemachine` development.

# Project Cerberus: The Thiele Kernel

This directory contains the formal specification and machine-checked proof of a minimal, **meta-logically self-auditing kernel**—a Thiele Machine kernel. This kernel is not only provably safe, but its safety is enforced at runtime by a logic oracle and paradox detection, embodying the Thiele Machine's foundational principles.

The file [`Cerberus.v`](coqproofs/Cerberus.v) contains a formal Coq model and theorems, including:

- [`pc_never_exceeds_program_bounds_thiele`](Cerberus.v):
	 - **If** the kernel's logic oracle (`logic_oracle`) confirms that all program axioms and stepwise safety checks are consistent,
	 - **Then** the program counter (PC) will never exceed the bounds of the program, for any program and any number of execution steps.
	 - If a paradox is detected, the kernel halts and sets `paradox_detected := true`.

This is the first kernel to make its own logical safety contract explicit and enforce it at runtime, not just in the proof but in the operational semantics.

## Thiele Machine Features

- **Self-Auditing State:** The `MachineState` tracks `mu_cost` (information cost) and `paradox_detected` (logical inconsistency flag).
- **Meta-Logical Oracle:** Every step is checked by `logic_oracle`, which verifies that the program's axioms and the current instruction's safety encoding are consistent.
- **Axiom Encoding:** The function `encode_safety_axioms` translates each instruction and its context into a logical form for the oracle.
- **Emergent Safety:** Theorems are conditional on the oracle's consistency, isolating the engineering of the oracle from the architecture of the kernel.

## Roadmap: Planned Improvements and Goals

1. **Realistic Oracle and Encoding**  
	Implement a real logic oracle and a robust axiom encoding to move beyond the current stub.
2. **Richer Instruction Set**  
	Add and verify more complex instructions (arithmetic, branching, I/O) with meta-logical safety.
3. **Liveness and Progress Properties**  
	Prove not just safety, but also liveness and progress, in the presence of the oracle.
4. **Compositional Reasoning**  
	Structure proofs for modularity and scalability.
5. **Executable Extraction**  
	Connect the formal model to executable code, preserving meta-logical safety.
6. **Automation and Proof Engineering**  
	Refactor and automate proofs for maintainability and extension.

---

License: See repository LICENSE.
