# Project Cerberus: A Provably Secure Kernel

This directory contains the formal specification and machine-checked proof of a minimal, provably secure kernel, designed using the principles of the Thiele Machine.

The file [`Cerberus.v`](Cerberus.v) contains a formal Coq proof of the following theorem:

- [`pc_never_exceeds_program_bounds`](Cerberus.v)

This theorem provides a mathematical guarantee that the kernel's program counter (PC) will never exceed the bounds of the program, for any program and any number of execution steps. In other words, the PC will always point to a valid instruction within the program or to a `Halt` state, and can never run off the end of the program—a common source of low-level exploits.





License: See repository LICENSE.


## Roadmap: Planned Improvements and Goals

The following improvements are planned for Project Cerberus:

1. **Formal Memory Safety**  
	Extend the formal model and proofs to guarantee that all memory accesses (loads and stores) are always within valid bounds, eliminating out-of-bounds memory errors.

2. **Richer Instruction Set**  
	Add and formally verify more complex instructions (e.g., arithmetic, branching, I/O), ensuring each new feature preserves safety and correctness.

3. **Liveness and Progress Properties**  
	Prove not just safety (nothing bad happens), but also liveness (something good eventually happens), such as guaranteed program termination or progress.

4. **Compositional Reasoning**  
	Structure the proofs so that properties of small components can be reused and combined, making it easier to scale up to larger kernels.

5. **Executable Extraction**  
	Connect the formal model to executable code, so that the verified kernel can be run or integrated into real systems.

6. **Automation and Proof Engineering**  
	Refactor and automate proofs for maintainability, readability, and easier extension as the kernel evolves.

