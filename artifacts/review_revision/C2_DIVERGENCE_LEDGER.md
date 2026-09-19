# C2 divergence ledger

This ledger compares the actual CPU (`ThieleCPUCore.thieleCore`) with the
refinement target `kami_step` for every supported opcode and FSM. Each entry
records how the divergence is resolved. Resolution follows Devon's 2026-09-14
decision: where the CPU disagrees with `vm_apply`/`kami_step` on VM-visible
state and no admission premise applies, the CPU changes. Hardware-only fields
are aligned on the `kami_step` or observation side. A guard that the VM lacks
but that produces a specified error stays an outside-domain outcome with an
explicit admission premise.

VM-visible fields are those read by `abs_phase1`: pc, mu, registers, memory,
the partition graph, CSRs, `mu_tensor`, err, `logic_acc`, `mstatus`, witness
counters and `certified`. Hardware-only snapshot fields are halted,
`partition_ops`, `mdl_ops`, `info_gain`, `error_code`, `module_tensors` and the
rich tables outside the graph projection.

## CPU changes

| Divergence | CPU behaviour before | VM / `kami_step` | Resolution |
| --- | --- | --- | --- |
| Logic-gate lock | LASSERT XORs `logic_acc` with 0xCAFEEACE; every step rewrites `mstatus` from `logic_acc`; REVEAL, PDISCOVER and CHSH_TRIAL latch err and halt while `logic_acc` differs from the key. | `logic_acc` and `mstatus` never change; no lock. | Removed from the CPU. |
| HALT pc | pc held. | pc advances. | CPU advances pc. |
| PDISCOVER register | `regs[A] := ptTable[B]`. | No register write. | Write removed. |
| CHSH_TRIAL x=1 | Adds 256 to mu; latches err when the `mu_tensor` total is zero. | Charges cost only; no tensor gate. | Surcharge and gate removed. |
| Morph runtime fault | pc := trap vector. | err latched, pc advances, mu charged. | CPU advances pc (in progress). |
| LASSERT with kind 0 | mu + cost + 1. | mu + flen x 8 + cost + 1, flen being the in-memory header. | CPU adds header x 8 (in progress). |

## Observation and `kami_step` alignment (hardware-only fields)

| Field | CPU | `kami_step` | Resolution |
| --- | --- | --- | --- |
| `info_gain` on EMIT | + B. | unchanged. | `kami_step` adds the payload bit count (in progress). |
| `info_gain` on PDISCOVER | + B. | unchanged. | Admitted encodings have B = 0; B carries no abstract operand. |
| `info_gain` on REVEAL | unchanged. | + bits. | `kami_step` leaves `info_gain` unchanged, as the CPU counts only PDISCOVER and EMIT. |
| `error_code` on LASSERT / CHSH_LASSERT failure | ERR_LOGIC_VAL. | unchanged. | `kami_step` sets the code (in progress). |
| `error_code` on morph runtime fault | fault-specific code. | unchanged. | `kami_step` sets the code (in progress). |
| LASSERT scratch | step and FSM rules write `lassert_*` scalars. | carried in `rich_lassert_state`. | FSM scratch leaves the boundary observation (in progress). |
| Pair cells dropped by normalization | Compaction writes retained pairs below the new `coupling_pair_next_id` and leaves dropped cells between it and the loading end marked valid. | `write_coupling_pairs_aux` writes exactly the deduplicated pairs; cells above the pointer stay empty. | The observation reads coupling pairs only below `coupling_pair_next_id`; the cells above it are unallocated scratch, not VM-visible (the graph projection reads pairs only through descriptor ranges). |

## VM change: LASSERT failure sets the CSR error flag

The VM latched `vm_err` on a failing LASSERT but left `csr_err` unchanged,
while a failing CHSH_LASSERT and every other VM error path set `csr_err` to 1.
The CPU has no separate `csr_err` register; the boundary observation derives
it from `err`. No admission premise can exclude a failing check, so the two
could not agree. Devon chose on 2026-09-15 to change the VM: `step_lassert`,
`vm_apply`, the unbounded sibling `VMUnboundedStep` and `kami_step` now set
`csr_err` to 1 when the LASSERT check fails. The CPU is unchanged. The
extraction `build/thiele_core.ml` carries the change and the OCaml runner
`build/extracted_vm_runner`, which the Python harness calls, is rebuilt from
it; `thielecpu/generated/generated_core.py` holds only instruction-name tables
and regenerates byte-identical. `ThieleMachineComplete.v` keeps its own
presentation copy, as recorded for the CPU lock.

## CPU changes for COMPOSE labels and MORPH_TENSOR

COMPOSE labels. The kernel and `kami_step` label a composed coupling
`l1 ++ ";" ++ l2`. The CPU stored no label and the observation reported the
empty string, so every successful COMPOSE disagreed on the descriptor label.
MORPH admits only the empty in-memory label, and a morphism without a valid
descriptor (MORPH_ID, identity morphisms, legacy self-MORPH) has the kernel's
`empty_coupling_data` label "empty". Every label reachable in the represented
domain is therefore a ";"-joined list of the atoms "" and "empty". Devon chose
on 2026-09-15 to store that list in the CPU (a first choice of a ";" count
was revised once the "empty" atom was found): a 6-bit atom count and a 32-bit
mask per descriptor, bit k marking atom k as "empty". The step rule commits one
"" atom for MORPH and, for COMPOSE, the count n1 + n2 and the mask
mask1 + (mask2 << n1), a side without a valid descriptor contributing one
"empty" atom. `hwb_rich` reports `atom_label n mask`, and `atom_label_compose`
proves the concatenation identity. Capacity premise: n1 + n2 at most 32.

MORPH_TENSOR. Reconstructed module regions are `seq 0 size` with size
nonzero, so any two regions share address 0. The kernel's
`graph_tensor_morphisms` requires disjoint source and target regions, and so
never succeeds on a reconstructed graph (`snap_graph_tensor_none`); `kami_step`
always records ERR_MORPH_NOT_FOUND. The CPU allocated a morphism with the
first morphism's source, the second's target and concatenated pairs. Devon
chose on 2026-09-15 to make the CPU fault: MORPH_TENSOR now always latches
err with ERR_MORPH_NOT_FOUND, charges its cost and advances pc. It no longer
allocates, enters the coupling FSM or counts toward rich-table overflow.

## Admission premises found by the LASSERT scan proof

The CPU scan and the kernel's model and countermodel checks agree when the
formula declares at least one clause and its `flen` literal words contain a
terminator for every declared clause. With zero declared clauses the kernel
check fails while the CPU treats the first clause as the last; with too few
terminators the kernel check fails while the CPU reads past `flen`. Both are
admission premises of the LASSERT refinement, together with the header
`flen` equal to the instruction's `flen`, no 32-bit wrap of the formula
pointer and of mu, and the trap vector at `LASSERT_TRAP_PC`.

## Admission premises found by the MORPH retirement proof

The CPU loads, deduplicates and commits exactly the kernel's serialized pairs
when: the pair count plus the pair pointer is at most 16 and the pointer is
below 16 (at pointer 16 with no pairs the 4-bit descriptor base records 0,
the kernel 16); the pairs and the label word lie below address 128 (the CPU
check admits pairs ending at address 127, which leaves the label word at
address 128 where the kernel's read wraps); the label word is zero, the only
label the CPU represents for MORPH; and every declared pair lies within the
source and target regions, since the CPU does not filter.

## Outside-domain outcomes kept

Bianchi violation, locality violation, partition-table overflow, the PDISCOVER
declared-bound guard, rich-format faults, rich-table overflow, morph descriptor
and pair capacity, and assertion-buffer extents keep their specified CPU
outcomes. Each has an admission premise in the refinement theorem.

## Value-width premises

The CPU stores 32-bit words; `kami_step` uses naturals or 64-bit words. The
admission premises require no 32-bit wrap where the target does not wrap the
same way: ADD, MUL, SHL and LUI results below 2^32; SUB without borrow; mu,
pc, witness counters and tensor sums below 2^32; addresses and pointer sums
below 128 without aliasing.
