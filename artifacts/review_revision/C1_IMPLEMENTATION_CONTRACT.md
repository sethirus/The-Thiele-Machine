# C1 finite implementation contract

This fixes the objects and intended finite observation for C2. It does **not**
assert retirement refinement, fault correctness, reachable-state preservation or
progress by itself; those are proved from the actual rules elsewhere in the tree
(`RetireMaster.v`, `TableInvariantsPreserved.v`, `TableInvariantsReachable.v`,
`RetireProgress.v`, `OutsideDomain.v`/`OutsideDomainMaster.v`, `RichFaultMaster.v`),
not by the admission predicates below. `STATUS.md` is the completion authority
for whether C1/C2 as a gate is open or closed; as of 2026-09-16 it records C1/C2
closed. Formal definitions: `coq/kami_hw/ImplementationContract.v`.

## Implementation objects and provenance

The source object is `ThieleCPUCore.thieleCore`; reset is
`initRegs (getRegInits thieleCore)`. `thieleCoreS`/`thieleCoreB` are its lowering
objects. The bus objects `ThieleCPUBusTop.thieleBusTopS`/`thieleBusTopB` are currently
aliases of those objects. The proof-level `bus_step` shadow model is not the
semantics of the actual `apbWrite` method.

Downstream objects are `build/kami_hw/thiele_hw.bsv`,
`thiele_hw_clean.bsv`, `mkModule1.v` and `mkModule1_synth.v` in that directory.
`c1_c2/source-hashes.json` retains the earlier interface-validation inputs;
`c2_dispatch/source-hashes.json` pins the earlier tensor/CSR and dispatch-factoring
checkpoint. Its generated artifacts passed the 18-test C3 audit, but predate the
VM alignment and label-storage changes recorded in `C2_DIVERGENCE_LEDGER.md`.
Current CPU source therefore requires fresh extraction, runtime regression and
C3 audit; `artifacts/rtl_pipeline_manifest.json` is historical until those pass.
Older manifests are preserved under `c3_audit/pre_tensor/`. C3 was regenerated and
re-audited against the current CPU source on 2026-09-16 (see `STATUS.md`); the
C1/C2 execution contract closed the same day. No updated physical measurements
are claimed.

## Words and supported opcodes

The supported set is exactly the 47 `OP_*` declarations in `ThieleTypes`, listed
in `supported_opcodes`, including CHSH_LASSERT and HALT. No Q-family opcodes or
reserved opcode 0x10 are included. The canonical assembler now covers all 47 hardware opcodes, including
`CHSH_LASSERT cost`; the four abstract Q-family opcodes remain outside this set.

ISA v2 words have version `[127:120]` = 2, format `[119:112]`, flags `[111:96]`,
ext1 `[95:64]`, ext0 `[63:32]`, opcode `[31:24]`, A `[23:16]`, B `[15:8]`, cost
`[7:0]`. `isa_v2_encode` matches `_encode`'s masking and placement. Textual inputs
must already fit their fields; masking is not a proof of lossless admission.
Assembly labels are instruction indices, with live fetch and branch targets
below 128. Format 0 uses zero flags; formats 1 and 2 also require zero flags.
Format 3 (morph inline) and 5 (cert inline) use subtype `[15:12]`, descriptor kind
`[11:8]` = 0 and inline length `[7:0]` in 1..8. Format 4 is descriptor-based,
with length zero and kind in 0..4. Opcode/format compatibility and descriptor
validity are checked by the actual `rich_fault` expressions.

All opcodes below retain the 8-bit cost lane. R(x) selects a register using four
bits; admitted textual register arguments are 0..15.

| Opcode(s) | Low-lane operands and extension interpretation |
| --- | --- |
| PNEW | A/B are the compact operands; B supplies region size. A textual region list is admissible only when exactly represented, not merely equal in length. |
| PSPLIT | A module, B split operand. Textual left/right sets are discarded by the legacy assembler and cannot be admitted on that basis. |
| PMERGE | A/B module operands. |
| LASSERT, LJOIN | A/B logic operands; descriptor/cert forms additionally select formula/cert payloads. SAT LASSERT uses the actual memory-scanning FSM. |
| MDLACC, PDISCOVER | A/B compact operands. |
| XFER | R(A) destination, R(B) source. |
| LOAD_IMM, LUI | R(A) destination, B literal. |
| CHSH_TRIAL | A[1] = x, A[0] = y, B[1] = a, B[0] = b. |
| XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK | A/B compact register operands; retain each opcode's `kami_step` meaning. |
| EMIT | A module, B disclosed bits. |
| REVEAL | A tensor index, B disclosed bits; REVEAL_EXT uses format 2 and ext0 for the index. |
| LOAD, HEAP_LOAD | R(A) destination, R(B) address register; heap address adds csr_heap_base. |
| STORE, HEAP_STORE | R(A) address register, R(B) source; heap address adds csr_heap_base. |
| ADD, SUB, AND, OR, SHL, SHR, MUL | R(A) destination, B[7:4] source 1, B[3:0] source 2. |
| JUMP, CALL | (A << 8) + B target; the current CPU still uses this low-lane target even with format 1. CALL uses the hardware stack convention. |
| JNEZ | R(A) test, B target; the current CPU still uses B even with format 1. |
| RET | No operand; hardware stack supplies return address. |
| CHECKPOINT, READ_PORT, WRITE_PORT, CERTIFY | A/B compact operands; port selection and certification follow the CPU decode and `kami_step`, with the correspondence still to prove. |
| TENSOR_SET | A[7:4] module 0..15; A[3:2] row, A[1:0] column; B unsigned 8-bit literal. Writes module_tensors, not mu_tensor. |
| TENSOR_GET | A[3:0] destination; B[7:4] module, B[3:2] row, B[1:0] column. |
| MORPH | Lossless assembler form MORPH_EXT: A destination, B source module, ext0[5:0] target module, ext0[12:6] coupling memory base; format 3, flags 4. |
| COMPOSE | COMPOSE_EXT: A destination, B first morph, ext0 second morph; format 3, flags 4. |
| MORPH_ID | A destination, B module; extended form uses format 3, flags 4. |
| MORPH_DELETE | A morph id; extended form uses format 3, flags 4. |
| MORPH_ASSERT | Extended form: A morph id, ext0 property checksum, format 5, flags 4. A checksum cannot be treated as an injective encoding of arbitrary strings. |
| MORPH_TENSOR | Extended form: A destination, B first morph, ext0[5:0] second morph, format 3, flags 4. The CPU always records ERR_MORPH_NOT_FOUND: represented regions are prefixes, never disjoint, so the kernel tensor product never succeeds on a represented state. |
| MORPH_GET | Extended form: A destination, B morph id, ext0 selector, format 3, flags 4. |
| CHSH_LASSERT | Witness buckets are in state; the instruction launches the CHSH FSM. Assembler form: CHSH_LASSERT cost. |
| HALT | No data operands. |

This table records the finite operand surface, not a decoder correctness theorem.
C2 must relate each actual decoded instruction to `kami_step`; in particular,
legacy MORPH/COMPOSE/MORPH_TENSOR/MORPH_GET/MORPH_ASSERT discard extra textual
operands. Use the explicit extended forms for the full operand contract. Arbitrary
textual regions, labels, property strings and extra operands are not silently
identified with their lossy encodings.

## Reset, loading and finite storage

All 139 register values are retained by `HWB` and `hwb_regs`. Widths are 32-bit
words, 16 registers, 128 data words, 128 instruction words, 64 partition slots,
16 morph slots, 16 slots in each descriptor/metadata table, 16 coupling pairs,
and 16 module tensors of 16 words each. The assertion buffers each have 64 words.
Allocation counters have an extra bit so exhaustion is representable.

Data memory, both tensors, csr_status and csr_heap_base reset to zero (`Default`).
Partition, morph and coupling-descriptor next-id reset to 1 (coupling descriptor zero is reserved); the other descriptor and pair counters reset to 0.
Active module resets to 1; trap vector resets to 3840. That trap address is outside
128-word instruction storage: a Bianchi trap is an observable outside-domain
outcome, not a claim that a handler at 3840 can execute faithfully. Fetch truncates
the PC to seven bits; admitted execution prohibits such aliasing.

`loadInstr` accepts a 7-bit address and 128-bit word and updates that imem cell.
The actual `apbWrite` method latches load address at 128 and full-width instruction
data at 132, then writes imem on a nonzero kick at 136. Addresses 152 and 156 set
active module and trap vector. Load before rule execution; do not interleave host
mutations with the retirement trace. There is no internal loading lock.

`.DATA`/`INIT_MEM` are assembler output metadata, not CPU methods. The core has no
host data-memory load or CSR-status/heap-base setter. Nonzero memory can be built
by admitted instructions. Arbitrary typed boundaries can contain arbitrary CSR
values, but this is distinct from reachability from reset; no loading theorem
for arbitrary such states is claimed.

## Observation and representable domain

`hwb_snapshot` explicitly maps every `KamiSnapshot` field, including module
tensors, status, heap base, cert address, logic accumulator and mstatus.
CSR err is 0/1 from the hardware err latch. `hwb_rich` reconstructs all valid
morph, coupling, formula, cert and metadata entries; coupling pairs are read
only below `coupling_pair_next_id`, since cells above it are unallocated scratch. The assertion shadow is
the empty shadow: LASSERT FSM registers are scratch, and `kami_step` never
reads or writes that shadow.
Finite arrays extend by zero or None outside their physical domain, rather than
wrapping indices. `hwb_observes` is equality with this snapshot. FSM scratch,
instruction memory, active module and trap vector remain in HWB and admission /
phase invariants even though KamiSnapshot does not expose them.

A coupling label is stored per descriptor as a list of atoms joined by ";":
an atom count (`coupling_desc_label_len_table`) and a mask whose bit k marks
atom k as the kernel's "empty" label, otherwise the empty string
(`coupling_desc_label_table`); observation uses `atom_label n mask`
(`represented_label`). MORPH admits only the empty in-memory label and commits
one "" atom; a morphism without a valid descriptor carries the single "empty"
atom; COMPOSE appends the second list above the first, which is the kernel's
`l1 ++ ";" ++ l2` (`atom_label_compose`). Module regions are
nonempty prefixes `seq 0 size`, size at most 128 (`represented_region`), matching
the existing graph reconstruction; size zero denotes absence. Endpoints are
memory indices 0..127 (`represented_endpoint`), additionally required to belong
to source/target regions for valid couplings. Arbitrary labels, empty allocated
regions and arbitrary finite subsets are not represented. C2 must prove admitted
operations preserve this representation or report a concrete implementation gap;
it must not erase labels or replace sets by sizes to manufacture refinement.

The target is `kami_step`. The further VM link reuses `EmbedStep`, `EmbedStep_WF`
and `FullEmbedStep` with their existing instruction, bound, representation and
well-formedness premises. Those premises remain obligations at each application.
`TensorDispatch` proves actual set/get writes for every canonical 4-bit
module operand and other operand/cost bits, with arbitrary tensor/register state;
by itself this write projection does not discharge the full comparison. That
full comparison is discharged separately, for every admitted instruction, by
`RetireMaster.Retire`'s own conclusion `hwb_snapshot d = kami_step (hwb_snapshot b) i`
(see `STATUS.md`'s C1/C2 closure entry, 2026-09-16). The further abstract VM
link through `EmbedStep`/`EmbedStep_WF`/`FullEmbedStep` is unaffected by that
closure and remains a separate obligation at each application.

## Admission, faults, capacity and scheduling

`live_boundary` requires all three FSM phase registers zero and err/halted false.
`in_region_address` requires the full mathematical address below both 128 and the
active module size; heap addition must not overflow before this test.
The actual CPU truncates register/heap/stack addresses to seven bits **before**
`check_bounds`. Thus a raw address such as 128 can alias cell zero and pass the
hardware locality guard. Nonaliasing is an admission requirement; a halt for
all full-width out-of-range addresses is not implemented and must not be claimed.
`finite_pc_mu` requires nonaliasing current/next fetch and nonwrapping mu.
All relevant arithmetic, witness/tensor sums, address additions and counters
need bounds wherever natural-number target semantics differs from word arithmetic.
The individual stored PC and mu are intrinsically 32-bit, but next-state natural
bounds and preservation are still proof obligations.

Fault predicates are the actual dispatch LET expressions. C2 must split on them
and prove each result; there is no assumed fault-correctness axiom:

| Guard | Required observation, with simultaneous guards retained |
| --- | --- |
| bianchi_violation | PC = trap vector; error code ERR_BIANCHI_VAL; mu unchanged. Bianchi alone does not latch err. Other simultaneous guards can latch err/halted. The sum used by hardware is a 32-bit sum. |
| locality_violation | err and halted; trap PC. If Bianchi is false, code ERR_LOCALITY_VAL. `kami_step` has no locality check, so this is the specified outside-domain outcome. |
| ptable_overflow_violation | err and halted; trap PC; ERR_PARTITION_VAL when higher-priority code guards are false. |
| nfi_violation (PDISCOVER cost below declared bound) | err and halted; trap PC; ERR_LOGIC_VAL subject to the exact code priority. |
| rich_fault | err; trap PC. Code priority: version, format, inline malformed, descriptor range, table overflow, invalid cert descriptor. Does not by itself set halted. |
| morph_runtime_fault | err; PC advances by one unless a higher-priority guard traps; actual morph-runtime error code. Does not by itself set halted. |

Dispatch code priority is Bianchi, locality, partition overflow, NFI, rich, morph
runtime, LASSERT trap, CHSH trap, otherwise old code. The high-value lock and
CHSH_TRIAL tensor gate have been removed. The CHSH assertion FSM reports
ERR_LOGIC on failure. HALT sets halted and advances PC unless a higher-priority
guard traps. `logic_acc` and `mstatus` are preserved; PDISCOVER writes no data
register; CHSH_TRIAL charges its instruction cost without an x=1 surcharge. Do not infer a full frame from a fault name:
charges, diagnostic counters, partial allocations and every written register
need their actual branch result proved. Multi-cycle faults require a separate
partial-allocation invariant.

`raw_pair_capacity` retains raw intermediate size: used prefix + MORPH input
count, copy count, or raw matching join output count must be at most 16, before
duplicate elimination. Descriptor/morph allocation must separately fit. Normalization
must preserve the exact last-occurrence order. A smaller normalized result does
not admit an overflowing raw operation.

Traces use Kami rule semantics, with no host methods during execution
(`execution_schedule` lists CPU rule names). Reachable FSM invariants must prove
phase exclusivity; arbitrary typed HWBs need not have mutually exclusive active
phases. Progress assumes that an enabled rule is eventually scheduled (or uses
the concrete selecting runner). Kami semantics alone permits stuttering and is
not a fairness theorem. C2 must prove enabledness, phase variants, retirement and
composition for all 12 rules under the stated scheduler condition.

## Proof ledger

Checked interface lemmas establish the opcode count, direct tensor/CSR
projections and stored PC/mu word bounds. C2 step 1 establishes completeness of the typed HWB representation.
They do not prove that CPU execution implements these observations. Dispatch
fault branches, all-opcode refinement, reset/reachability invariants, multi-cycle
progress and emitted-artifact provenance remain the numbered C2/C3 obligations
in STATUS.md. No gate closes merely by compiling these definitions.

The exact `Print Assumptions` census is in `c1_c2/contracts.log`:
`supported_opcode_count`, `hwb_snapshot_module_tensors`, `hwb_snapshot_csrs` and
`hwb_pc_mu_word_bounds` are closed under the global context. The general map
representation results depend on `Eqdep.Eq_rect_eq.eq_rect_eq` through the
existing Kami equality machinery. `cpu_reset_run_has_boundary` additionally
inherits `FunctionalExtensionality.functional_extensionality_dep` from
`CoreTyping.cpu_reset_run_register_schema`. These are existing library assumptions,
not new declarations; the representation results are not advertised as axiom-free.

Dependency-enabled `coqchk` passed (exit 0, 730.905 s, peak 350 MB), with no
unsafe type-in-type, (co)fixpoint or assumed-positivity entries. Its imported-library
inventory also lists the pre-existing vendor `Kami.Lib.CommonTactics.cheat`
declaration. None of the named results above has `cheat` in its `Print Assumptions`
output. The checker inventory and theorem-specific dependency census are distinct.
