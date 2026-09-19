# Fixed-program graph input audit

The bounded source audit found no register-indirect graph/tensor/morphism operand in `Kernel.SimulationProof.vm_apply`: module/morphism IDs, tensor indices, TENSOR_SET values and MORPH coupling bases are instruction literals. TENSOR_GET, MORPH_GET and allocated morph IDs pass through 64-bit-truncating `write_reg` (SimulationProof470–552; VMState2169). Allocation counters themselves increase without wrapping (VMState305,395). PSPLIT/PMERGE reduce their operand IDs modulo64; that does not wrap the fresh allocation counter (SimulationProof269–278).

MDLACC, LJOIN and PDISCOVER are pure advance in this runner. REVEAL increments the separate unbounded `vm_mu_tensor`, but no audited opcode reads it into control. TENSOR_SET writes a literal natural, not a computed counter value. A blanket fixed-ID obstruction would still need to handle MORPH_TENSOR's stored endpoint lookups and whole-graph `graph_find_region` search (VMState599 onward). This is not a whole-ISA impossibility argument.

## Checked initial-input route

`well_formed_graph` (VMState230) does not require unique IDs. A graph containing repeated ID0 modules with successive tensor tokens therefore satisfies that named predicate when `pg_next_id>0` and its morphism list is empty. TENSOR_GET at literal module0 reads the first token. PSPLIT0 removes the first matching module, then prepends two fresh modules. Starting the allocation counter at64 ensures these new IDs do not equal0, so lookup skips them and exposes the next token.

`/tmp/thiele-resume/GraphInputStreamProbe.v` compiled successfully with six results: general well-formedness, non-unique IDs, first token1, second token2 after one actual PSPLIT, fresh-ID prefix `[65;64;0]`, and exhausted read0 after two actual PSPLITs. The latter observations use actual `vm_apply` instructions; the fresh-prefix example uses `vm_compute`. No repository source was changed.

This supplies a concrete potential sequential input channel using a fixed instruction vocabulary and a preloaded graph. Its lack of reachability from `empty_graph` does not automatically disqualify an allowed initial-input encoding. No push-back, reusable second counter, or general writable store has been demonstrated. The probe does not yet prove a uniform `run_vm` loop consuming arbitrary streams.

## Exact next dependency

Prove the fixed instruction-list stream-consumption macro uniformly over arbitrary token lists, then determine how to combine that initial read-only input with sufficient internally writable unbounded storage and independently controllable tests. A stream alone does not establish a self-interpreter.
