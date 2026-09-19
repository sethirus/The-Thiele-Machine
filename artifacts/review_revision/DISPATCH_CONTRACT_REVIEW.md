# Dispatch/descriptor contract investigation

This is a bounded source investigation, not an inductive invariant proof.

A satisfiable successful-run invariant can use natural observations B of
coupling_pair_next_id, D of coupling_desc_next_id, and M of morph_next_id:
0<=B<=16, 1<=D<=16, 1<=M<=16; descriptor0 remains an empty special case;
every committed nonzero descriptor q<D is valid and has base+count<=B;
every clean-idle live nonzero morph descriptor names such a committed q;
all pair entries below B are valid. Do not require valid pair flags only below
B: raw normalization leaves stale valid flags beyond the compacted endpoint.
Reset supplies B=0,D=1,M=1, zero tables and idle phases (CPU lines275–315,
COUPLING_DESC_NEXT_ID_INIT line78, ThieleTypes initial values lines89–94).
Existing input ranges then precede fresh append base B. Successful dispatch
requires D<16/M<16, so new descriptor slot D cannot alias q<D; commit advances
to at most16 and preserves previous pair payloads by the new prefix proofs.

Busy states need an explicit pending morph referencing descriptor D. Header
failure can leave this reference uncommitted at phase0 with err=true. Thus
idle alone cannot imply the clean morph-reference condition, and fault states
must receive their own exact partial-allocation contract.

Actual dispatch expressions: allocation conditions CPU887–910; descriptor
selection/identity routing/source ranges CPU937–995; write-base/pointer and
zero cursors CPU1638–1651. MORPH base is zero-extended from seven bits
(CPU741–745,1639–1641). Source descriptor validity/range bounds are not checked
by copy/join dispatch; they must follow from the invariant. Capacity premises
remain per-operation: raw MORPH count plus B, copied c1+c2 plus B, or raw
matching join-output count plus B. Normalized size alone is insufficient.

Confirmed distinct bug: nominal success predicates omit the global dispatch
fault gate. Morph-table writes check seven faults (CPU1470–1512), but the old
mc_phase write CPU1638 unconditionally used mc_new_phase. A version-invalid
MORPH therefore trapped without allocating a morph yet still allocated a
coupling descriptor/pairs in subsequent clocks. Reproduction is in
/tmp/thiele-resume/dispatch-probe/: two-instruction PNEW→malformed MORPH setup,
continued-clock scratch testbench, raw before traces and hashes. The durable
four-case regression has 2 failing invalid-version cases and 2 passing controls.
This is separate from the documented later header-capacity failure.

Prepared minimal canonical fix dispatch-gate.patch applies exactly the same
seven-fault condition to mc_phase activation. It leaves subsequent header
failure behavior unchanged. No repository CPU/RTL source was mutated during
this investigation. No further fault classes were investigated after the
explicit quota-limit instruction.
