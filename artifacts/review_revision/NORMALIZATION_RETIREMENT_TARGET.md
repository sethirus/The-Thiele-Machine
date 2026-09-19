# Candidate normalization retirement target (2026-09-12)

This is a source-inspection report, not a checked theorem. It neither changes nor closes the full C1/C2 target. No CPU, ISA, monograph, or status file was changed in preparing it. No Coq build or runtime test was run for this report.

## Exact implementation and existing proof boundary

- Module: `KamiHW.ThieleCPUCore.thieleCore`, source definition line 112. Its `thieleCoreS := getModuleS thieleCore` and `thieleCoreB := ModulesSToBModules thieleCoreS` are at lines 2792–2793.
- Actual actions occur as named entries of `Kami.Syntax.getRules thieleCore`: `mc_normalize_start` (2027), `mc_normalize_scan` (2039), `mc_normalize_emit` (2057), `mc_commit` (2081). Use those entries, not a newly transcribed Gallina transition, as theorem subjects.
- Raw construction: `mc_morph_header` (1861), `mc_morph_loop` (1889), `mc_copy_loop` (1919), `mc_join_loop` (1968); dispatch is part of rule `step` (351), with source/count selection around 942 and writes around 1638.
- Source SHA-256: `185c23f622fbeda4cb0a582079fe34f44ddfbca93f5f489bf280a587b588a6b3`.
- Emitted RTL: `thielecpu/hardware/rtl/thiele_cpu_kami.v`, SHA-256 `3dce8a80735f3f5d57222af4321e0d51978a00226e38912c516ab64678e9948d`.
- Reference list: `ThieleMachineComplete.normalize_coupling` (1080) uses `nodup nat_pair_eq_dec`; `relational_compose` (1208) is outer left-list order, inner right-list order, filtered by the join key.
- Existing `GraphReconstructionBridge.driven_step_wf`, `driven_trace_commutes`, `driven_step_morph`, `driven_step_compose`, and `driven_step_morph_tensor` concern snapshot/Gallina execution. They do not establish these actual rule actions.
- `F4_VerilogEvaluator` explicitly says at lines 17–28 that its string-to-nat evaluator is NOT `Kami.Semantics.SemAction`; its simple-action theorem does not cover this module's typed vector operations or emitted RTL.

Actual semantic hooks in `vendor/kami/Kami/Semantics.v`:
`SemAction` (382), `Substep.SingleRule` (621), `Step` (740), `Multistep` (952), `initRegs` (970), `Behavior` (1034), `traceRefines` (1063). `SemAction` takes the old typed register map and produces an update map, calls, and return. State update is `M.union updates old`. `Multistep` conses the newest label at the front, so a chronological rule list must be reversed when related to its labels.

## Proposed first checked result: actual normalization suffix

Proposed name `thieleCore_normalization_retirement` is a target label only, not an existing symbol.

Let H be a typed `RegsT` conforming to the actual register declarations. Read natural values by `wordToNat`, and read a pair at index k by the actual src/dst vector entries converted to naturals. Define `slice H b n` as the ordered list at b through b+n-1. Define `ActualRule k H H'` by membership of the named action in `getRules thieleCore`, `SemAction H (a type) updates empty_calls WO`, and `H' = M.union updates H`. Also prove that this relation embeds into `Step thieleCore`; do not merely use it as an independent assumed execution model.

Precondition for this LOCAL suffix lemma:

1. `mc_phase=5`; `mc_write_base=b`; `mc_write_ptr=e`; `coupling_pair_next_id=b`; `0<=b<=e<=16`.
2. `1<=d<16`, where d is `coupling_desc_next_id`; descriptor d is fresh; descriptor zero retains its reserved identity/empty role.
3. `slice H b (e-b)=raw`, and all raw slots are valid. All previously allocated descriptor ranges lie below b (empty ranges allowed). All existing descriptors and pair ranges satisfy their typed finite-table bounds.
4. Other multi-cycle engines have phase zero. No reset or external state-mutating methods interleave. Read-only observation methods are permitted. In particular exclude `loadInstr`, `apbWrite`, `setActiveModule`, `setTrapVector` for the global frame claim, rather than assuming that all methods are harmless.

Conclusion: there exists an execution of the ACTUAL named actions ending at H', with

- phase zero;
- descriptor d valid, base `b mod 16`, count `length (nodup nat_pair_eq_dec raw)`;
- pair-next `b + length (nodup nat_pair_eq_dec raw)` and desc-next `d+1`;
- ordered descriptor readout exactly `nodup nat_pair_eq_dec raw`;
- every old descriptor and pair slot below b unchanged, hence every old coupling readout unchanged;
- PC, mu, err, error_code, halted, ordinary registers, graph endpoint/identity fields, memories and other registers outside this suffix's write footprint unchanged;
- stale slots after the new end need not be erased. They are not allocated by descriptor readout. Their valid bits can remain true; an invariant claiming every valid slot lies below pair-next would be false after compaction.

Exactly `2 + n*(n+3)/2` normalization/commit rule firings occur, with n=e-b, thus at most 154. Empty input takes start then commit. For each of n candidates, scan includes one terminal out-of-range firing as well as every later candidate, then emit. This count is a derived candidate bound, not yet Coq checked.

The local result is deliberately an intermediate dependency: it preserves all state fields outside its write footprint, but does not pretend to prove missing label/region correspondence or that dispatch established the precondition. It is NOT a replacement for the full C1/C2 target.

## Progress assumptions and invariant

Kami `Substep` includes `EmptyRule`, and `Step` permits stuttering. Therefore universal bounded physical-time termination does not follow from `Multistep` existence alone. Prove (a) enabled-rule progress and bound in relevant rule firings, (b) eventual completion under weak fairness for continuously enabled coupling rules, and (c) only if claiming a wall-clock bound, a bounded scheduling delay K, giving at most K times the rule-firing bound. Generated BSC scheduling must be separately connected or trusted/tested. Clock running and reset deasserted are physical assumptions.

Normalization invariant with immutable ghost raw list, e=b+length raw:

- input index b<=i<e, output b<=out<=i, suffix slice [i,e) still equals the corresponding original raw suffix;
- compacted prefix [b,out) consists, in original order, of indices k<i whose original pair has NO equal occurrence at any later original index;
- scan phase 8 has i+1<=j<=e, and duplicate is precisely whether some k in [i+1,j) equals raw[i-b];
- after terminal scan, phase 9 has j=e+1 and duplicate is membership in the entire suffix;
- copying out<=i cannot corrupt an unread suffix. In-range i/out are below16, while j may equal16/17; the guarded comparison ignores its wrapped vector read at the terminal step;
- all increments are <32, so the five-bit index/count operations coincide with natural arithmetic, including end16 and empty base16. Commit stores base0 when b=16 and count0, an empty range.

A lexicographic phase/index measure (remaining candidates, remaining suffix comparisons, phase rank) proves progress. Alternatively sum the exact remaining scan/emit counts, taking account of the terminal scan.

## Integration with construction, conservative admission and failure

After dispatch, PC/mu/registers/morph tables have already changed, and the new morph points at descriptor d BEFORE descriptor d is valid. The abstract retirement relation must allow this as intermediate state, and count retirement at completion, not infer it from early PC advance or the existing instruction counter alone.

Raw admission policy, with workspace W=16-b:

- MORPH: raw count n <= W and n <= floor((127-memory_base)/2). Header failure sets err=true, error_code=ERR_COUPLING_INVALID, phase0, without descriptor commit. Accepted loading performs n pair writes, then normalization.
- COPY: raw length n1+n2 must fit W. Identity compose selects zero count on the identity side; tensor copies source1 then source2. If done, transition to normalization even at full capacity. If not done and ptr16, fail immediately without another pair write.
- JOIN: preserve the exact nested-loop order of `relational_compose`; raw MATCH count must fit W. Nonmatching combinations at full capacity are allowed. The first additional match at full capacity fails. Both empty inputs exit immediately to normalization.

Admission when the normalized list fits but the raw list does not fit is NOT promised by this implementation.

Failure is NOT transactional rollback: dispatch has already allocated/updated morph fields and accounting, and COPY/JOIN can have written a raw prefix. Descriptor/pair next counters are not advanced by their failure rule. The main step has `Assert !err`, so no subsequent instruction fires on this latched failure. A full theorem needs a distinct fault outcome exposing the exact partial state (or an explicitly justified fault observation), not falsely equating it to the ordinary successful VM step or a no-op rollback.

The local suffix proof covers only success from a validated raw range; separate header/copy/join failure lemmas and progress cases remain required.

## Representation obligations that this target cannot erase

The actual module stores 32-bit pair values, 16 pair slots, 16 descriptor slots with zero reserved, and 16 morph slots; `ptTable` stores region sizes, not arbitrary membership. MORPH labels are not stored; the testbench's `empty` label is a placeholder. Tensor endpoint behavior is still a separate correspondence obligation. Preserving these fields in a suffix proof cannot create absent representation. The full contract must implement the promised supported representations or explicitly record a target change.

For the larger retirement theorem, define boundary relation R over supported abstract state, actual typed map, and exact observable set. Prove reset/init R, dispatch into an intermediate invariant, per-actual-rule preservation, success to R of the abstract result, faults to defined fault relation, and progress. Labels, region membership, tensor endpoint selection, arithmetic/ledger bounds, and opcode-specific validation must be actual obligations of R and initialization, not opaque assumptions of the final theorem.

## Smallest next proof dependency and evidence

First missing dependency: isolate `mc_normalize_start` by getRules membership and prove its concrete `SemAction` update equation from the typed-register lookup hypotheses, plus frame preservation. The action has only reads, expressions, writes, assert, return; it has no calls. Proof should invert/construct `SemReadReg`, `SemLet`, `SemWriteReg`, `SemAssertTrue`, `SemReturn`, using lookup and distinct-write-name facts. Then scan/emit introduce vector update and word-range lemmas. No checked proof script for these actions currently exists in the inspected files; do not mark a suggested script as validated.

Suggested order: named-action membership lemma; generic typed lookup/update helpers; start exact-action lemma; scan exact-action lemma; emit exact-action lemma; commit exact-action lemma; common in-place invariant; well-founded progress; Substep/Step lifting; raw-building integration; full boundary R and faults; emitted RTL chain.

Validation for each future proof: compile its actual module with existing _CoqProject mappings; capture Check/Print and Print Assumptions of the theorem and expanded precondition/relation; run full dependent build after integration. Bind raw output and source hashes. Source-inspection commands for this report were sed/grep on the named files and sha256sum above, all successful except one exploratory grep used nonexistent coq/kernel/*.v (kernel files are nested); it did not run a proof check.

## Checked follow-up: start-rule dependency

The previously missing first action dependency is now proved in `/tmp/thiele-resume/NormalizationStartProbe.v`, without repository changes:

- `normalization_start_rule := nth 7 (getRules thieleCore) ...` selects the existing action; `normalization_start_rule_name` proves its actual name and `normalization_start_rule_in` proves membership in the actual module's rules.
- `normalization_start_actual_action` constructs `SemAction` under typed reads phase=5, base=b, end=e. Its exact update map writes mc_i=b, mc_j=b+1 (5-bit), mc_norm_ptr=b, mc_duplicate=false, and mc_phase=11 iff b=e, else8. It makes no finite-range assumption because this single start action's bitvector behavior is defined for every 5-bit b/e. Natural-range invariants remain required downstream.
- `normalization_start_actual_substep` lifts this to `Substep thieleCore old updates (Rle (Some "mc_normalize_start")) empty_calls`, via `SingleRule` and the checked membership lemma.
- Both action/substep theorem assumption reports list exactly `FunctionalExtensionality.functional_extensionality_dep`, inherited through the existing Kami definitions. No axiom or admitted declaration was added. The membership lemma is closed under the global context.
- This is existence with an exact update map, not yet uniqueness of every SemAction derivation, full Step lifting, initialization reachability, or retirement/progress across subsequent rules.

Reproduction: `python3 /tmp/thiele-resume/run_normalization_probe.py` invokes coqc with existing project mappings and COQPATH; latest exit0. `/tmp/thiele-resume/NormalizationStartProbe.log` includes the exact compiler command, exit code, Check types, expanded updates and Print Assumptions. This supersedes only the report's earlier no-proof status for the start-rule dependency. Scan, emit, commit, progress, frame integration, dispatch, failures, and downstream RTL correspondence remain open.
