# ISA Proof-Impact Checklist

**Date**: 2026-03-27
**Purpose**: Map every Thiele Machine opcode to the theorems that depend on it. Use this checklist whenever an opcode is added, removed, or modified.

**Key predicates**:
- `cert_addr_setterb`: Can set `csr_cert_addr` (supra-cert channel) — 5 ops
- `is_cert_setterb`: Can touch any cert channel (adds `read_port` + `certify`) — 7 ops
- `instruction_cost = S cost`: Costs at least 1 regardless of argument — 6 ops (subset of is_cert_setterb)

---

## Opcode Impact Table

| Opcode | cert_addr_setter? | is_cert_setter? | cost formula | Sets vm_err? | Touches vm_graph? | Proof files impacted |
|---|---|---|---|---|---|---|
| `pnew` | NO | NO | `cost` | YES (module alloc fail) | YES (adds module) | MuLedgerConservation, InsightTaxonomy |
| `psplit` | NO | NO | `cost` | YES | YES | MuLedgerConservation |
| `pmerge` | NO | NO | `cost` | YES | YES | MuLedgerConservation |
| `lassert` | **YES** | **YES** | `encoded_formula_units×8 + S cost` | YES | NO | AbstractNoFI §8, InsightTaxonomy, MuLedgerConservation |
| `ljoin` | **YES** | **YES** | `S cost` | NO | NO | AbstractNoFI §8, InsightTaxonomy, MuLedgerConservation |
| `mdlacc` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `pdiscover` | NO | NO | `cost` | NO | YES | MuLedgerConservation |
| `xfer` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `load_imm` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `load` | NO | NO | `cost` | YES (OOB) | NO | MuLedgerConservation |
| `store` | NO | NO | `cost` | YES (OOB) | NO | MuLedgerConservation |
| `add` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `sub` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `jump` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `jnez` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `call` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `ret` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `chsh_trial` | NO | NO | `cost` | NO | NO (updates vm_witness) | MuLedgerConservation, VerilogRefinement |
| `xor_load` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `xor_add` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `xor_swap` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `xor_rank` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `emit` | **YES** | **YES** | `S cost` | NO | NO | AbstractNoFI §8, InsightTaxonomy, MuLedgerConservation |
| `reveal` | **YES** | **YES** | `S cost` | NO | NO | AbstractNoFI §8, InsightTaxonomy, MuLedgerConservation |
| `oracle_halts` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `halt` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `checkpoint` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `read_port` | NO | **YES** | `S cost` | NO | NO | AbstractNoFI §10, MuLedgerConservation |
| `write_port` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `heap_load` | NO | NO | `cost` | YES (OOB) | NO | MuLedgerConservation |
| `heap_store` | NO | NO | `cost` | YES (OOB) | NO | MuLedgerConservation |
| `certify` | NO | **YES** | `S cost` | NO | NO | AbstractNoFI §10 (vm_certified channel), PrimeAxiom, MuLedgerConservation |
| `and` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `or` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `shl` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `shr` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `mul` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `lui` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `tensor_set` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `tensor_get` | NO | NO | `cost` | NO | NO | MuLedgerConservation |
| `morph` | NO | NO | `cost` | YES (src/dst invalid) | **YES** (adds morphism) | MuLedgerConservation, InsightTaxonomy, ShadowProjection |
| `compose` | NO | NO | `cost` | YES (morphs invalid) | **YES** (adds morphism) | MuLedgerConservation, InsightTaxonomy |
| `morph_id` | NO | NO | `cost` | YES (module invalid) | **YES** (adds morphism) | MuLedgerConservation, InsightTaxonomy |
| `morph_delete` | NO | NO | `cost` | YES (morph not found) | **YES** (removes morphism) | MuLedgerConservation, InsightTaxonomy, ShadowProjection (probe) |
| `morph_assert` | **YES** | **YES** | `S cost` | YES (morph not found) | NO | AbstractNoFI §8, InsightTaxonomy (core NoFI), MuLedgerConservation |
| `morph_tensor` | NO | NO | `cost` | YES (morphs invalid) | **YES** (adds morphism) | MuLedgerConservation, InsightTaxonomy |
| `morph_get` | NO | NO | `cost` | YES (morph not found) | NO | MuLedgerConservation |

**Total opcodes**: 46

---

## Impact Zones by Proof File

### If you change ANY opcode in cert_addr_setterb (lassert, ljoin, emit, reveal, morph_assert):
- **AbstractNoFI.v**: `no_free_certification` and `cert_addr_setter_cost_pos` — the case analysis over cert-setters must still hold
- **InsightTaxonomy.v**: `certified_insight_nonfree`, `no_free_certified_insight` — check they still apply
- **ShadowProjection.v**: If morph_assert is changed, check `shadow_separation_theorem`

### If you add a NEW cert_addr_setter:
1. Add it to `cert_addr_setterb` in AbstractNoFI.v
2. Verify `instruction_cost` uses `S cost` for the new opcode
3. Run `make -C coq -j4` and verify zero Admitted
4. Update this checklist

### If you change instruction_cost for a cert-setter to `cost` (removing S):
1. `cert_addr_setter_cost_pos` will break (proof by case analysis)
2. `no_free_certification` is invalidated
3. The entire NoFI story collapses — this is a breaking change

### If you change vm_certified semantics (currently only set by certify):
- **AbstractNoFI.v §10**: `no_free_certification_certified` — must verify the new opcode uses `S cost`
- **PrimeAxiom.v**: `vm_apply_certified` — case analysis over all opcodes for vm_certified

### If you add/remove opcodes that touch vm_graph (morph, compose, morph_id, morph_delete, morph_tensor, pnew, psplit, pmerge, pdiscover):
- **ShadowProjection.v**: The shadow_proj definition and separation theorems are NOT affected (shadow_proj ignores vm_graph). But the choice of probe for `shadow_separation_theorem` depends on morph_delete's semantics.
- **InsightTaxonomy.v**: If the new opcode is a cert-addr-setter, update `_not_cert_setter` lemmas

### If you add/remove opcodes that touch vm_err:
- **HardwareBisimulation.v**: The bisimulation includes vm_err in the refinement relation
- No NoFI theorems directly depend on vm_err (they depend on csr_cert_addr and vm_certified)

### If you change any opcode cost from `S cost` to `cost` (downgrade):
- **MuLedgerConservation.v**: `vm_apply_mu` — case-analysis proof will still hold (mu grows by `cost` instead of `S cost`)
- If the opcode is a cert-setter: NoFI breaks (see above)
- If not a cert-setter: cost change is safe w.r.t. NoFI

---

## Checklist for Adding a New Opcode

```
[ ] 1. Add constructor to vm_instruction inductive type in VMStep.v
[ ] 2. Add arm to instruction_cost match (choose cost vs S cost deliberately)
    [ ] If it sets csr_cert_addr: MUST use S cost
    [ ] If it sets vm_certified: MUST use S cost
    [ ] If structural only: cost is fine
[ ] 3. Add arm to vm_apply match in VMStep.v
[ ] 4. If cert-addr-setter: add to cert_addr_setterb in AbstractNoFI.v
[ ] 5. If cert-setter (any channel): add to is_cert_setterb in VMStep.v
[ ] 6. Run make -C coq -j4 and confirm zero Admitted (MuLedgerConservation will
       need a new case in vm_apply_mu)
[ ] 7. Run python3 scripts/inquisitor.py
[ ] 8. Update isa_proof_impact.md (this file)
[ ] 9. Update forge_vm.py constructor field map if needed
[ ] 10. Run make isa-proof-freshness-check
```
