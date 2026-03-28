# The Classical Shadow — What It Is and Why It Matters

**Date**: 2026-03-27
**Formal reference**: `coq/kernel/ShadowProjection.v` — fully proven, zero Admitted

---

## The Full Thiele VM State

The Thiele Machine state is the record:

```
VMState = {
  vm_graph     : PartitionGraph,   (* morphism graph: modules + morphisms *)
  vm_csrs      : CSRState,         (* includes csr_cert_addr *)
  vm_regs      : list nat,         (* general-purpose registers *)
  vm_mem       : list nat,         (* data memory *)
  vm_pc        : nat,              (* program counter *)
  vm_mu        : nat,              (* monotone cost ledger *)
  vm_mu_tensor : list nat,         (* tensor product cost components *)
  vm_err       : bool,             (* error flag *)
  vm_logic_acc : nat,              (* logic accumulator *)
  vm_mstatus   : nat,              (* machine status register *)
  vm_witness   : WitnessCounts,    (* CHSH witness buckets *)
  vm_certified : bool              (* certification flag *)
}
```

---

## The Classical Shadow

The **classical shadow** is the lossy projection that a classical machine can observe:

```
shadow_proj : VMState → ClassicalState

ClassicalState = {
  cs_regs      : list nat,
  cs_mem       : list nat,
  cs_pc        : nat,
  cs_mu        : nat,
  cs_err       : bool,
  cs_certified : bool
}
```

**What shadow_proj retains**: registers, memory, program counter, μ, error flag, certified flag.

**What shadow_proj forgets**:
- `vm_graph` — the entire morphism graph (modules, morphisms, composition chains)
- `vm_csrs.csr_cert_addr` — the supra-cert address (whether a structural claim has been formally asserted)
- `vm_witness` — CHSH experiment witness buckets
- `vm_mstatus` — machine status
- `vm_mu_tensor` — tensor cost components

---

## Two States With the Same Shadow

The separation witness pair (from `ShadowProjection.v`):

| Field | separation_A | separation_B |
|---|---|---|
| vm_regs | [] | [] |
| vm_mem | [] | [] |
| vm_pc | 0 | 0 |
| vm_mu | 0 | 0 |
| vm_err | false | false |
| vm_certified | false | false |
| **vm_graph.pg_morphisms** | **[(0, identity_morph)]** | **[]** |

`shadow_proj separation_A = shadow_proj separation_B` — proven by `shadow_proj_forgets_graph`.

Any classical machine that observes only (regs, mem, pc, μ, err, certified) sees these states as **identical**. No function of the classical shadow can distinguish them:

```coq
Theorem shadow_does_not_capture_morphisms :
  forall {A : Type} (f : ClassicalState -> A),
    f (shadow_proj separation_A) = f (shadow_proj separation_B).
```

---

## The Probe That Separates Them

The Thiele instruction `MORPH_DELETE 0 0` (delete morphism id=0, cost=0) is a legitimate ISA instruction. Applied to these two states:

| State | Probe result |
|---|---|
| separation_A | `vm_err = false` — morphism 0 exists, deletion succeeds |
| separation_B | `vm_err = true` — morphism 0 does not exist, deletion fails |

This is not a trick — `vm_err` is part of the classical shadow. After the probe, the states differ in `vm_err`, which is observable to any classical machine. The point is that the probe is **required** to surface the difference: before the probe, no classical observation works.

---

## The Shadow Separation Theorem

```coq
Theorem shadow_separation_theorem :
  exists (s1 s2 : VMState) (probe : vm_instruction),
    shadow_equal s1 s2 /\
    s1.(vm_graph).(pg_morphisms) <> s2.(vm_graph).(pg_morphisms) /\
    (vm_apply s1 probe).(vm_err) = false /\
    (vm_apply s2 probe).(vm_err) = true.
```

**What this proves**:
1. There exist classically indistinguishable states (same shadow)
2. That differ in retained graph structure (different morphisms)
3. Such that one legitimate ISA instruction separates them by observable output

**What this does NOT prove**:
- That the morphism graph represents any physical structure
- That this separation is useful for any specific application
- That the probe is hard to find (it is explicitly exhibited)
- That all Thiele programs are "better" than classical programs

---

## Why the Shadow Projection Matters

The shadow projection formalizes the question: **what can a classical machine know from observing Thiele output?**

The answer: a classical machine cannot reconstruct `vm_graph`, `csr_cert_addr`, or `vm_witness` from the shadow. These fields carry structural information that the Thiele Machine retains and that classical machines cannot represent.

The practical consequence:
- A Thiele certification receipt (`csr_cert_addr ≠ 0`) is **not forgeable by classical computation** — because a classical machine cannot manipulate `csr_cert_addr` (it is outside the shadow)
- A morphism chain in `vm_graph` proves that specific structural relationships were built — a classical machine holding the same registers and μ may have taken any path

The shadow projection is strictly lossy — formally proven as `shadow_strictly_lossy` in ShadowProjection.v.
