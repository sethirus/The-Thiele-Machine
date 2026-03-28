# The Thiele Machine — One-Page Kernel Statement

## What the machine is

The Thiele Machine is a formal computational model with a richer state space than classical machines.
Its state is the tuple: `(graph, csrs, regs, mem, pc, mu, mu_tensor, err, witness, mstatus, logic_acc, certified)`.

The key addition over a classical machine is **vm_graph** — a morphism graph recording partition modules and certified structural relationships between them. This structure is invisible to classical observation but semantically actionable via morphism-aware instructions.

## What μ is

μ (`vm_mu`) is the machine's **monotone cost ledger**. It starts at 0 and never decreases.

- Every instruction charges `instruction_cost(i)` to μ at each step: `(vm_apply s i).mu = s.mu + instruction_cost i`
- This is proven exactly (no approximation) — `vm_apply_mu`, MuLedgerConservation.v
- μ is the **unique** measure satisfying this conservation law: `mu_is_initial_monotone`, MuInitiality.v

## What certification means

There are two certification channels:

1. **`csr_cert_addr ≠ 0`** ("supra-cert"): set by REVEAL, EMIT, LJOIN, LASSERT, MORPH_ASSERT. Represents that a structural claim has been formally asserted and recorded. This is `has_supra_cert` in the Coq semantics.

2. **`vm_certified = true`**: set by CERTIFY opcode. A direct certification flag.

Both channels are **non-free**: setting either one requires at least 1 unit of μ.

## What is formally proven

| Theorem | File | Claim |
|---|---|---|
| `no_free_certification` | AbstractNoFI.v §8 | If cert_addr 0→nonzero in one step, cost ≥ 1 |
| `no_free_certification_mu` | AbstractNoFI.v §8 | If cert_addr 0→nonzero in one step, μ grew ≥ 1 |
| `no_free_certification_trace_mu` | AbstractNoFI.v §9 | Over any trace, cert evidence appearing implies μ grew ≥ 1 |
| `certification_requires_positive_mu` | AbstractNoFI.v §11 | Either channel activating implies μ grew ≥ 1 |
| `no_free_certified_insight` | InsightTaxonomy.v | The umbrella NoFI theorem for certified structural insight |
| `shadow_separation_theorem` | ShadowProjection.v | ∃ states with same classical shadow that a valid probe separates |
| `shadow_strictly_lossy` | ShadowProjection.v | shadow_proj forgets semantically actionable structure |
| `categorical_separation` | PartitionSeparation.v | ∃ classically-equivalent but Thiele-distinct states |
| `mu_is_initial_monotone` | MuInitiality.v | μ is the unique canonical cost measure |
| `vm_apply_mu` | MuLedgerConservation.v | Exact conservation: μ = sum of instruction costs |

**Status**: All theorems above are proven with zero Admitted. INQUISITOR OK.
