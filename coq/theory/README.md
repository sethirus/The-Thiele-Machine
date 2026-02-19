# Core Theory

**Mission:** Core theoretical framework proofs including separation, universality, no-free-lunch, and genesis theorems.

## Structure

- `ArchTheorem.v` - Arch Theorem - Defines: OptimalStrategy, PerformanceMetric, ProblemClass; Key results: optimal_quartet_complete, optimal_quartet_distinct, optimal_quartet_high_accuracy (+8 more)
- `Core.v` - Core - Defines: Cat, Prog, EqProg; Key results: interp_respects, cut_is_composition
- `CostIsComplexity.v` - Cost Is Complexity - Key results: run_compiler, produces_shape, produces_length (+3 more)
- `EvolutionaryForge.v` - Evolutionary Forge - Defines: Primitive, Graph; Key results: crossover_length, performance_deterministic, optimal_quartet_viable (+11 more)
- `Genesis.v` - Genesis - Defines: Proc, Thiele, ThieleStep; Key results: proc_realises_thiele, to_from_id, from_to_id
- `GeometricSignature.v` - Geometric Signature - Defines: GeometricSignatureTy, ProblemStructure; Key results: vi_non_negative, vi_symmetric, vi_identity (+6 more)
- `LogicToPhysics.v` - Logic To Physics - Key results: cut_is_relational_composition
- `NoFreeLunch.v` - No Free Lunch - Defines: PhysicalState; Key results: ghost_impossible, NoFreeLunch
- `PhysRel.v` - Phys Rel - Key results: iff_to_eq, rel_comp_id_l, rel_comp_id_r (+1 more)
- `Representations.v` - Representations - Key results: grover_bound_from_mu, born_rule_from_mu, landauer_from_mu (+4 more)
- `Separation.v` - Separation - Key results: blind_steps_succ, pow2_ge_linear, sighted_is_quadratic (+3 more)
- `Universality.v` - Universality - Defines: Cat, Prog, ProgEq (+3 more); Key results: prog_mu_respects_eq, prog_id_l, prog_id_r (+9 more)
- `WitnessIsGenesis.v` - Witness Is Genesis - Defines: CreatorState, ChildState, WitnessState; Key results: auditor_func_accepts, witness_auditor_accepts, Ouroboros_Witness_Is_A_Coherent_Process

## Verification Status

| File | Admits | Status |
|:---|:---:|:---:|
| `ArchTheorem.v` | 0 | ✅ |
| `Core.v` | 0 | ✅ |
| `CostIsComplexity.v` | 0 | ✅ |
| `EvolutionaryForge.v` | 0 | ✅ |
| `Genesis.v` | 0 | ✅ |
| `GeometricSignature.v` | 0 | ✅ |
| `LogicToPhysics.v` | 0 | ✅ |
| `NoFreeLunch.v` | 0 | ✅ |
| `PhysRel.v` | 0 | ✅ |
| `Representations.v` | 0 | ✅ |
| `Separation.v` | 0 | ✅ |
| `Universality.v` | 0 | ✅ |
| `WitnessIsGenesis.v` | 0 | ✅ |

**Result:** All 13 files verified with 0 admits.
