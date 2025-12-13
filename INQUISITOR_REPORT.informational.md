# INQUISITOR REPORT
Generated: 2025-12-13 01:17:08Z (UTC)
Scanned: 128 Coq files under `coq/`
## Summary
- HIGH: 0
- MEDIUM: 0
- LOW: 63

## Rules
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter`
- `HYPOTHESIS_ASSUME`: `Hypothesis` (escalates to HIGH for suspicious names)
- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (informational)
- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)
- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`
- `EMPTY_LIST`: `Definition ... := [].`
- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`
- `TRUE_CONST`: `Definition ... := True.` or `:= true.`
- `PROP_TAUTOLOGY`: `Theorem ... : True.`
- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`
- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof

## Findings
### LOW

#### `coq/kernel/MuLedgerConservation.v`
- L303: **SECTION_BINDER** — Found Variable mu_blind_component.
  - `Variable mu_blind_component mu_sighted_component : vm_instruction -> nat.`
- L304: **SECTION_BINDER** — Found Variable mu_component_split.
  - `Variable mu_component_split : forall instr,`
- L377: **SECTION_BINDER** — Found Variable Hash.
  - `Variable Hash : Type.`
- L378: **SECTION_BINDER** — Found Variable combine.
  - `Variable combine : Hash -> Hash -> Hash.`
- L379: **SECTION_BINDER** — Found Variable default.
  - `Variable default : Hash.`

#### `coq/kernel/VMStep.v`
- L14: **MODULE_SIGNATURE_DECL** — Found Parameter check_lrat inside Module Type.
  - `Parameter check_lrat : string -> string -> bool.`
- L15: **MODULE_SIGNATURE_DECL** — Found Parameter check_model inside Module Type.
  - `Parameter check_model : string -> string -> bool.`

#### `coq/modular_proofs/EncodingBounds.v`
- L21: **SECTION_BINDER** — Found Context BASE.
  - `Context (BASE SHIFT_LEN : nat).`
- L26: **SECTION_BINDER** — Found Context BASE_ge_2.
  - `Context (BASE_ge_2 : 2 <= BASE).`
- L27: **SECTION_BINDER** — Found Context SHIFT_LEN_ge_1.
  - `Context (SHIFT_LEN_ge_1 : 1 <= SHIFT_LEN).`
- L143: **SECTION_BINDER** — Found Context encode_list.
  - `Context (encode_list : list nat -> nat).`
- L144: **SECTION_BINDER** — Found Context digits_ok.
  - `Context (digits_ok : list nat -> Prop).`
- L145: **SECTION_BINDER** — Found Context encode_list_upper.
  - `Context (encode_list_upper : forall xs, digits_ok xs -> encode_list xs < Nat.pow BASE (length xs)).`

#### `coq/modular_proofs/Simulation.v`
- L16: **SECTION_BINDER** — Found Context.
  - `Context {tm : TMTransition}.`
- L17: **SECTION_BINDER** — Found Context sem.
  - `Context (sem : ModularThieleSemantics tm).`

#### `coq/modular_proofs/Thiele_Basics.v`
- L41: **SECTION_BINDER** — Found Context.
  - `Context {tm : TMTransition}.`
- L42: **SECTION_BINDER** — Found Context sem.
  - `Context (sem : ModularThieleSemantics tm).`

#### `coq/physics/DiscreteModel.v`
- L155: **SECTION_BINDER** — Found Variable Encoded.
  - `Variable Encoded : Type.`
- L156: **SECTION_BINDER** — Found Variable encode.
  - `Variable encode : Lattice -> Encoded.`
- L157: **SECTION_BINDER** — Found Variable decode.
  - `Variable decode : Encoded -> Lattice.`
- L158: **SECTION_BINDER** — Found Variable impl_step.
  - `Variable impl_step : Encoded -> Encoded.`
- L160: **SECTION_BINDER** — Found Variable decode_encode_id.
  - `Variable decode_encode_id : forall L, decode (encode L) = L.`
- L161: **SECTION_BINDER** — Found Variable impl_refines_physics.
  - `Variable impl_refines_physics :`

#### `coq/physics/DissipativeModel.v`
- L50: **SECTION_BINDER** — Found Variable Encoded.
  - `Variable Encoded : Type.`
- L51: **SECTION_BINDER** — Found Variable encode.
  - `Variable encode : Lattice -> Encoded.`
- L52: **SECTION_BINDER** — Found Variable decode.
  - `Variable decode : Encoded -> Lattice.`
- L53: **SECTION_BINDER** — Found Variable impl_step.
  - `Variable impl_step : Encoded -> Encoded.`
- L55: **SECTION_BINDER** — Found Variable decode_encode_id.
  - `Variable decode_encode_id : forall l, decode (encode l) = l.`
- L56: **SECTION_BINDER** — Found Variable impl_refines_dissipative.
  - `Variable impl_refines_dissipative :`

#### `coq/physics/WaveModel.v`
- L250: **SECTION_BINDER** — Found Variable Encoded.
  - `Variable Encoded : Type.`
- L251: **SECTION_BINDER** — Found Variable encode.
  - `Variable encode : WaveState -> Encoded.`
- L252: **SECTION_BINDER** — Found Variable decode.
  - `Variable decode : Encoded -> WaveState.`
- L253: **SECTION_BINDER** — Found Variable impl_step.
  - `Variable impl_step : Encoded -> Encoded.`
- L255: **SECTION_BINDER** — Found Variable decode_encode_id.
  - `Variable decode_encode_id : forall s, decode (encode s) = s.`
- L256: **SECTION_BINDER** — Found Variable impl_refines_wave.
  - `Variable impl_refines_wave : forall s, decode (impl_step (encode s)) = wave_step s.`

#### `coq/sandboxes/EncodingMini.v`
- L23: **SECTION_BINDER** — Found Context.
  - `Context {BASE SHIFT_LEN : nat}.`
- L28: **SECTION_BINDER** — Found Context BASE_ge_2.
  - `Context (BASE_ge_2 : 2 <= BASE).`
- L29: **SECTION_BINDER** — Found Context SHIFT_LEN_ge_1.
  - `Context (SHIFT_LEN_ge_1 : 1 <= SHIFT_LEN).`

#### `coq/shor_primitives/Modular.v`
- L17: **SECTION_BINDER** — Found Variable n.
  - `Variable n : nat.`

#### `coq/shor_primitives/PeriodFinding.v`
- L125: **SECTION_BINDER** — Found Variable N.
  - `Variable N a : nat.`

#### `coq/thiele_manifold/PhysicalConstants.v`
- L18: **SECTION_BINDER** — Found Variable N.
  - `Variable N : nat.`

#### `coq/thiele_manifold/PhysicsIsomorphism.v`
- L68: **SECTION_BINDER** — Found Context.
  - `Context {DP : DiscretePhysics} (E : ThieleEmbedding DP).`

#### `coq/thielemachine/coqproofs/BellInequality.v`
- L1297: **SECTION_BINDER** — Found Context.
  - `Context {Instr State Observation : Type}.`
- L1299: **SECTION_BINDER** — Found Variable concrete_step.
  - `Variable concrete_step : Instr -> State -> BridgeStepResult State Observation.`

#### `coq/thielemachine/coqproofs/HardwareVMHarness.v`
- L31: **SECTION_BINDER** — Found Variable vm_trace.
  - `Variable vm_trace   : list vm_instruction.`
- L32: **SECTION_BINDER** — Found Variable decode_vm.
  - `Variable decode_vm  : HardwareBridge.RTLState -> VMState.`
- L33: **SECTION_BINDER** — Found Variable rtl_refines_vm.
  - `Variable rtl_refines_vm : forall fuel s,`

#### `coq/thielemachine/coqproofs/HyperThiele_Halting.v`
- L24: **SECTION_BINDER** — Found Context H.
  - `Context (H : Oracle) (Halts : nat -> Prop).`
- L26: **SECTION_BINDER** — Found Variable H_correct.
  - `Variable H_correct : forall e, H e = true <-> Halts e.`

#### `coq/thielemachine/coqproofs/ListHelpers.v`
- L12: **SECTION_BINDER** — Found Context.
  - `Context {A : Type}.`

#### `coq/thielemachine/coqproofs/OracleImpossibility.v`
- L125: **SECTION_BINDER** — Found Variable oracle.
  - `Variable oracle : Prog -> bool.`

#### `coq/thielemachine/coqproofs/PhysicsEmbedding.v`
- L16: **SECTION_BINDER** — Found Context encode_lattice.
  - `Context (encode_lattice : Lattice -> VMState)`
- L20: **SECTION_BINDER** — Found Variable decode_encode_id.
  - `Variable decode_encode_id : forall L, decode_lattice (encode_lattice L) = L.`
- L21: **SECTION_BINDER** — Found Variable physics_vm_step_simulation.
  - `Variable physics_vm_step_simulation :`
- L24: **SECTION_BINDER** — Found Variable physics_trace_irreversible_free.
  - `Variable physics_trace_irreversible_free :`

#### `coq/thielemachine/coqproofs/RepresentationTheorem.v`
- L36: **MODULE_SIGNATURE_DECL** — Found Parameter partition_trace_equiv inside Module Type.
  - `Parameter partition_trace_equiv : S1.PartitionTrace -> S2.PartitionTrace -> Prop.`
- L37: **MODULE_SIGNATURE_DECL** — Found Parameter mu_trace_equiv inside Module Type.
  - `Parameter mu_trace_equiv : S1.MuTrace -> S2.MuTrace -> Prop.`
- L82: **MODULE_SIGNATURE_DECL** — Found Parameter partition_equiv inside Module Type.
  - `Parameter partition_equiv : S1.Partition -> S2.Partition -> Prop.`
- L83: **MODULE_SIGNATURE_DECL** — Found Parameter trace_mu_equiv inside Module Type.
  - `Parameter trace_mu_equiv : forall (t1 : S1.Trace) (t2 : S2.Trace), Prop.`

#### `coq/thielemachine/coqproofs/WaveEmbedding.v`
- L17: **SECTION_BINDER** — Found Context encode_wave.
  - `Context (encode_wave : WaveState -> VMState)`
- L21: **SECTION_BINDER** — Found Variable decode_encode_id.
  - `Variable decode_encode_id : forall S, decode_wave (encode_wave S) = S.`
- L22: **SECTION_BINDER** — Found Variable wave_vm_step_simulation.
  - `Variable wave_vm_step_simulation :`
- L25: **SECTION_BINDER** — Found Variable wave_trace_irreversible_free.
  - `Variable wave_trace_irreversible_free :`

