# Thiele Machine Specification

## Postulate
The model assumes a fundamental information currency: every act of discovery has a cost measured in **μ-bits**.

## Key Definitions
- **Thiele machine** – an abstract CPU state that extends a Turing machine with a running information cost and a paradox flag【F:coq/thielemachine/coqproofs/ThieleMachine.v†L55-L66】.
- **μ-bit cost** – the field `mu_cost` counts paid discovery; `total_mu_cost` lifts it to an option type where paradoxes yield infinity【F:coq/thielemachine/coqproofs/ThieleMachine.v†L131-L136】.
- **Sight debt** – the difference between the μ-cost of a blind model and that of a partition-aware model. Paying this debt creates the "map" enabling efficient computation.

## Logic Oracle
`logic_oracle : list nat -> bool` is an uninterpreted oracle returning `false` when a set of axioms is inconsistent. We assume it is sound: any paradox triggers the flag and forces infinite μ-cost.

## Proven Results
- **CPU simulates Turing step** – one `RunTMStep` instruction reproduces the behaviour of a TM transition【F:coq/thielemachine/coqproofs/ThieleMachine.v†L176-L188】.
- **Paradox implies infinite cost** – once `paradox_detected` is set, `total_mu_cost` is undefined【F:coq/thielemachine/coqproofs/ThieleMachine.v†L190-L199】.
- **Subsumption** – one `thiele_step` mirrors a single `tm_step`【F:coq/thielemachine/coqproofs/Subsumption.v†L1-L24】.

## Conjectures
- Thiele machines strictly contain Turing machines.
- The Law of No Unpaid Sight Debt (NUSD) governs all computation.

These open problems guide future formalisation and experimentation.

## Experiments
Reproducible experiments, including the Engine of Discovery and structured Tseitin instances, are detailed in `docs/EXPERIMENTS.md`.
