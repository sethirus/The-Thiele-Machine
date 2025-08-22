# Universe.v: Categorical Physics and Logic

This directory contains `Universe.v`, a Coq formalization of the functorial relationship between a physical universe and its logical abstraction, following the Thiele Machine paradigm.

## Contents

- **Physical Category (C_phys):**
  - Objects: States of a universe (lists of natural numbers, representing momenta)
  - Morphisms: Paths of local interactions (collisions) that conserve momentum
- **Logical Category (C_logic):**
  - Objects: Total momentum values (natural numbers)
  - Morphisms: Equalities between total momenta
- **Functor F:**
  - Maps each physical state to its total momentum
  - Maps each physical path to a proof that total momentum is conserved along that path

## Main Theorem

- **Thiele_Functor_Is_Sound:**
  - Proves that the functor F is well-defined: every physical process (path) conserves total momentum, as seen in the logical world

## Usage

- See `Universe.v` for the formalization and proof
- Compile with Coq 8.20+:

      coqc Universe.v

## License

See repository LICENSE.
