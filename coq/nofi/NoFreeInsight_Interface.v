From Coq Require Import List Arith.PeanoNat.

(** * No-Free-Insight interface (axiom-free)

    This file intentionally contains **no `Axiom`** and **no `Admitted`**.

    The idea is to separate:
    - *assumptions/contracts* (as a Module Type interface)
    - from *the kernel instantiation* (proved separately).

    Any system implementing this interface can reuse the theorem proven in
    `NoFreeInsight_Theorem.v`.
*)

Module Type NO_FREE_INSIGHT_SYSTEM.
  Parameter S : Type.
  Parameter Trace : Type.
  Parameter Obs : Type.
  Parameter Strength : Type.

  Parameter run : Trace -> S -> option S.

  (** Successful execution predicate (kernel instance: vm_err = false). *)
  Parameter ok : S -> Prop.

  Parameter mu : S -> nat.
  Parameter observe : S -> Obs.

  Parameter certifies : S -> Strength -> Prop.
  Parameter strictly_stronger : Strength -> Strength -> Prop.

  (** Semantic structure addition: may depend on the initial state.
      (E.g. a cert CSR transition from 0 -> nonzero during execution.) *)
  Parameter structure_event : Trace -> S -> Prop.
  Parameter clean_start : S -> Prop.

  (** Certified notion (general, CHSH-free):
      execution succeeded and a certification witness holds. *)
  Parameter Certified : Trace -> S -> Strength -> Prop.

  (** Certified must coincide with the kernel-derived definition. *)
  Parameter Certified_spec :
    forall tr s0 strength,
      Certified tr s0 strength <->
      exists s1, run tr s0 = Some s1 /\ ok s1 /\ certifies s1 strength.

  (** ** Laws (fields)

      These are not axioms: they are obligations for any instantiation.
  *)

  Parameter mu_monotone :
    forall tr s0 s1,
      run tr s0 = Some s1 ->
      mu s0 <= mu s1.

  (** Core “no free insight” contract (strengthening form):
      any certified strict strengthening requires a structural event. *)
  Parameter no_free_insight_contract :
    forall tr s0 s1 strength weak,
      clean_start s0 ->
      run tr s0 = Some s1 ->
      strictly_stronger strength weak ->
      certifies s1 strength ->
      structure_event tr s0.
End NO_FREE_INSIGHT_SYSTEM.
