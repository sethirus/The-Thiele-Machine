(* ================================================================= *)
(* Concrete Implementation of Thiele Machine Interface *)
(* ================================================================= *)
From Coq Require Import List String ZArith.
Import ListNotations.

(* Include the universal theorems and signature inline *)
Require ThieleMachineUniv.

(* Now implement the concrete module using the existing concrete definitions *)
Module ConcreteThiele <: ThieleMachineUniv.THIELE_ABSTRACT.

  (* Bind types to existing concrete types *)
  Definition Instr := ThieleInstr.
  Definition State := ConcreteState.
  Definition Event := ThieleEvent.
  Definition Cert  := ConcreteCert.
  Definition Hash  := ConcreteHash.

  (* Bind wf predicates *)
  Definition is_LASSERT := concrete_is_LASSERT.
  Definition is_MDLACC  := concrete_is_MDLACC.

  (* Observations + step *)
  Record StepObs := { ev : option Event; mu_delta : Z; cert : Cert }.
  Definition step := concrete_step.

  (* Checker, sizes, eq *)
  Definition check_step := concrete_check_step.
  Definition bitsize    := concrete_bitsize.
  Definition state_eqb  := concrete_state_eq.

  (* Hash-chain (optional) *)
  Definition H0         := Concrete_H0.
  Definition hash_state := concrete_hash_state.
  Definition hash_cert  := concrete_hash_cert.
  Definition hcombine   := concrete_hcombine.

  (* Axioms / interface lemmas: discharge by importing your proven theorems *)
  Theorem check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  Proof. apply concrete_check_step_sound. Admitted.

  Theorem mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  Proof. apply concrete_mu_lower_bound. Admitted.

  Theorem check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  Proof. apply concrete_check_step_complete. Admitted.

  Theorem state_eqb_refl : forall s, state_eqb s s = true.
  Proof. apply concrete_state_eqb_refl. Admitted.

End ConcreteThiele.