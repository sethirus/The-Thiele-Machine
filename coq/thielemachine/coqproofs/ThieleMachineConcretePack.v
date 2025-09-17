(* ================================================================= *)
(* Concrete Implementation of Thiele Machine Interface *)
(* ================================================================= *)
From Coq Require Import List String ZArith.
Import ListNotations.

(* Include the universal theorems and signature inline *)
Require Import ThieleMachineConcrete.
Require Import ThieleMachineUniv.

(* Concrete module implementing the Thiele Machine interface *)
Module ConcreteThiele <: THIELE_ABSTRACT.

  Include ThieleMachineConcrete.

  (* Define the required types *)
  Definition Instr := ThieleInstr.
  Definition State := ConcreteState.
  Definition Event := ThieleEvent.
  Definition Cert := ConcreteCert.

  (* Define the required functions *)
  Definition is_LASSERT := concrete_is_LASSERT.
  Definition is_MDLACC := concrete_is_MDLACC.

  (* Step semantics *)
  Definition step := concrete_step.

  (* Checker and utilities *)
  Definition check_step := concrete_check_step.
  Definition bitsize := concrete_bitsize.
  Definition state_eqb := concrete_state_eq.

  (* Hash functions *)
  Definition hash_state := concrete_hash_state.
  Definition hash_cert := concrete_hash_cert.
  Definition hcombine := concrete_hcombine.

  (* Well-formedness *)
  Definition well_formed_prog (P : list Instr) : bool :=
    forallb (fun i => orb (is_LASSERT i) (is_MDLACC i)) P.

  (* Receipts and replay *)
  Definition Receipt := (State * State * option Event * Cert)%type.

  Fixpoint replay_ok (P:list Instr) (s0:State) (rs:list Receipt) : bool :=
    match rs with
    | [] => true
    | (spre, spost, oev, c)::tl =>
        if negb (state_eqb spre s0) then false
        else if check_step P spre spost oev c
             then replay_ok P spost tl
             else false
    end.

  Fixpoint receipts_of (P:list Instr) (s0:State)
         (tr:list (State*StepObs)) : list Receipt :=
    match tr with
    | [] => []
    | (s',obs)::tl =>
        (s0,s',obs.(ev),obs.(cert)) :: receipts_of P s' tl
    end.

  Definition sum_mu (tr: list (State*StepObs)) : Z :=
    fold_left (fun acc '(_,obs) => Z.add acc obs.(mu_delta)) tr 0%Z.

  Definition sum_bits (rs: list Receipt) : Z :=
    fold_left (fun acc '(_,_,_,c) => Z.add acc (bitsize c)) rs 0%Z.

  (* Include the proven theorems *)
  Theorem check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  Proof. apply concrete_check_step_sound. Qed.

  Theorem mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  Proof. apply concrete_mu_lower_bound. Qed.

  Theorem check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  Proof. apply concrete_check_step_complete. Qed.

  Theorem state_eqb_refl : forall s, state_eqb s s = true.
  Proof. apply concrete_state_eqb_refl. Qed.

End ConcreteThiele.