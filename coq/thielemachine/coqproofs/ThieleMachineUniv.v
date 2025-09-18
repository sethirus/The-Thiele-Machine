(* ================================================================= *)
(* Universal Theorems Functor for Thiele Machine *)
(* ================================================================= *)
From Coq Require Import List ZArith Lia.
Import ListNotations.

(* ================================================================= *)
(* Abstract Interface for Thiele Machine *)
(* ================================================================= *)

Module Type THIELE_ABSTRACT.
  (* Types *)
  Parameter Instr State Event Cert Hash : Type.
  Parameter is_LASSERT is_MDLACC : Instr -> bool.

  (* Step semantics + observation *)
  Record StepObs := { ev : option Event; mu_delta : Z; cert : Cert }.
  Parameter step : list Instr -> State -> State -> StepObs -> Prop.

  (* Checker, sizes, eq *)
  Parameter check_step : list Instr -> State -> State -> option Event -> Cert -> bool.
  Parameter bitsize : Cert -> Z.
  Parameter state_eqb : State -> State -> bool.

  (* Hash chain (optional) *)
  Parameter H0 : Hash.
  Parameter hash_state : State -> Hash.
  Parameter hash_cert  : Cert  -> Hash.
  Parameter hcombine   : Hash -> Hash -> Hash.

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

  Fixpoint sum_mu (tr: list (State*StepObs)) : Z :=
    match tr with
    | [] => 0%Z
    | (_,obs)::tl => Z.add obs.(mu_delta) (sum_mu tl)
    end.

  Fixpoint sum_bits (rs: list Receipt) : Z :=
    match rs with
    | [] => 0%Z
    | (_,_,_,c)::tl => Z.add (bitsize c) (sum_bits tl)
    end.

  (* Axioms / interface lemmas *)
  Axiom check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.

  Axiom mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).

  Axiom check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.

  Axiom state_eqb_refl : forall s, state_eqb s s = true.

End THIELE_ABSTRACT.

(* ================================================================= *)
(* Universal Theorems Functor *)
(* ================================================================= *)

Module ThieleUniversal (M : THIELE_ABSTRACT).
  Import M.

  (* A standard big-step execution relation over step *)
  Inductive Exec : list Instr -> State -> list (State*StepObs) -> Prop :=
  | exec_nil : forall s, Exec [] s []
  | exec_cons : forall P s s' obs tl,
      step P s s' obs ->
      Exec P s' tl ->
      Exec P s ((s',obs)::tl).

  Theorem universal_replay :
    forall P s0 tr,
      well_formed_prog P = true ->
      Exec P s0 tr ->
      replay_ok P s0 (receipts_of P s0 tr) = true.
  Proof.
    intros P s0 tr Hwf Hexec.
    induction Hexec as [s | P s s' obs tl Hstep Hexec' IH].
    - (* Base case: empty trace *)
      simpl. reflexivity.
    - (* Inductive case *)
      simpl.
      rewrite state_eqb_refl.
      rewrite (check_step_sound P s s' obs Hstep).
      apply IH.
      assumption.
  Qed.

  Theorem universal_mu_accounting :
      forall P s0 tr,
        well_formed_prog P = true ->
        Exec P s0 tr ->
        Z.le (sum_bits (receipts_of P s0 tr)) (sum_mu tr).
    Proof.
      intros P s0 tr Hwf Hexec.
      induction Hexec as [s | P s s' obs tl Hstep Hexec' IH].
      - (* Base case: empty trace *)
        simpl. apply Z.le_refl.
      - (* Inductive case *)
        simpl.
        unfold sum_bits, sum_mu.
        simpl.
        (* receipts_of adds (s, s', obs.(ev), obs.(cert)) to the list *)
        (* sum_bits adds bitsize(obs.(cert)) to the sum of the tail *)
        (* sum_mu adds obs.(mu_delta) to the sum of the tail *)
        (* By mu_lower_bound, bitsize(obs.(cert)) <= obs.(mu_delta) *)
        apply Z.add_le_mono.
        + apply (mu_lower_bound P s s' obs Hstep).
        + apply IH. assumption.
    Qed.

End ThieleUniversal.

(* ================================================================= *)
(* Concrete Instantiation *)
(* ================================================================= *)

Require Import ThieleMachine.ThieleMachineConcrete.

Module ConcreteThiele : THIELE_ABSTRACT.

  Definition Instr := ThieleInstr.
  Definition State := ConcreteState.
  Definition Event := ThieleEvent.
  Definition Cert := ConcreteCert.
  Definition Hash := Hash.

  Definition is_LASSERT := concrete_is_LASSERT.
  Definition is_MDLACC := concrete_is_MDLACC.

  Definition step := concrete_step.

  Definition check_step := concrete_check_step.
  Definition bitsize := concrete_bitsize.
  Definition state_eqb := concrete_state_eq.

  Definition H0 := H0.
  Definition hash_state := concrete_hash_state.
  Definition hash_cert := concrete_hash_cert.
  Definition hcombine := concrete_hcombine.

  (* Axioms satisfied by concrete implementation *)
  Definition check_step_sound := concrete_check_step_sound.
  Definition mu_lower_bound := concrete_mu_lower_bound.
  Definition check_step_complete := concrete_check_step_complete.
  Definition state_eqb_refl := concrete_state_eqb_refl.

End ConcreteThiele.

(* Instantiate universal theorems with concrete implementation *)
Module ConcreteUniversal := ThieleUniversal ConcreteThiele.