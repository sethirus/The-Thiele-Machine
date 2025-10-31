(* ================================================================= *)
(* Abstract Interface for Thiele Machine *)
(* ================================================================= *)
From Coq Require Import List String ZArith.
From ThieleMachine Require Import ThieleMachine.
Import ListNotations.

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

  Definition sum_mu (tr: list (State*StepObs)) : Z :=
    fold_left (fun acc '(_,obs) => Z.add acc obs.(mu_delta)) tr 0%Z.

  Definition sum_bits (rs: list Receipt) : Z :=
    fold_left (fun acc '(_,_,_,c) => Z.add acc (bitsize c)) rs 0%Z.

  (* Axioms / interface lemmas *)
  Parameter check_step_sound :
    forall P s s' obs, step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  (* Justified: The check_step function is sound with respect to the step semantics, ensuring valid transitions are accepted. *)

  Parameter mu_lower_bound :
    forall P s s' obs, step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  (* Justified: The mu cost is at least the certificate size, providing a lower bound for computational resources. *)

  Parameter check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  (* Justified: The check_step function is complete, accepting all valid transitions with their observations and certificates. *)

  Parameter state_eqb_refl : forall s, state_eqb s s = true.
  (* Justified: State equality is reflexive, ensuring that any state equals itself. *)

End THIELE_ABSTRACT.

Module MinimalThieleMachine <: THIELE_ABSTRACT.
  Module TM := ThieleMachine.

  Definition Instr : Type := TM.Instr.
  Definition State : Type := TM.State.
  Definition Event : Type := TM.Event.
  Definition Cert : Type := TM.Cert.
  Definition Hash : Type := TM.Hash.

  Definition is_LASSERT (i : Instr) : bool := TM.is_LASSERT i.
  Definition is_MDLACC (i : Instr) : bool := TM.is_MDLACC i.

  Definition StepObs : Type := TM.StepObs.

  Definition mk_prog (code : list Instr) : TM.Prog := {| TM.code := code |}.

  Definition step (P : list Instr) (s s' : State) (obs : StepObs) : Prop :=
    TM.step (mk_prog P) s s' obs.

  Definition check_step
    (P : list Instr) (spre spost : State) (oev : option Event) (c : Cert) : bool :=
    TM.check_step (mk_prog P) spre spost oev c.

  Definition bitsize (c : Cert) : Z := TM.bitsize c.

  Definition state_eqb (s1 s2 : State) : bool := TM.state_eq s1 s2.

  Definition H0 : Hash := TM.H0.
  Definition hash_state (s : State) : Hash := TM.hash_state s.
  Definition hash_cert (c : Cert) : Hash := TM.hash_cert c.
  Definition hcombine (h1 h2 : Hash) : Hash := TM.hcombine h1 h2.

  Lemma check_step_sound :
    forall P s s' obs,
      step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  Proof.
    intros P s s' obs Hstep.
    unfold step, check_step in *.
    apply TM.check_step_sound.
    exact Hstep.
  Qed.

  Lemma mu_lower_bound :
    forall P s s' obs,
      step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  Proof.
    intros P s s' obs Hstep.
    unfold step, bitsize in *.
    apply TM.mu_lower_bound.
    exact Hstep.
  Qed.

  Lemma check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  Proof.
    intros P s s' oev c Hchk.
    unfold step, check_step in *.
    apply TM.check_step_complete in Hchk.
    destruct Hchk as [obs [Hstep [Hev Hcert]]].
    exists obs. repeat split; assumption.
  Qed.

  Lemma state_eqb_refl : forall s, state_eqb s s = true.
  Proof.
    intro s.
    unfold state_eqb.
    apply TM.state_eqb_refl.
  Qed.
End MinimalThieleMachine.
