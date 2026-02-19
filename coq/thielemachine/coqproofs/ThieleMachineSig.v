(* ================================================================= *)
(* Abstract Interface for Thiele Machine *)
(* ================================================================= *)
From Coq Require Import List String ZArith.
From ThieleMachine Require Import ThieleMachine.
Import ListNotations.

(* This file used to expose an abstract signature via a Module Type with many
   Parameters. To keep the repository assumption-free, we only retain the
   concrete, proven implementation used throughout the development. *)

Module MinimalThieleMachine.
  Module TM := ThieleMachine.

  Definition Instr : Type := TM.Instr.
  Definition State : Type := TM.State.
  Definition Event : Type := TM.Event.
  Definition Cert : Type := TM.Cert.
  Definition Hash : Type := TM.Hash.

  Definition is_LASSERT (i : Instr) : bool := TM.is_LASSERT i.
  Definition is_MDLACC (i : Instr) : bool := TM.is_MDLACC i.

  Record StepObs := {
    ev       : option Event;
    mu_delta : Z;
    cert     : Cert;
  }.

  Definition mk_prog (code : list Instr) : TM.Prog := {| TM.code := code |}.

  Definition to_TM_StepObs (obs : StepObs) : TM.StepObs :=
    {| TM.ev := obs.(ev); TM.mu_delta := obs.(mu_delta); TM.cert := obs.(cert) |}.

  Definition from_TM_StepObs (tm_obs : TM.StepObs) : StepObs :=
    {| ev := tm_obs.(TM.ev); mu_delta := tm_obs.(TM.mu_delta); cert := tm_obs.(TM.cert) |}.

  Definition step (P : list Instr) (s s' : State) (obs : StepObs) : Prop :=
    TM.step (mk_prog P) s s' (to_TM_StepObs obs).

  Definition check_step
    (P : list Instr) (spre spost : State) (oev : option Event) (c : Cert) : bool :=
    TM.check_step (mk_prog P) spre spost oev c.

  Definition bitsize (c : Cert) : Z := TM.bitsize c.

  Definition state_eqb (s1 s2 : State) : bool := TM.state_eq s1 s2.

  Definition H0 : Hash := TM.H0.
  Definition hash_state (s : State) : Hash := TM.hash_state s.
  Definition hash_cert (c : Cert) : Hash := TM.hash_cert c.
  Definition hcombine (h1 h2 : Hash) : Hash := TM.hcombine h1 h2.

  (** [check_step_sound]: formal specification. *)
  Lemma check_step_sound :
    forall P s s' obs,
      step P s s' obs ->
      check_step P s s' obs.(ev) obs.(cert) = true.
  Proof.
    intros P s s' obs Hstep.
    unfold step, check_step in *.
    destruct obs as [oev omu ocert]; simpl in *.
    unfold to_TM_StepObs in Hstep; simpl in Hstep.
    apply TM.check_step_sound in Hstep.
    simpl in Hstep.
    exact Hstep.
  Qed.

  (** [mu_lower_bound]: formal specification. *)
  Lemma mu_lower_bound :
    forall P s s' obs,
      step P s s' obs ->
      Z.le (bitsize obs.(cert)) obs.(mu_delta).
  Proof.
    intros P s s' obs Hstep.
    unfold step, bitsize in *.
    simpl in *.
    apply (TM.mu_lower_bound (mk_prog P) s s' (to_TM_StepObs obs)).
    exact Hstep.
  Qed.

  (** [check_step_complete]: formal specification. *)
  Lemma check_step_complete :
    forall P s s' oev c,
      check_step P s s' oev c = true ->
      exists obs, step P s s' obs /\ obs.(ev) = oev /\ obs.(cert) = c.
  Proof.
    intros P s s' oev c Hchk.
    unfold step, check_step in *.
    apply TM.check_step_complete in Hchk.
    destruct Hchk as [tm_obs [Hstep [Hev Hcert]]].
    exists (from_TM_StepObs tm_obs).
    unfold from_TM_StepObs; simpl.
    split.
    - unfold step, to_TM_StepObs; simpl.
      destruct tm_obs; simpl in *; subst.
      exact Hstep.
    - split; [exact Hev | exact Hcert].
  Qed.

  (** [state_eqb_refl]: formal specification. *)
  Lemma state_eqb_refl : forall s, state_eqb s s = true.
  Proof.
    intro s.
    unfold state_eqb.
    apply TM.state_eqb_refl.
  Qed.

  Definition well_formed_prog (P : list Instr) : bool :=
    forallb (fun i => orb (is_LASSERT i) (is_MDLACC i)) P.

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

End MinimalThieleMachine.
