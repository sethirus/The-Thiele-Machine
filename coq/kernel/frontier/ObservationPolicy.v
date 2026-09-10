(** Observation, event pricing, and retained history.
    All cost units here are abstract naturals, not measured heat. *)
From Coq Require Import List Bool Arith.PeanoNat Lia.
From Kernel Require Import VMState VMStep SimulationProof MuInitiality.
Import ListNotations.
Set Implicit Arguments.


  Definition query_fiber_constant {State View Answer : Type}
      (observe : State -> View) (query : State -> Answer) : Prop :=
    forall s t, observe s = observe t -> query s = query t.

  Theorem decoding_requires_fiber_constancy {State View Answer : Type}
      (observe : State -> View) (query : State -> Answer) :
    (exists decode : View -> Answer, forall s, decode (observe s) = query s) ->
    query_fiber_constant observe query.
  Proof.
    intros [decode H] s t E. rewrite <- (H s), <- (H t), E. reflexivity.
  Qed.

  (** A supplied section keeps this converse constructive. It is not
      inferred from surjectivity by an undisclosed choice principle. *)
  Theorem selected_representatives_give_decoder {State View Answer : Type}
      (observe : State -> View) (query : State -> Answer)
      (representative : View -> State)
      (section_law : forall v, observe (representative v) = v) :
    query_fiber_constant observe query <->
    exists decode : View -> Answer, forall s, decode (observe s) = query s.
  Proof.
    split.
    - intro H. exists (fun v => query (representative v)).
      intro s. apply H. apply section_law.
    - apply decoding_requires_fiber_constancy.
  Qed.

  Definition any_event {Instruction : Type} (events : list (Instruction -> bool)) (i : Instruction) : bool :=
    existsb (fun event => event i) events.
  Definition joint_floor {Instruction : Type} (events : list (Instruction -> bool)) (i : Instruction) : nat :=
    if any_event events i then 1 else 0.
  Definition respects_each_event {Instruction : Type} (events : list (Instruction -> bool)) (cost : Instruction -> nat) : Prop :=
    forall event, In event events -> forall i, event i = true -> 1 <= cost i.

  Theorem joint_floor_is_least {Instruction : Type} (events : list (Instruction -> bool)) :
    forall cost, respects_each_event events cost <-> forall i, joint_floor events i <= cost i.
  Proof.
    intro cost. split.
    - intros H i. unfold joint_floor, any_event.
      destruct (existsb (fun event => event i) events) eqn:E; [|lia].
      apply existsb_exists in E. destruct E as [event [Hin He]].
      exact (H event Hin i He).
    - intros H event Hin i He. specialize (H i).
      unfold joint_floor, any_event in H.
      assert (E : existsb (fun event => event i) events = true).
      { apply existsb_exists. exists event. auto. }
      rewrite E in H. exact H.
  Qed.

  Corollary least_joint_floor_respects_all_events {Instruction : Type} (events : list (Instruction -> bool)) :
    respects_each_event events (joint_floor events).
  Proof. apply joint_floor_is_least. intro i. reflexivity. Qed.

(** Independent Boolean coordinates can both change in a single unit-cost
    transition. Coordinate independence does not imply additive charges. *)
Definition first_rises (p : (bool * bool) * (bool * bool)) : bool :=
  negb (fst (fst p)) && fst (snd p).
Definition second_rises (p : (bool * bool) * (bool * bool)) : bool :=
  negb (snd (fst p)) && snd (snd p).

Theorem independent_coordinates_joint_change_costs_one :
  fst (false,false) = fst (false,true) /\
  snd (false,false) <> snd (false,true) /\
  snd (false,false) = snd (true,false) /\
  fst (false,false) <> fst (true,false) /\
  first_rises ((false,false),(true,true)) = true /\
  second_rises ((false,false),(true,true)) = true /\
  joint_floor [first_rises; second_rises] ((false,false),(true,true)) = 1 /\
  respects_each_event [first_rises; second_rises] (fun _ => 1).
Proof.
  repeat split; try reflexivity; try discriminate.
  intros event Hin i He. lia.
Qed.

  Definition calibrated_positive_model {Operation : Type} (eligible : Operation -> Prop) (cost : Operation -> nat) : Prop :=
    exists dissipation : Operation -> nat,
      (forall i, eligible i -> 1 <= dissipation i) /\
      (forall i, dissipation i <= cost i).

  (** Exact consistency test. Taking dissipation := cost proves mathematical
      existence, not physical calibration or an independent derivation of cost. *)
  Theorem calibrated_model_exists_iff_positive_cost {Operation : Type} (eligible : Operation -> Prop) (cost : Operation -> nat) :
    calibrated_positive_model eligible cost <-> forall i, eligible i -> 1 <= cost i.
  Proof.
    split.
    - intros [d [Hpositive Hupper]] i Hi.
      specialize (Hpositive i Hi). specialize (Hupper i). lia.
    - intro H. exists cost. split; [exact H|intro i; reflexivity].
  Qed.

Inductive bit_operation := bit_idle | bit_reset.
Definition bit_step (s : bool) (i : bit_operation) : bool :=
  match i with bit_idle => s | bit_reset => false end.
Definition bit_cost (i : bit_operation) : nat :=
  match i with bit_idle => 0 | bit_reset => 1 end.
Definition bit_loses_distinction (i : bit_operation) : Prop :=
  exists s t, s <> t /\ bit_step s i = bit_step t i.

Theorem bit_erasure_classification :
  forall i, bit_loses_distinction i <-> i = bit_reset.
Proof.
  intros []; unfold bit_loses_distinction; cbn.
  - split; [intros [s [t [H E]]]; contradiction|discriminate].
  - split; [reflexivity|intro; exists false, true; split; discriminate || reflexivity].
Qed.

Theorem bit_model_has_satisfiable_calibration :
  calibrated_positive_model bit_loses_distinction bit_cost.
Proof.
  apply calibrated_model_exists_iff_positive_cost.
  intros i H. apply bit_erasure_classification in H. subst i. cbn. lia.
Qed.

  Definition history_step {State Instruction : Type} (step : State -> Instruction -> State) (sh : State * list State) (i : Instruction) :=
    (step (fst sh) i, fst sh :: snd sh).
  Definition history_undo {State : Type} (sh : State * list State) : option (State * list State) :=
    match snd sh with [] => None | old :: history => Some (old, history) end.

  Theorem retained_history_recovers_previous_state {State Instruction : Type} (step : State -> Instruction -> State) :
    forall sh i, history_undo (history_step step sh i) = Some sh.
  Proof. intros [s h] i. reflexivity. Qed.

  Theorem retained_history_step_injective {State Instruction : Type} (step : State -> Instruction -> State) :
    forall i sh th, history_step step sh i = history_step step th i -> sh = th.
  Proof.
    intros i sh th H. apply (f_equal history_undo) in H.
    rewrite !retained_history_recovers_previous_state in H. inversion H. reflexivity.
  Qed.

  Theorem history_simulates_observed_step {State Instruction : Type} (step : State -> Instruction -> State) :
    forall sh i, fst (history_step step sh i) = step (fst sh) i.
  Proof. intros. reflexivity. Qed.

Theorem visible_reset_does_not_force_global_erasure :
  bit_step false bit_reset = bit_step true bit_reset /\
  history_step bit_step (false, []) bit_reset <>
    history_step bit_step (true, []) bit_reset /\
  (forall sh th,
    history_step bit_step sh bit_reset = history_step bit_step th bit_reset -> sh = th).
Proof.
  split; [reflexivity|split].
  - discriminate.
  - apply retained_history_step_injective.
Qed.

(** The zero-cost PC-collapse witness also has an injective history lift.
    Thus the macro-collapse criterion cannot identify global erasure. *)
Theorem zero_cost_vm_jump_has_injective_history_lift :
  instruction_cost (instr_jump 1 0) = 0 /\
  vm_pc (fst (history_step vm_apply (init_state, []) (instr_jump 1 0))) = 1 /\
  (forall sh th,
    history_step vm_apply sh (instr_jump 1 0) =
    history_step vm_apply th (instr_jump 1 0) -> sh = th).
Proof.
  split; [reflexivity|split; [reflexivity|apply retained_history_step_injective]].
Qed.
