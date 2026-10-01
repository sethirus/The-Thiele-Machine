(** Proved outcomes for the coordinator-free ecosystem game. *)

From Coq Require Import Arith Bool Lia.
From Kernel Require Import EcosystemGameTarget.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedLedger.

Lemma toggle_game_positive : 0 < observer_count toggle_game.
Proof. cbn. lia. Qed.

Lemma toggle_game_consensus : observer_consensus toggle_game.
Proof. intros s i j _ _. reflexivity. Qed.

Lemma toggle_game_authentic : observer_authenticity toggle_game.
Proof. intros s i _. reflexivity. Qed.

Lemma toggle_game_coordinator_free : coordinator_free_update toggle_game.
Proof.
  exists negb. intros s i _. reflexivity.
Qed.

Lemma toggle_game_revokes : ~ event_permanent toggle_game.
Proof.
  intros H.
  specialize (H true eq_refl).
  discriminate.
Qed.

Theorem toggle_game_refutes_strong_pointer_necessity :
  ~ strong_pointer_necessity.
Proof.
  intros H.
  apply toggle_game_revokes.
  exact (H toggle_game toggle_game_positive toggle_game_consensus
    toggle_game_authentic toggle_game_coordinator_free).
Qed.

(** Durability is sufficient, but it is the premise that rules out the
    toggle counterexample. *)
Theorem durable_consensus_implies_permanence : forall g,
  0 < observer_count g ->
  observer_authenticity g ->
  durable_views g ->
  event_permanent g.
Proof.
  intros g Hpositive Hauth Hdurable s Hevent.
  assert (Hrange : in_range g 0) by (unfold in_range; lia).
  assert (Hview : observer_view g 0 s = true).
  { rewrite Hauth by exact Hrange. exact Hevent. }
  pose proof (Hdurable s 0 Hrange Hview) as Hnext.
  rewrite Hauth in Hnext by exact Hrange.
  exact Hnext.
Qed.

(** * The VM's certification record is the durable case

    Run the game on the VM itself: the state is a VM state, the event is
    [vm_certified], every observer reads it, and a step executes one fixed
    instruction. The VM's record is durable, so durable consensus gives
    permanence, the property the toggle game lacks. *)
Definition vm_certification_game (n : nat) (i : vm_instruction) : EcosystemGame := {|
  game_state := VMState;
  observer_count := n;
  game_event := fun s => s.(vm_certified);
  observer_view := fun _ s => s.(vm_certified);
  game_step := fun s => vm_apply_u s i
|}.

Lemma vm_certification_game_consensus : forall n i,
  observer_consensus (vm_certification_game n i).
Proof. intros n i s a b _ _. reflexivity. Qed.

Lemma vm_certification_game_authentic : forall n i,
  observer_authenticity (vm_certification_game n i).
Proof. intros n i s a _. reflexivity. Qed.

Lemma vm_certification_game_durable : forall n i,
  durable_views (vm_certification_game n i).
Proof.
  intros n i s a _ H. exact (vm_apply_u_certified_permanent s i H).
Qed.

Theorem vm_certification_is_permanent_consensus : forall n i,
  0 < n -> event_permanent (vm_certification_game n i).
Proof.
  intros n i Hn.
  apply durable_consensus_implies_permanence.
  - exact Hn.
  - apply vm_certification_game_authentic.
  - apply vm_certification_game_durable.
Qed.

Print Assumptions toggle_game_refutes_strong_pointer_necessity.
Print Assumptions durable_consensus_implies_permanence.
Print Assumptions vm_certification_is_permanent_consensus.
