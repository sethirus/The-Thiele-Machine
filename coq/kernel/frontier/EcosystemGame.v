(** Proved outcomes for the coordinator-free ecosystem game. *)

(* SCOPE NOTE: standalone proof scope. The game is an abstract ecosystem of
   observers and one event, with the same standing as PointerObservable.v;
   no machine is fixed. *)

From Coq Require Import Arith Bool Lia.
From Kernel Require Import EcosystemGameTarget.

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

Print Assumptions toggle_game_refutes_strong_pointer_necessity.
Print Assumptions durable_consensus_implies_permanence.
