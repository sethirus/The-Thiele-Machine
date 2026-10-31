(** NecWPointer: the pointer chapter pushed to its limits.

    - The toy: three observers are not needed. Certification is the unique
      pointer among the rival "work at least 1" exactly when there is at
      least one observer; with none, every event proliferates vacuously.
    - One blind observer: the observer must be in range and the event must
      hold where it is blind; both are needed. The converse fails: an
      observer that reports an event that did not happen also blocks
      proliferation, with no blind observer anywhere. Either kind of wrong
      observer is enough.
    - Durability: one authentic, durable observer is enough for a permanent
      event; the repository's theorem is the case of observer 0. Each
      premise is needed (no observers; views that are not authentic; views
      that are not durable). Given authentic views and at least one
      observer, durable views and a permanent event are the same thing. *)

(* SCOPE NOTE: standalone proof scope. Observers, events and pointers of the
   ecosystem game, stated over abstract events and views; no machine is
   fixed. *)

From Coq Require Import List Lia Bool Arith.PeanoNat.
Import ListNotations.
From Kernel Require Import PointerObservable PointerObservableCounterexamples.
From Kernel Require Import EcosystemGameTarget EcosystemGame.
Import ReplicatedLedgerToy.

(* ================================================================= *)
(** * 1. The toy: one observer is enough, none is not                 *)
(* ================================================================= *)

Definition nec_w_toy_n (N : nat) : Ecosystem := {|
  eco_state := ToyState;
  eco_observers := N;
  eco_fragment := fun _ s => toy_cert s
|}.

Theorem nec_w_toy_observers_iff :
  forall N, unique_pointer_among (nec_w_toy_n N) cert_event [work_event] <-> 1 <= N.
Proof.
  intros N. split.
  - intros [_ Hr]. destruct N as [| N]; [| lia].
    exfalso. inversion Hr as [| ? ? Hw _]. apply Hw. intros i Hi. simpl in Hi. lia.
  - intros HN. split.
    + intros i Hi s. unfold cert_event. simpl. reflexivity.
    + constructor; [| constructor].
      intros H. specialize (H 0 HN {| toy_cert := false; toy_work := 1 |}).
      unfold work_event in H. simpl in H. destruct H as [Hf _].
      specialize (Hf ltac:(lia)). discriminate.
Qed.

(* ================================================================= *)
(** * 2. One blind observer                                           *)
(* ================================================================= *)

(** One faithful observer and a blind fragment at index 1, outside the
    range. *)
Definition nec_w_eco_out : Ecosystem := {|
  eco_state := bool;
  eco_observers := 1;
  eco_fragment := fun i s => if Nat.eqb i 0 then s else false
|}.

Theorem nec_w_blind_needs_in_range :
  eco_fragment nec_w_eco_out 1 true = false /\
  (fun s : bool => s = true) true /\
  redundantly_proliferating nec_w_eco_out (fun s => s = true).
Proof.
  split; [reflexivity | split; [reflexivity |]].
  intros i Hi s. simpl in Hi. assert (i = 0) by lia. subst i. simpl. tauto.
Qed.

(** A blind fragment where the event fails does not block it. *)
Definition nec_w_eco_one : Ecosystem := {|
  eco_state := bool;
  eco_observers := 1;
  eco_fragment := fun _ s => s
|}.

Theorem nec_w_blind_needs_event :
  eco_fragment nec_w_eco_one 0 false = false /\
  ~ (fun s : bool => s = true) false /\
  redundantly_proliferating nec_w_eco_one (fun s => s = true).
Proof.
  split; [reflexivity | split; [discriminate |]].
  intros i Hi s. simpl. tauto.
Qed.

(** The converse fails: an observer that always says yes blocks
    proliferation and is blind nowhere. *)
Definition nec_w_eco_liar : Ecosystem := {|
  eco_state := bool;
  eco_observers := 1;
  eco_fragment := fun _ _ => true
|}.

Theorem nec_w_blind_converse_refuted :
  ~ redundantly_proliferating nec_w_eco_liar (fun s => s = true) /\
  ~ exists i s, i < eco_observers nec_w_eco_liar /\ eco_fragment nec_w_eco_liar i s = false.
Proof.
  split.
  - intros H. specialize (H 0 ltac:(simpl; lia) false). simpl in H.
    destruct H as [_ H]. specialize (H eq_refl). discriminate.
  - intros [i [s [_ H]]]. discriminate.
Qed.

(** Either kind of wrong observer is enough. *)
Theorem nec_w_wrong_observer_blocks :
  forall (eco : Ecosystem) (E : eco_state eco -> Prop) i s,
    i < eco_observers eco ->
    (E s /\ eco_fragment eco i s = false) \/ (~ E s /\ eco_fragment eco i s = true) ->
    ~ redundantly_proliferating eco E.
Proof.
  intros eco E i s Hi [[HE Hf] | [HnE Hf]] H.
  - exact (blind_observer_blocks_proliferation eco E i s Hi Hf HE H).
  - apply HnE. apply (H i Hi s). exact Hf.
Qed.

(* ================================================================= *)
(** * 3. Durability                                                   *)
(* ================================================================= *)

Theorem nec_w_one_durable_observer_enough :
  forall g i, in_range g i ->
    (forall s, observer_view g i s = game_event g s) ->
    (forall s, observer_view g i s = true -> observer_view g i (game_step g s) = true) ->
    event_permanent g.
Proof.
  intros g i Hi Hauth Hdur s He.
  rewrite <- Hauth. apply Hdur. rewrite Hauth. exact He.
Qed.

Corollary nec_w_durable_corollary : forall g,
  0 < observer_count g -> observer_authenticity g -> durable_views g -> event_permanent g.
Proof.
  intros g Hpos Hauth Hdur.
  apply (nec_w_one_durable_observer_enough g 0 Hpos).
  - intros s. apply Hauth. exact Hpos.
  - intros s. apply Hdur. exact Hpos.
Qed.

Definition nec_w_game (n : nat) (view : nat -> bool -> bool) : EcosystemGame := {|
  game_state := bool;
  observer_count := n;
  game_event := fun b => b;
  observer_view := view;
  game_step := negb
|}.

Theorem nec_w_durable_premises_needed :
  (* no observers *)
  (observer_authenticity (nec_w_game 0 (fun _ b => b)) /\
   durable_views (nec_w_game 0 (fun _ b => b)) /\
   ~ event_permanent (nec_w_game 0 (fun _ b => b))) /\
  (* views that are not authentic *)
  (0 < observer_count (nec_w_game 2 (fun _ _ => true)) /\
   durable_views (nec_w_game 2 (fun _ _ => true)) /\
   ~ observer_authenticity (nec_w_game 2 (fun _ _ => true)) /\
   ~ event_permanent (nec_w_game 2 (fun _ _ => true))) /\
  (* views that are not durable *)
  (0 < observer_count toggle_game /\ observer_authenticity toggle_game /\
   ~ durable_views toggle_game /\ ~ event_permanent toggle_game).
Proof.
  split; [| split].
  - split; [intros s i Hi; unfold in_range in Hi; simpl in Hi; lia |].
    split; [intros s i Hi; unfold in_range in Hi; simpl in Hi; lia |].
    intros H. specialize (H true eq_refl). discriminate.
  - split; [simpl; lia |]. split; [intros s i _ _; reflexivity |].
    split; [intros H; specialize (H false 0 ltac:(unfold in_range; simpl; lia)); discriminate |].
    intros H. specialize (H true eq_refl). discriminate.
  - split; [exact toggle_game_positive | split; [exact toggle_game_authentic |]].
    split; [| exact toggle_game_revokes].
    intros H. specialize (H true 0 ltac:(unfold in_range; simpl; lia) eq_refl). discriminate.
Qed.

(** With authentic views and at least one observer, durable views and a
    permanent event are the same thing. *)
Theorem nec_w_durable_iff_permanent :
  forall g, 0 < observer_count g -> observer_authenticity g ->
    (durable_views g <-> event_permanent g).
Proof.
  intros g Hpos Hauth. split.
  - apply durable_consensus_implies_permanence; assumption.
  - intros Hp s i Hi Hv. rewrite Hauth in Hv |- * by exact Hi. apply Hp. exact Hv.
Qed.

Print Assumptions nec_w_toy_observers_iff.
Print Assumptions nec_w_blind_needs_in_range.
Print Assumptions nec_w_blind_needs_event.
Print Assumptions nec_w_blind_converse_refuted.
Print Assumptions nec_w_wrong_observer_blocks.
Print Assumptions nec_w_one_durable_observer_enough.
Print Assumptions nec_w_durable_corollary.
Print Assumptions nec_w_durable_premises_needed.
Print Assumptions nec_w_durable_iff_permanent.
