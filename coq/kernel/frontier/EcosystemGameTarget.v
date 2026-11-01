(** Target for the coordinator-free ecosystem game. *)

From Coq Require Import Arith Bool.

(* SCOPE NOTE: standalone proof scope.  This is an abstract distributed
   observation game; correspondence to a deployed protocol is not assumed. *)

Record EcosystemGame : Type := {
  game_state : Type;
  observer_count : nat;
  game_event : game_state -> bool;
  observer_view : nat -> game_state -> bool;
  game_step : game_state -> game_state
}.

Definition in_range (g : EcosystemGame) (i : nat) : Prop :=
  i < observer_count g.

Definition observer_consensus (g : EcosystemGame) : Prop :=
  forall s i j,
    in_range g i -> in_range g j ->
    observer_view g i s = observer_view g j s.

(** Boolean soundness and completeness for every observer. *)
Definition observer_authenticity (g : EcosystemGame) : Prop :=
  forall s i, in_range g i -> observer_view g i s = game_event g s.

(** The next public view is computed by the same local rule at every
    observer.  The rule receives neither an observer index nor coordinator
    state. *)
Definition coordinator_free_update (g : EcosystemGame) : Prop :=
  exists local : bool -> bool,
    forall s i, in_range g i ->
      observer_view g i (game_step g s) = local (observer_view g i s).

Definition event_permanent (g : EcosystemGame) : Prop :=
  forall s, game_event g s = true -> game_event g (game_step g s) = true.

Definition durable_views (g : EcosystemGame) : Prop :=
  forall s i, in_range g i ->
    observer_view g i s = true ->
    observer_view g i (game_step g s) = true.

Definition strong_pointer_necessity : Prop :=
  forall g,
    0 < observer_count g ->
    observer_consensus g ->
    observer_authenticity g ->
    coordinator_free_update g ->
    event_permanent g.

Definition toggle_game : EcosystemGame := {|
  game_state := bool;
  observer_count := 2;
  game_event := fun b => b;
  observer_view := fun _ b => b;
  game_step := negb
|}.
