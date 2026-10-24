(* SCOPE NOTE: standalone proof scope.
   Generic output/transition factorization with an explicit section.
   It tests the proposed quotient interpretation without assuming a product
   decomposition or the native certification implementation. *)

(* Exact conditions for implementing an observation on the chosen base.
   A supplied section avoids any quotient or choice axiom. *)
From Coq Require Import List.
Import ListNotations.

Section Contract.
Context {State Base Input Answer : Type}.
Variable view : State -> Base.
Variable representative : Base -> State.
Hypothesis section_law : forall b, view (representative b) = b.
Variable step : Input -> State -> State.
Variable answer : State -> Answer.

Definition output_factors := exists decode : Base -> Answer,
  forall s, decode (view s) = answer s.
Definition output_constant := forall s t,
  view s = view t -> answer s = answer t.
Definition step_factors := exists shadow : Input -> Base -> Base,
  forall i s, view (step i s) = shadow i (view s).
Definition step_stable := forall i s t,
  view s = view t -> view (step i s) = view (step i t).

Theorem output_factorization_iff : output_factors <-> output_constant.
Proof.
  split.
  - intros [decode H] s t E; rewrite <- (H s), <- (H t), E; reflexivity.
  - intro H; exists (fun b => answer (representative b)); intro s.
    apply H; apply section_law.
Qed.

Theorem transition_factorization_iff : step_factors <-> step_stable.
Proof.
  split.
  - intros [shadow H] i s t E; rewrite !H, E; reflexivity.
  - intro H; exists (fun i b => view (step i (representative b))).
    intros i s; apply H; symmetry; apply section_law.
Qed.

Theorem base_only_implementation_iff :
  (output_factors /\ step_factors) <-> (output_constant /\ step_stable).
Proof. rewrite output_factorization_iff, transition_factorization_iff; reflexivity. Qed.
End Contract.

Section ChangeOfEncoding.
Context {State Host Input Answer Base : Type}.
Variable step : Input -> State -> State.
Variable host_step : Input -> Host -> Host.
Variable encode : State -> Host.
Variable answer : State -> Answer.
Variable host_answer : Host -> Answer.
Hypothesis commutes : forall i s, encode (step i s) = host_step i (encode s).
Hypothesis preserves_answer : forall s, host_answer (encode s) = answer s.

Fixpoint run (w : list Input) (s : State) :=
  match w with [] => s | i::rest => run rest (step i s) end.
Fixpoint host_run (w : list Input) (s : Host) :=
  match w with [] => s | i::rest => host_run rest (host_step i s) end.

Theorem encoding_preserves_runs : forall w s,
  encode (run w s) = host_run w (encode s).
Proof. induction w; intro s; cbn; [reflexivity|rewrite IHw, commutes; reflexivity]. Qed.

Theorem encoding_cannot_merge_distinguishable_states : forall s t w,
  answer (run w s) <> answer (run w t) -> encode s <> encode t.
Proof.
  intros s t w H E; apply H.
  rewrite <- !preserves_answer, !encoding_preserves_runs, E; reflexivity.
Qed.

Variable view : State -> Base.
Variable host_view : Host -> Base.
Hypothesis preserves_view : forall s, host_view (encode s) = view s.

Theorem hidden_pair_survives_view_preserving_encoding : forall s t,
  view s = view t -> answer s <> answer t ->
  encode s <> encode t /\ host_view (encode s) = host_view (encode t) /\
  host_answer (encode s) <> host_answer (encode t).
Proof.
  intros s t Hv Ha; split.
  - intro E; apply Ha; rewrite <- !preserves_answer, E; reflexivity.
  - split; [rewrite !preserves_view|rewrite !preserves_answer]; assumption.
Qed.
End ChangeOfEncoding.

Print Assumptions output_factorization_iff.
Print Assumptions transition_factorization_iff.
Print Assumptions base_only_implementation_iff.
Print Assumptions encoding_preserves_runs.
Print Assumptions encoding_cannot_merge_distinguishable_states.
Print Assumptions hidden_pair_survives_view_preserving_encoding.
