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

(* A supplied operational model may have several successors. A deterministic
   observation-level description is adequate exactly when neither its answers
   nor its next observations depend on the distinctions the view discards.
   A representative and a permitted successor are explicit constructive data;
   no choice or empirical adequacy of the operational model is inferred. *)
Section OperationalAdequacy.
Context {Physical Visible Input Output : Type}.
Variable next : Input -> Physical -> Physical -> Prop.
Variable visible : Physical -> Visible.
Variable observe : Physical -> Output.
Variable represent : Visible -> Physical.
Variable choose_next : Input -> Physical -> Physical.
Hypothesis represent_correct : forall b, visible (represent b) = b.
Hypothesis choose_permitted : forall i s, next i s (choose_next i s).

Theorem operational_adequacy_iff :
  (exists (decode : Visible -> Output) (shadow : Input -> Visible -> Visible),
    (forall s, decode (visible s) = observe s) /\
    (forall i s t, next i s t -> visible t = shadow i (visible s))) <->
  ((forall s t, visible s = visible t -> observe s = observe t) /\
   (forall i s s' t t', visible s = visible s' ->
     next i s t -> next i s' t' -> visible t = visible t')).
Proof.
  split.
  - intros [decode [shadow [Ho Hs]]]; split.
    + intros s t E; rewrite <- (Ho s), <- (Ho t), E; reflexivity.
    + intros i s s' t t' E H H'.
      rewrite (Hs i s t H), (Hs i s' t' H'), E; reflexivity.
  - intros [Ho Hs].
    exists (fun b => observe (represent b)).
    exists (fun i b => visible (choose_next i (represent b))); split.
    + intro s; apply Ho; apply represent_correct.
    + intros i s t H; apply (Hs i s (represent (visible s)) t).
      * symmetry; apply represent_correct.
      * exact H.
      * apply choose_permitted.
Qed.
End OperationalAdequacy.

Section ObservableBranching.
Context {Physical Input Output Host : Type}.
Variable next : Input -> Physical -> Physical -> Prop.
Variable answer : Physical -> Output.

Theorem branching_answers_exclude_exact_deterministic_encoding :
  forall i s t u, next i s t -> next i s u -> answer t <> answer u ->
  ~ exists (encode : Physical -> Host) (step : Input -> Host -> Host)
           (decode : Host -> Output),
      (forall x, decode (encode x) = answer x) /\
      (forall j x y, next j x y -> encode y = step j (encode x)).
Proof.
  intros i s t u Ht Hu Hneq [encode [step [decode [Ho Hs]]]].
  apply Hneq. rewrite <- (Ho t), <- (Ho u), (Hs i s t Ht), (Hs i s u Hu).
  reflexivity.
Qed.
End ObservableBranching.

Theorem hidden_bit_blocks_visible_only_dynamics :
  ~ exists shadow : bool -> bool,
    forall s : bool * bool, shadow (fst s) = fst (snd s, snd s).
Proof.
  intros [shadow H].
  pose proof (H (false,false)) as H0; pose proof (H (false,true)) as H1.
  cbn in H0,H1; congruence.
Qed.

Print Assumptions operational_adequacy_iff.
Print Assumptions branching_answers_exclude_exact_deterministic_encoding.
Print Assumptions hidden_bit_blocks_visible_only_dynamics.
