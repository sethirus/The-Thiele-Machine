(* SCOPE NOTE: standalone proof scope.
   Generic transport of Minimal.Representation capacity through
   a supplied exact encoding. Independence and exact recovery are hypotheses;
   no claim that every native run realizes arbitrary profiles is assumed. *)

(* Transport the existing capacity bound through an arbitrary exact encoding. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Minimal.Representation.
Module R := Minimal.Representation.

Section Capacity.
Context {State Host Base : Type}.
Variable view : State -> Base.
Variable profile : State -> list bool.
Variable realize : list bool -> State.
Variable encode : State -> Host.
Variable host_view : Host -> Base.
Variable host_decode : Host -> list bool.
Hypothesis preserves_view : forall s, host_view (encode s) = view s.
Hypothesis preserves_profile : forall s, host_decode (encode s) = profile s.

Theorem faithful_encoding_preserves_fibre_bound : forall m b fibre,
  (forall bits, length bits = m -> view (realize bits) = b /\
    profile (realize bits) = bits) ->
  (forall h, host_view h = b -> In h fibre) ->
  2^m <= length fibre.
Proof.
  intros m b fibre Hreal Hcover.
  apply (R.independent_profiles_capacity host_view host_decode
    (fun bits => encode (realize bits)) b m fibre).
  - intros bits Hlen; rewrite preserves_view, preserves_profile; apply Hreal; exact Hlen.
  - exact Hcover.
Qed.
End Capacity.

(* The capacity obligation alone needs no ledger, versions or certification:
   an ordinary list of m bits attains the exact finite bound. *)
Section Attained.
Context {Base : Type}.
Variable b : Base.
Definition bit_states m := map (fun bits => (b,bits)) (R.profiles m).

Theorem ordinary_bits_attain_the_bound : forall m,
  NoDup (bit_states m) /\ length (bit_states m) = 2^m /\
  (forall bits, length bits = m ->
    In (b,bits) (bit_states m) /\ fst (b,bits) = b /\ snd (b,bits) = bits).
Proof.
  intro m; split.
  - apply R.map_injective_nodup; [apply R.profiles_nodup|intros; congruence].
  - split.
    + unfold bit_states; rewrite map_length, R.profiles_length; reflexivity.
    + intros bits H; split.
      * apply in_map; apply R.profiles_complete; exact H.
      * split; reflexivity.
Qed.
End Attained.

(* One Boolean question needs only two states, however long the history.
   Requiring one latch is not requiring recovery of every individual event. *)
Definition any_record (history : list bool) := existsb (fun b => b) history.
Theorem one_latch_does_not_require_history_recovery :
  any_record [true;false] = any_record [false;true] /\
  [true;false] <> [false;true].
Proof. split; [reflexivity|discriminate]. Qed.

Print Assumptions faithful_encoding_preserves_fibre_bound.
Print Assumptions ordinary_bits_attain_the_bound.
Print Assumptions one_latch_does_not_require_history_recovery.
