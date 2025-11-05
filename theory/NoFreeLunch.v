Set Implicit Arguments.

(* NoFreeLunch.v — formal impossibility of information without physical distinction *)

Record PhysicalState := {
  observe : Prop
}.

Definition Represents (s : PhysicalState) (p : Prop) : Prop := observe s = p.

Definition state_of (p : Prop) : PhysicalState := {| observe := p |}.

Definition Ghost : Prop :=
  exists p q : Prop,
    p <> q /\ (forall s : PhysicalState, Represents s p -> Represents s q).

Lemma ghost_impossible : Ghost -> False.
Proof.
  intros [p [q [Hneq Hghost]]].
  pose (s := state_of p).
  assert (Hp : Represents s p) by reflexivity.
  specialize (Hghost s Hp).
  unfold Represents in Hghost.
  apply Hneq.
  exact Hghost.
Qed.

Theorem NoFreeLunch :
  forall p q : Prop,
    p <> q ->
    exists s : PhysicalState,
      (Represents s p /\ ~ Represents s q) \/
      (~ Represents s p /\ Represents s q).
Proof.
  intros p q Hneq.
  exists (state_of p).
  left.
  split.
  - reflexivity.
  - intro Hrep.
    apply Hneq.
    exact Hrep.
Qed.
