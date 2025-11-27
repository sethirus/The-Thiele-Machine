From Coq Require Import List Lia Arith.PeanoNat.
Import ListNotations.

(** * A dissipative lattice model

    This optional study provides a simple, explicitly irreversible dynamics to
    contrast with the reversible lattice gas.  Cells can be either [Vac] or
    [Hot]; the step function erases all heat in one sweep, so the energy
    observable is monotonically nonincreasing and strictly drops on any
    non-empty configuration. *)

Inductive Cell := Vac | Hot.
Definition Lattice := list Cell.

Definition energy (l : Lattice) : nat := length (filter (fun c => match c with Hot => true | _ => false end) l).

Definition dissipative_step (l : Lattice) : Lattice := map (fun _ => Vac) l.

Lemma dissipative_step_energy_zero :
  forall l, energy (dissipative_step l) = 0.
Proof.
  intro l. unfold energy, dissipative_step.
  induction l as [|c tl IH]; simpl; auto.
Qed.

Lemma dissipative_energy_nonincreasing :
  forall l, energy (dissipative_step l) <= energy l.
Proof.
  intro l. unfold energy, dissipative_step.
  induction l as [|c tl IH]; simpl; auto.
  destruct c; simpl; lia.
Qed.

Lemma dissipative_energy_strict_when_hot :
  forall l, energy l > 0 -> energy (dissipative_step l) < energy l.
Proof.
  intros l Hpos.
  rewrite dissipative_step_energy_zero. lia.
Qed.

(** Named form for the strict-decrease property used in dissipative embeddings
    and entropy-style lower bounds. *)
Theorem dissipative_energy_strictly_decreasing :
  forall l, energy l > 0 -> energy (dissipative_step l) < energy l.
Proof. apply dissipative_energy_strict_when_hot. Qed.

(** Abstract embedding wrapper so later proofs can transport the monotone
    energy law without committing to a specific machine. *)
Section Embedding.
  Variable Encoded : Type.
  Variable encode : Lattice -> Encoded.
  Variable decode : Encoded -> Lattice.
  Variable impl_step : Encoded -> Encoded.

  Hypothesis decode_encode_id : forall l, decode (encode l) = l.
  Hypothesis impl_refines_dissipative :
    forall l, decode (impl_step (encode l)) = dissipative_step l.

  Lemma embedded_energy_nonincreasing :
    forall l, energy (decode (impl_step (encode l))) <= energy (decode (encode l)).
  Proof.
    intros l. rewrite impl_refines_dissipative, decode_encode_id.
    apply dissipative_energy_nonincreasing.
  Qed.
End Embedding.
