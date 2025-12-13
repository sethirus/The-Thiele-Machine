From Coq Require Import List Bool Lia Arith.PeanoNat ZArith.
Import ListNotations.

(** * A reversible lattice gas toy model

    This file supplies a simple, nontrivial "physics-style" model: a reversible
    1D lattice gas with local swaps.  The update rule is involutive and
    conserves both particle count and a momentum-like quantity, giving us
    concrete invariants we can transport through later embeddings. *)

Inductive Cell := Empty | LeftMover | RightMover.

Definition Lattice := list Cell.

(** Observable quantities: particle count and a signed momentum tally. *)
Definition is_particle (c : Cell) : bool :=
  match c with
  | Empty => false
  | _ => true
  end.

Definition particle_count (l : Lattice) : nat :=
  length (filter is_particle l).

Lemma particle_count_cons :
  forall c xs,
    particle_count (c :: xs) = (if is_particle c then 1 else 0) + particle_count xs.
Proof.
  intros c xs. unfold particle_count. simpl.
  destruct c; simpl; reflexivity.
Qed.

Definition cell_momentum (c : Cell) : Z :=
  match c with
  | Empty => 0%Z
  | LeftMover => (-1)%Z
  | RightMover => 1%Z
  end.

Fixpoint momentum (l : Lattice) : Z :=
  match l with
  | [] => 0%Z
  | c :: tl => cell_momentum c + momentum tl
  end.

(** Pairwise reversible update: each adjacent pair swaps.  This is
    involutive and clearly conserves the multiset of cells, so both particle
    count and momentum are preserved. *)
Definition pair_update (c1 c2 : Cell) : Cell * Cell := (c2, c1).

Fixpoint physics_step (L : Lattice) : Lattice :=
  match L with
  | c1 :: c2 :: tl =>
      let '(d1, d2) := pair_update c1 c2 in d1 :: d2 :: physics_step tl
  | [c] => [c]
  | [] => []
  end.

Lemma pair_update_involutive :
  forall c1 c2, pair_update (fst (pair_update c1 c2)) (snd (pair_update c1 c2)) = (c1, c2).
Proof. intros c1 c2. destruct c1, c2; simpl; reflexivity. Qed.

Lemma particle_count_swap :
  forall c1 c2 xs,
    particle_count (c1 :: c2 :: xs) = particle_count (c2 :: c1 :: xs).
Proof. intros c1 c2 xs; destruct c1, c2; simpl; reflexivity. Qed.

Lemma momentum_swap :
  forall c1 c2 xs,
    momentum (c1 :: c2 :: xs) = momentum (c2 :: c1 :: xs).
Proof. intros c1 c2 xs; simpl; lia. Qed.

Lemma physics_step_involutive :
  forall L, physics_step (physics_step L) = L.
Proof.
  fix F 1.
  intro L; destruct L as [|c1 L']; simpl; auto.
  destruct L' as [|c2 tl]; simpl; auto.
  specialize (F tl). simpl in F. now rewrite F.
Qed.

Lemma pair_update_preserves_particle_count :
  forall c1 c2,
    particle_count [fst (pair_update c1 c2); snd (pair_update c1 c2)] =
    particle_count [c1; c2].
Proof.
  intros c1 c2. unfold pair_update, particle_count; simpl.
  repeat (destruct c1; destruct c2; simpl; try lia).
Qed.

Lemma physics_preserves_particle_count :
  forall L, particle_count (physics_step L) = particle_count L.
Proof.
  fix F 1.
  intro L; destruct L as [|c1 L']; simpl; auto.
  destruct L' as [|c2 tl]; simpl; auto.
  repeat rewrite particle_count_cons.
  rewrite F.
  destruct c1, c2; simpl; lia.
Qed.

Lemma pair_update_preserves_momentum :
  forall c1 c2,
    momentum [fst (pair_update c1 c2); snd (pair_update c1 c2)] =
    momentum [c1; c2].
Proof.
  intros c1 c2. unfold pair_update, momentum; simpl.
  repeat (destruct c1; destruct c2; simpl; lia).
Qed.

Lemma physics_preserves_momentum :
  forall L, momentum (physics_step L) = momentum L.
Proof.
  fix F 1.
  intro L; destruct L as [|c1 L']; simpl; auto.
  destruct L' as [|c2 tl]; simpl; auto.
  simpl. rewrite F. lia.
Qed.

(** Named aliases for the core physics invariants so downstream embeddings can
    cite them directly. *)
Theorem lattice_particles_conserved :
  forall L, particle_count (physics_step L) = particle_count L.
Proof. apply physics_preserves_particle_count. Qed.

Theorem lattice_momentum_conserved :
  forall L, momentum (physics_step L) = momentum L.
Proof. apply physics_preserves_momentum. Qed.

Theorem lattice_step_involutive :
  forall L, physics_step (physics_step L) = L.
Proof. apply physics_step_involutive. Qed.

(** Handy aliases so downstream embeddings can cite the conservation and
    reversibility properties directly. *)
Definition physics_conserves_particles := physics_preserves_particle_count.
Definition physics_conserves_momentum := physics_preserves_momentum.

Corollary physics_conservation_bundle :
  forall L,
    physics_step (physics_step L) = L /\
    particle_count (physics_step L) = particle_count L /\
    momentum (physics_step L) = momentum L.
Proof.
  intros L; repeat split; auto using physics_step_involutive,
    physics_preserves_particle_count, physics_preserves_momentum.
Qed.

(** Abstract embedding interface: if a concrete program [impl_step] simulates
    [physics_step] over some encoded state space, it automatically inherits the
    conservation laws.  No Thiele-specific machinery is required here; the
    assumptions can be discharged later by a simulation lemma in the VM/Thiele
    stack. *)
Section Embedding.
  Variable Encoded : Type.
  Variable encode : Lattice -> Encoded.
  Variable decode : Encoded -> Lattice.
  Variable impl_step : Encoded -> Encoded.

  Variable decode_encode_id : forall L, decode (encode L) = L.
  Variable impl_refines_physics :
    forall L, decode (impl_step (encode L)) = physics_step L.

  Lemma embedded_particle_count_conserved :
    forall L,
      particle_count (decode (impl_step (encode L))) = particle_count (decode (encode L)).
  Proof.
    intros L. rewrite impl_refines_physics, decode_encode_id.
    apply physics_preserves_particle_count.
  Qed.

  Lemma embedded_momentum_conserved :
    forall L,
      momentum (decode (impl_step (encode L))) = momentum (decode (encode L)).
  Proof.
    intros L. rewrite impl_refines_physics, decode_encode_id.
    apply physics_preserves_momentum.
  Qed.
End Embedding.

