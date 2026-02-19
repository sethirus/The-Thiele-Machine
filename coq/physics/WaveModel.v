From Coq Require Import List Arith.PeanoNat Lia ZArith.
Import ListNotations.

Fixpoint map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => f x1 x2 :: map2 f t1 t2
  | _, _ => []
  end.

(** [map2_length]: formal specification. *)
Lemma map2_length : forall A B C (f : A -> B -> C) l1 l2,
  (* SAFE: Bounded arithmetic operation with explicit domain *)
    length (map2 f l1 l2) = Nat.min (length l1) (length l2).
Proof.
  intros A B C f l1; induction l1 as [|x xs IH]; intros l2; destruct l2; simpl; try reflexivity.
  simpl. rewrite IH. reflexivity.
Qed.

(** * A discrete wave/propagation model

    This optional study captures a simple 1D wave-style dynamics: left-moving
    amplitudes shift left while right-moving amplitudes shift right on a
    periodic lattice.  The step is reversible, conserves both total energy and
    a momentum-like difference, and admits an explicit inverse. *)

Record WaveCell := {
  left_amp : nat;
  right_amp : nat
}.

Definition WaveState := list WaveCell.

(** Basic combinators for sums and rotations. *)
Fixpoint sum_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(** [sum_list_app]: formal specification. *)
Lemma sum_list_app : forall a b, sum_list (a ++ b) = sum_list a + sum_list b.
Proof.
  induction a as [|x xs IH]; intros b; simpl; auto.
  rewrite IH. lia.
Qed.

Definition rotate_left {A} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => xs ++ [x]
  end.

Definition rotate_right {A} (l : list A) : list A :=
  match rev l with
  | [] => []
  | x :: xs => x :: rev xs
  end.

(** [rotate_left_length]: formal specification. *)
Lemma rotate_left_length : forall A (l : list A), length (rotate_left l) = length l.
Proof.
  intros A l; destruct l; simpl; auto.
  rewrite app_length. simpl. lia.
Qed.

(** [rotate_right_length]: formal specification. *)
Lemma rotate_right_length : forall A (l : list A), length (rotate_right l) = length l.
Proof.
  intros A l; unfold rotate_right.
  destruct (rev l) as [|x xs] eqn:Hrev; simpl.
  - rewrite <- (rev_length l). rewrite Hrev. reflexivity.
  - rewrite <- (rev_length l).
    rewrite Hrev. simpl. rewrite rev_length. reflexivity.
Qed.

(** [sum_list_rotate_left]: formal specification. *)
Lemma sum_list_rotate_left : forall l, sum_list (rotate_left l) = sum_list l.
Proof.
  destruct l as [|x xs]; simpl; auto.
  rewrite (sum_list_app xs [x]). simpl; lia.
Qed.

(** [sum_list_rotate_right]: formal specification. *)
Lemma sum_list_rotate_right : forall l, sum_list (rotate_right l) = sum_list l.
Proof.
  intro l.
  unfold rotate_right.
  destruct (rev l) as [|x xs] eqn:Hrev; simpl; auto.
  - assert (length l = 0) by (rewrite <- rev_length, Hrev; reflexivity).
    apply length_zero_iff_nil in H. subst. reflexivity.
  - pose proof (rev_involutive l) as Hinv.
    rewrite Hrev in Hinv. simpl in Hinv.
    rewrite <- Hinv. rewrite sum_list_app. simpl. lia.
Qed.

(** [rotate_right_left_inv]: formal specification. *)
Lemma rotate_right_left_inv : forall A (l : list A), rotate_right (rotate_left l) = l.
Proof.
  intro A; destruct l as [|x xs]; simpl; auto.
  unfold rotate_right. simpl.
  rewrite rev_app_distr. simpl. now rewrite rev_involutive.
Qed.

(** [rotate_left_right_inv]: formal specification. *)
Lemma rotate_left_right_inv : forall A (l : list A), rotate_left (rotate_right l) = l.
Proof.
  intros A l; unfold rotate_right.
  destruct (rev l) as [|y ys] eqn:Hrev; simpl; auto.
  - assert (length l = 0) by (rewrite <- rev_length, Hrev; reflexivity).
    apply length_zero_iff_nil in H. subst. reflexivity.
  - assert (rev ys ++ [y] = l) by (pose proof (rev_involutive l) as Hinv; rewrite Hrev in Hinv; simpl in Hinv; exact Hinv).
    exact H.
Qed.

(** [map2_map_both]: formal specification. *)
Lemma map2_map_both : forall (X A B C : Type) (f : A -> B -> C) (g : X -> A) (h : X -> B) (xs : list X),
    map2 f (map g xs) (map h xs) = map (fun x => f (g x) (h x)) xs.
Proof.
  induction xs as [|x xs IH]; simpl; auto.
  now rewrite IH.
Qed.

(** [map_left_of_cells]: formal specification. *)
Lemma map_left_of_cells : forall l1 l2,
    length l1 = length l2 ->
    map left_amp (map2 (fun l r => {| left_amp := l; right_amp := r |}) l1 l2) = l1.
Proof.
  induction l1 as [|a tl IH]; intros l2 Hlen; destruct l2; simpl in *; try discriminate; auto.
  inversion Hlen as [Hlen'].
  f_equal. apply IH. exact Hlen'.
Qed.

(** [map_right_of_cells]: formal specification. *)
Lemma map_right_of_cells : forall l1 l2,
    length l1 = length l2 ->
    map right_amp (map2 (fun l r => {| left_amp := l; right_amp := r |}) l1 l2) = l2.
Proof.
  induction l1 as [|a tl IH]; intros l2 Hlen; destruct l2; simpl in *; try discriminate; auto.
  inversion Hlen as [Hlen'].
  f_equal. apply IH. exact Hlen'.
Qed.

(** [rebuild_cells]: formal specification. *)
Lemma rebuild_cells : forall s,
    map (fun c => {| left_amp := left_amp c; right_amp := right_amp c |}) s = s.
Proof.
  induction s as [|c tl IH]; simpl; auto.
  destruct c as [l r]. simpl. f_equal. apply IH.
Qed.

(** ** Wave dynamics *)
Definition wave_step (s : WaveState) : WaveState :=
  let lefts := rotate_left (map left_amp s) in
  let rights := rotate_right (map right_amp s) in
  map2 (fun l r => {| left_amp := l; right_amp := r |}) lefts rights.

Definition wave_step_inv (s : WaveState) : WaveState :=
  let lefts := rotate_right (map left_amp s) in
  let rights := rotate_left (map right_amp s) in
  map2 (fun l r => {| left_amp := l; right_amp := r |}) lefts rights.

Definition total_left (s : WaveState) : nat := sum_list (map left_amp s).
Definition total_right (s : WaveState) : nat := sum_list (map right_amp s).
Definition wave_energy (s : WaveState) : nat := total_left s + total_right s.
Definition wave_momentum (s : WaveState) : Z :=
  Z.of_nat (total_right s) - Z.of_nat (total_left s).

(** [wave_step_length]: formal specification. *)
Lemma wave_step_length : forall s, length (wave_step s) = length s.
Proof.
  intro s. unfold wave_step.
  set (ls := map left_amp s).
  set (rs := map right_amp s).
  simpl.
  rewrite map2_length.
  rewrite rotate_left_length, rotate_right_length.
  subst ls rs. rewrite !map_length. rewrite Nat.min_idempotent. reflexivity.
Qed.

(** [wave_step_inv_length]: formal specification. *)
Lemma wave_step_inv_length : forall s, length (wave_step_inv s) = length s.
Proof.
  intro s. unfold wave_step_inv.
  set (ls := map left_amp s).
  set (rs := map right_amp s).
  simpl.
  rewrite map2_length.
  rewrite rotate_right_length, rotate_left_length.
  subst ls rs. rewrite !map_length. rewrite Nat.min_idempotent. reflexivity.
Qed.

(** [wave_step_inverse]: formal specification. *)
Lemma wave_step_inverse : forall s, wave_step_inv (wave_step s) = s.
Proof.
  intro s.
  unfold wave_step, wave_step_inv.
  set (ls := map left_amp s).
  set (rs := map right_amp s).
  simpl.
  assert (Hlen : length ls = length rs).
  { subst ls rs. repeat rewrite map_length. reflexivity. }
  assert (Hleft : map left_amp (map2 (fun l r => {| left_amp := l; right_amp := r |}) (rotate_left ls) (rotate_right rs)) = rotate_left ls).
  { apply map_left_of_cells.
    rewrite rotate_left_length, rotate_right_length. exact Hlen. }
  assert (Hright : map right_amp (map2 (fun l r => {| left_amp := l; right_amp := r |}) (rotate_left ls) (rotate_right rs)) = rotate_right rs).
  { apply map_right_of_cells.
    rewrite rotate_left_length, rotate_right_length. exact Hlen. }
  simpl in Hleft, Hright.
  rewrite Hleft, Hright.
  rewrite rotate_right_left_inv, rotate_left_right_inv.
  subst ls rs.
  rewrite map2_map_both.
  simpl. apply rebuild_cells.
Qed.

(** [wave_step_preserves_left]: formal specification. *)
Lemma wave_step_preserves_left : forall s, total_left (wave_step s) = total_left s.
Proof.
  intro s. unfold wave_step, total_left.
  set (ls := map left_amp s).
  set (rs := map right_amp s).
  simpl.
  assert (Hlen : length (rotate_left ls) = length (rotate_right rs)).
  { subst ls rs. rewrite rotate_left_length, rotate_right_length. repeat rewrite map_length. reflexivity. }
  pose proof (map_left_of_cells (rotate_left ls) (rotate_right rs) Hlen) as Hleft.
  rewrite Hleft. subst ls rs. rewrite sum_list_rotate_left. reflexivity.
Qed.

(** [wave_step_preserves_right]: formal specification. *)
Lemma wave_step_preserves_right : forall s, total_right (wave_step s) = total_right s.
Proof.
  intro s. unfold wave_step, total_right.
  set (ls := map left_amp s).
  set (rs := map right_amp s).
  simpl.
  assert (Hlen : length (rotate_left ls) = length (rotate_right rs)).
  { subst ls rs. rewrite rotate_left_length, rotate_right_length. repeat rewrite map_length. reflexivity. }
  pose proof (map_right_of_cells (rotate_left ls) (rotate_right rs) Hlen) as Hright.
  rewrite Hright. subst ls rs. rewrite sum_list_rotate_right. reflexivity.
Qed.

(** [wave_energy_conserved]: formal specification. *)
Theorem wave_energy_conserved : forall s, wave_energy (wave_step s) = wave_energy s.
Proof.
  intro s. unfold wave_energy.
  rewrite wave_step_preserves_left, wave_step_preserves_right. reflexivity.
Qed.

(** [wave_momentum_conserved]: formal specification. *)
Theorem wave_momentum_conserved : forall s, wave_momentum (wave_step s) = wave_momentum s.
Proof.
  intro s. unfold wave_momentum.
  rewrite wave_step_preserves_left, wave_step_preserves_right. lia.
Qed.

(** [wave_step_reversible]: formal specification. *)
Theorem wave_step_reversible : forall s, wave_step_inv (wave_step s) = s.
Proof. apply wave_step_inverse. Qed.

(** [wave_conservation_bundle]: formal specification. *)
Corollary wave_conservation_bundle :
  forall s,
    wave_step_inv (wave_step s) = s /\
    wave_energy (wave_step s) = wave_energy s /\
    wave_momentum (wave_step s) = wave_momentum s.
Proof.
  intro s; repeat split; auto using wave_step_inverse, wave_energy_conserved, wave_momentum_conserved.
Qed.

(** Abstract embedding helper for reuse in VM/Thiele contexts. *)
Section Embedding.
  Variable Encoded : Type.
  Variable encode : WaveState -> Encoded.
  Variable decode : Encoded -> WaveState.
  Variable impl_step : Encoded -> Encoded.

  Variable decode_encode_id : forall s, decode (encode s) = s.
  Variable impl_refines_wave : forall s, decode (impl_step (encode s)) = wave_step s.

  (** [embedded_energy_conserved]: formal specification. *)
  Lemma embedded_energy_conserved :
    forall s, wave_energy (decode (impl_step (encode s))) = wave_energy (decode (encode s)).
  Proof.
    intro s. rewrite impl_refines_wave, decode_encode_id.
    apply wave_energy_conserved.
  Qed.

  (** [embedded_momentum_conserved]: formal specification. *)
  Lemma embedded_momentum_conserved :
    forall s, wave_momentum (decode (impl_step (encode s))) = wave_momentum (decode (encode s)).
  Proof.
    intro s. rewrite impl_refines_wave, decode_encode_id.
    apply wave_momentum_conserved.
  Qed.
End Embedding.
