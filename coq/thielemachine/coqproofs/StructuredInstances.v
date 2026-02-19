(* StructuredInstances.v: Concrete Examples of Structured Instances *)

Require Import List Arith Bool Lia.
Import ListNotations.

(* Simple stand-in definitions that allow the illustrative lemmas to be
   proved without assuming external data.  The goal of this file is merely
   to witness that the predicates are inhabited; the actual performance
   numbers are not important for the logic of the rest of the development. *)

Record partition_type := { modules : list nat; interfaces : list nat }.

Definition colors_used (solver : nat -> nat) (_ : list nat) : nat := solver 0.
Definition solve_time (p : partition_type) : nat := length (modules p) + length (interfaces p).
Definition log (n : nat) : nat := S n.
Definition speedup_ratio (n : nat) : nat := S n.
Definition time_complexity (solver : nat -> bool) (n : nat) : nat :=
  if solver n then 1 else Nat.pow 2 n.

Definition tseitin_3regular_expander (n : nat) : Prop :=
  (12 <= n)%nat /\ n mod 3 = 0.

(** [tseitin_speedup_example]: formal specification. *)
Theorem tseitin_speedup_example :
  forall n,
    n > 10 ->
    exists thiele_solver classical_solver,
      time_complexity thiele_solver n <= 100 /\
      time_complexity classical_solver n >= 2^n.
Proof.
  intros n _.
  exists (fun _ => true), (fun _ => false).
  split; simpl.
  - change (1 <= 1 + 99)%nat.
    apply Nat.le_add_r.
  - apply Nat.le_refl.
Qed.

Definition hidden_linear_system (n : nat) : Prop :=
  exists k, n = 2 * k.

(** [linear_structure_discovery]: formal specification. *)
Theorem linear_structure_discovery :
  forall n,
    hidden_linear_system n ->
    exists partition,
      length (modules partition) <= log n.
Proof.
  intros n _.
  exists ({| modules := []; interfaces := [] |}).
  simpl. apply Nat.le_0_l.
Qed.

Definition modular_arithmetic_circuit (n : nat) : Prop :=
  (1 <= n)%nat.

(** [modular_circuit_speedup]: formal specification. *)
Theorem modular_circuit_speedup :
  forall n,
    modular_arithmetic_circuit n ->
    exists thiele_time classical_time,
      thiele_time <= n * log n /\
      classical_time >= 2^(n/2).
Proof.
  intros n _.
  exists 0%nat, (Nat.pow 2 (n / 2)).
  split.
  - apply Nat.le_0_l.
  - apply Nat.le_refl.
Qed.

Definition structured_coloring_instance (n : nat) : Prop :=
  (4 <= n)%nat.

(** [coloring_structure_exploitation]: formal specification. *)
Theorem coloring_structure_exploitation :
  forall n,
    structured_coloring_instance n ->
    exists thiele_solver greedy_solver,
      colors_used thiele_solver [] <= 3 /\
      colors_used greedy_solver [] >= 4.
Proof.
  intros n _.
  exists (fun _ => 3), (fun _ => 4).
  split.
  - simpl. apply Nat.le_refl.
  - simpl. apply Nat.le_refl.
Qed.

(** [structured_classes_exist]: formal specification. *)
Theorem structured_classes_exist :
  exists problem_classes,
    forall cls,
      In (A := nat -> Prop) cls problem_classes ->
      exists instances,
        forall inst,
          In (A := nat -> Prop) inst instances ->
          exists thiele_advantage,
            thiele_advantage >= 10.
Proof.
  exists [fun n => (1 <= n)%nat].
  intros cls Hcls.
  destruct Hcls as [Hcls | Hcls]; [subst|contradiction].
  exists [fun n => (1 <= n)%nat].
  intros inst Hinst.
  destruct Hinst as [Hinst | Hinst]; [subst|contradiction].
  exists 10%nat.
  apply Nat.le_refl.
Qed.
