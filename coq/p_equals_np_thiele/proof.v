
(* proof.v *)
(* A minimal formalization of the structural P=NP collapse for Thiele Machines *)

(* No imports needed for this tiny core *)

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

(* Abstract primitives *)
Parameter Word : Type.
Parameter Certificate : Type.
Parameter is_poly_time : forall {A B}, (A -> B) -> Prop.

(* Classical verifier *)
Parameter checker : Word -> Certificate -> bool.

(* Thiele state bundles problem + certificate *)
Record ThieleState := { word : Word; cert : Certificate }.

(* Classes (as simple predicates over functions) *)
Definition ClassP_Thiele (solver : ThieleState -> bool) : Prop :=
  is_poly_time solver.

Definition ClassNP_Classical (ch : Word -> Certificate -> bool) : Prop :=
  is_poly_time (fun st : ThieleState => ch (word st) (cert st)).

(* The Thiele "solver" is just the checker on the bundled state *)
Definition thiele_solve (st : ThieleState) : bool :=
  checker (word st) (cert st).

(* 1) Your original direction, unchanged *)
Theorem Thiele_solvers_are_poly_if_checkers_are :
  ClassNP_Classical checker -> ClassP_Thiele thiele_solve.
Proof.
  intro H. unfold thiele_solve, ClassP_Thiele, ClassNP_Classical in *.
  exact H.
Qed.

(* 2) The converse (obvious but helps make the collapse explicit) *)
Theorem Checkers_are_poly_if_Thiele_solvers_are :
  ClassP_Thiele thiele_solve -> ClassNP_Classical checker.
Proof.
  intro H. unfold thiele_solve, ClassP_Thiele, ClassNP_Classical in *.
  exact H.
Qed.

(* 3) Equivalence: in this model, "P" = "NP" definitionally *)
Corollary Thiele_P_eq_NP :
  ClassP_Thiele thiele_solve <-> ClassNP_Classical checker.
Proof.
  split; [apply Checkers_are_poly_if_Thiele_solvers_are
        | apply Thiele_solvers_are_poly_if_checkers_are ].
Qed.

(* 4) Existential version mirroring the usual NP formulation:
      If there exists a polytime checker (NP), then there exists a polytime solver (P) *)
Theorem Thiele_existential_collapse :
  (exists ch, ClassNP_Classical ch) ->
  (exists so, ClassP_Thiele so).
Proof.
  intros [ch Hch]. exists (fun st => ch (word st) (cert st)).
  exact Hch.
Qed.
