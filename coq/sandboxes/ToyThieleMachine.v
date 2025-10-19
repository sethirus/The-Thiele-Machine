Require Import List.
Require Import Nat.

Import ListNotations.

(** * A Toy Thiele Machine Microcosm

    This development implements the "microcosm" experiment described in the
    narrative: a minimal universe where a Thiele-style instruction admits a
    behaviour that a classical Turing interpreter cannot emulate.  The tape is a
    list of natural numbers with fixed length eight.  Turing instructions can
    write the value [1] at a specific position, but they can never introduce
    zeroes.  The Thiele machine extends this vocabulary with a geometric
    [ClaimLeftZero] instruction that forces the left half of the tape to the
    value [0] while incurring a µ-bit cost.
*)

Module ToyThiele.

(** ** Machine state and helpers *)

Record state := {
  tape : list nat;
  mu_cost : nat
}.

Definition initial_tape : list nat := [1;1;1;1;1;1;1;1].
Definition target_tape  : list nat := [0;0;0;0;1;1;1;1].

Definition initial_state : state := {| tape := initial_tape; mu_cost := 0 |}.

Definition left_half_length : nat := 4.

Fixpoint replace_with_one (idx : nat) (l : list nat) : list nat :=
  match l, idx with
  | [], _ => []
  | _ :: xs, 0 => 1 :: xs
  | x :: xs, S k => x :: replace_with_one k xs
  end.

Definition zero_left_half (l : list nat) : list nat :=
  repeat 0 left_half_length ++ skipn left_half_length l.

(** ** Instruction vocabulary *)

Inductive instruction :=
| WriteOne (idx : nat)
| ClaimLeftZero
| Verify.

Definition program := list instruction.

(** ** Turing interpreter semantics *)

Definition step_turing (i : instruction) (σ : state) : state :=
  match i with
  | WriteOne idx => {| tape := replace_with_one idx σ.(tape);
                       mu_cost := σ.(mu_cost) |}
  | ClaimLeftZero => σ (* The classical machine cannot realise the claim. *)
  | Verify => σ
  end.

Fixpoint run_turing (p : program) (σ : state) : state :=
  match p with
  | [] => σ
  | i :: ps => run_turing ps (step_turing i σ)
  end.

(** ** Thiele interpreter semantics *)

Definition mu_claim_cost : nat := 1.

Definition step_thiele (i : instruction) (σ : state) : state :=
  match i with
  | WriteOne idx => {| tape := replace_with_one idx σ.(tape);
                       mu_cost := σ.(mu_cost) |}
  | ClaimLeftZero => {| tape := zero_left_half σ.(tape);
                        mu_cost := σ.(mu_cost) + mu_claim_cost |}
  | Verify => σ
  end.

Fixpoint run_thiele (p : program) (σ : state) : state :=
  match p with
  | [] => σ
  | i :: ps => run_thiele ps (step_thiele i σ)
  end.

(** ** The geometric program *)

Definition geometric_program : program := [ClaimLeftZero; Verify].

Lemma run_turing_geometric :
  run_turing geometric_program initial_state = initial_state.
Proof.
  reflexivity.
Qed.

Lemma initial_not_target : initial_tape <> target_tape.
Proof.
  discriminate.
Qed.

Theorem turing_cannot_solve :
  tape (run_turing geometric_program initial_state) <> target_tape.
Proof.
  rewrite run_turing_geometric.
  exact initial_not_target.
Qed.

Lemma zero_left_half_target : zero_left_half initial_tape = target_tape.
Proof.
  reflexivity.
Qed.

Lemma run_thiele_geometric :
  run_thiele geometric_program initial_state =
    {| tape := target_tape; mu_cost := mu_claim_cost |}.
Proof.
  reflexivity.
Qed.

Theorem thiele_can_solve :
  tape (run_thiele geometric_program initial_state) = target_tape /\
  mu_cost (run_thiele geometric_program initial_state) = mu_claim_cost.
Proof.
  rewrite run_thiele_geometric.
  split; reflexivity.
Qed.

End ToyThiele.
