Require Import List.
Require Import Bool.
Require Import Nat.

Import ListNotations.

Module VerifiedGraphSolver.

(** * Verified Graph Colouring Microcosm

    This file instantiates a nine-node graph colouring problem that mirrors the
    `triadic_cascade` laboratory from the Python demo.  Two solvers are
    implemented:
    - a classical degree-ordered backtracking search that counts arithmetic
      branch attempts, and
    - a Thiele-style solver that spends µ-bits on anchor claims and congruence
      feasibility queries before assigning the unique colouring with zero
      residual search.

    Theorems at the bottom of the file state the exact costs recovered by each
    solver, providing a "Cessna"-scale artifact that bridges the toy
    microcosm and the full VM experiment.
*)

(** ** Basic graph definitions *)

Inductive colour := Red | Green | Blue.

Definition colour_eqb (c1 c2 : colour) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Green, Green => true
  | Blue, Blue => true
  | _, _ => false
  end.

Definition palette : list colour := [Red; Green; Blue].

Definition nodes : list nat := [0;1;2;3;4;5;6;7;8].

Definition neighbours (n : nat) : list nat :=
  match n with
  | 0 => [1;2;4;5]
  | 1 => [0;2;3;5]
  | 2 => [0;1;3;4]
  | 3 => [1;2;7;8]
  | 4 => [0;2;6;8]
  | 5 => [0;1;6;7]
  | 6 => [4;5]
  | 7 => [3;5]
  | 8 => [3;4]
  | _ => []
  end.

Definition partial := nat -> option colour.

Definition empty_partial : partial := fun _ => None.

Definition assign (σ : partial) (node : nat) (c : colour) : partial :=
  fun n => if Nat.eqb n node then Some c else σ n.

Definition lookup (σ : partial) (node : nat) : option colour := σ node.

Definition conflict (node : nat) (c : colour) (σ : partial) : bool :=
  existsb
    (fun nbr =>
       match lookup σ nbr with
       | Some c' => colour_eqb c c'
       | None => false
       end)
    (neighbours node).

(** ** Classical backtracking solver *)

Fixpoint backtrack (order : list nat) (σ : partial) (count : nat)
  {struct order} : option (nat * partial) :=
  match order with
  | [] => Some (count, σ)
  | node :: rest =>
      let fix try_palette (pal : list colour) (σ' : partial) (count' : nat)
          {struct pal} : option (nat * partial) :=
          match pal with
          | [] => None
          | c :: cs =>
              let count'' := S count' in
              if conflict node c σ' then
                try_palette cs σ' count''
              else
                match backtrack rest (assign σ' node c) count'' with
                | Some res => Some res
                | None => try_palette cs σ' count''
                end
          end in
      try_palette palette σ count
  end.

Definition classical_run : option (nat * partial) :=
  backtrack nodes empty_partial 0.

Definition canonical_partial : partial :=
  assign
    (assign
      (assign
        (assign
          (assign
            (assign
              (assign
                (assign (assign empty_partial 0 Red) 1 Green) 2 Blue) 3 Red) 4 Green)
            5 Blue) 6 Red) 7 Green) 8 Blue.

(** ** Thiele-style solver with µ-bit accounting *)

Record thiele_state := {
  state_partial : partial;
  state_mu : nat;
  state_arith : nat
}.

Definition thiele_empty : thiele_state :=
  {| state_partial := empty_partial; state_mu := 0; state_arith := 0 |}.

Definition claim (σ : thiele_state) (node : nat) (c : colour) : thiele_state :=
  {| state_partial := assign σ.(state_partial) node c;
     state_mu := S σ.(state_mu);
     state_arith := σ.(state_arith) |}.

Definition assign_state (σ : thiele_state) (node : nat) (c : colour)
  : thiele_state :=
  {| state_partial := assign σ.(state_partial) node c;
     state_mu := σ.(state_mu);
     state_arith := σ.(state_arith) |}.

Definition query_colour (σ : thiele_state) (node : nat) (c : colour)
  : bool * thiele_state :=
  let possible := negb (conflict node c σ.(state_partial)) in
  (possible,
   {| state_partial := σ.(state_partial);
      state_mu := S σ.(state_mu);
      state_arith := σ.(state_arith) |}).

Fixpoint query_palette
  (σ : thiele_state) (pal : list colour) (node : nat)
  {struct pal} : list colour * thiele_state :=
  match pal with
  | [] => ([], σ)
  | c :: cs =>
      let '(ok, σ1) := query_colour σ node c in
      let '(rest, σ2) := query_palette σ1 cs node in
      if ok then (c :: rest, σ2) else (rest, σ2)
  end.

Definition propagate_node (σ : thiele_state) (node : nat) : thiele_state :=
  let '(options, σ1) := query_palette σ palette node in
  match options with
  | [c] => assign_state σ1 node c
  | _ => σ1
  end.

Definition thiele_run : thiele_state :=
  let σ1 := claim thiele_empty 0 Red in
  let σ2 := claim σ1 1 Green in
  fold_left propagate_node [2;3;4;5;6;7;8] σ2.

(** ** Verified outcomes *)

Lemma classical_is_slow :
  classical_run = Some (18, canonical_partial).
Proof.
  unfold classical_run.
  vm_compute.
  reflexivity.
Qed.

Lemma thiele_is_fast :
  thiele_run =
    {| state_partial := canonical_partial;
       state_mu := 23;
       state_arith := 0 |}.
Proof.
  unfold thiele_run.
  vm_compute.
  reflexivity.
Qed.

End VerifiedGraphSolver.
