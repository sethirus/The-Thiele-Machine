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

(** ** μ-spec v2.0 helpers *)

Definition node_token_length (node : nat) : nat :=
  match node with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => 1
  | _ => 1
  end.

Definition colour_token_length (c : colour) : nat :=
  match c with
  | Red => 3
  | Green => 5
  | Blue => 4
  end.

Definition canonical_length (lengths : list nat) : nat :=
  match lengths with
  | [] => 0
  | _ => fold_left Nat.add lengths 0 + Nat.pred (length lengths)
  end.

Definition question_bits_from_lengths (lengths : list nat) : nat :=
  8 * canonical_length lengths.

Definition claim_question_bits (node : nat) (c : colour) : nat :=
  question_bits_from_lengths
    [1; 5; 4; node_token_length node; colour_token_length c; 1].

Definition oracle_question_bits (node : nat) : nat :=
  question_bits_from_lengths [1; 6; 4; node_token_length node; 1].

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
  state_mu_question : nat;
  state_mu_ratios : list (nat * nat);
  state_arith : nat
}.

Definition thiele_empty : thiele_state :=
  {| state_partial := empty_partial;
     state_mu_question := 0;
     state_mu_ratios := [];
     state_arith := 0 |}.

Definition with_partial (σ : thiele_state) (σp : partial) : thiele_state :=
  {| state_partial := σp;
     state_mu_question := σ.(state_mu_question);
     state_mu_ratios := σ.(state_mu_ratios);
     state_arith := σ.(state_arith) |}.

Definition record_event (σ : thiele_state) (question_bits before after : nat)
  : thiele_state :=
  {| state_partial := σ.(state_partial);
     state_mu_question := σ.(state_mu_question) + question_bits;
     state_mu_ratios := (before, after) :: σ.(state_mu_ratios);
     state_arith := σ.(state_arith) |}.

Definition claim (σ : thiele_state) (node : nat) (c : colour) : thiele_state :=
  let σ1 := record_event σ (claim_question_bits node c) 3 1 in
  with_partial σ1 (assign σ.(state_partial) node c).

Definition assign_state (σ : thiele_state) (node : nat) (c : colour)
  : thiele_state :=
  with_partial σ (assign σ.(state_partial) node c).

Definition node_options (σ : thiele_state) (node : nat) : list colour :=
  filter (fun c => negb (conflict node c σ.(state_partial))) palette.

Definition propagate_node (σ : thiele_state) (node : nat) : thiele_state :=
  let options := node_options σ node in
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  let after := Nat.max 1 (length options) in
  let σ1 := record_event σ (oracle_question_bits node) 3 after in
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

Definition mu_question_total : nat :=
  fold_left Nat.add
    ([claim_question_bits 0 Red; claim_question_bits 1 Green] ++
     map oracle_question_bits [2;3;4;5;6;7;8]) 0.

Definition mu_ratio_list : list (nat * nat) := repeat (3, 1) 9.

Definition calculate_formal_mu_cost : nat * list (nat * nat) :=
  (mu_question_total, mu_ratio_list).

Definition expected_thiele_state : thiele_state :=
  {| state_partial := canonical_partial;
     state_mu_question := mu_question_total;
     state_mu_ratios := mu_ratio_list;
     state_arith := 0 |}.

Lemma thiele_is_fast : thiele_run = expected_thiele_state.
Proof.
  unfold thiele_run, expected_thiele_state.
  vm_compute.
  reflexivity.
Qed.

Lemma thiele_pays_the_cost :
  (state_mu_question thiele_run, state_mu_ratios thiele_run) =
  calculate_formal_mu_cost.
Proof.
  unfold calculate_formal_mu_cost, thiele_run.
  vm_compute.
  reflexivity.
Qed.

End VerifiedGraphSolver.
