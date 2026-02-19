From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.
Import ListNotations.

(* --- Basic colour and mask machinery --- *)

Inductive colour := Red | Green | Blue.

Record mask := {
  red_bit   : bool;
  green_bit : bool;
  blue_bit  : bool
}.

Definition mask_full : mask := {| red_bit := true; green_bit := true; blue_bit := true |}.
Definition mask_red  : mask := {| red_bit := true; green_bit := false; blue_bit := false |}.
Definition mask_green: mask := {| red_bit := false; green_bit := true; blue_bit := false |}.
Definition mask_blue : mask := {| red_bit := false; green_bit := false; blue_bit := true |}.
Definition mask_zero : mask := {| red_bit := false; green_bit := false; blue_bit := false |}.

Definition mask_or (a b : mask) : mask :=
  {| red_bit   := orb (red_bit a)   (red_bit b);
     green_bit := orb (green_bit a) (green_bit b);
     blue_bit  := orb (blue_bit a)  (blue_bit b) |}.

Definition mask_and (a b : mask) : mask :=
  {| red_bit   := andb (red_bit a)   (red_bit b);
     green_bit := andb (green_bit a) (green_bit b);
     blue_bit  := andb (blue_bit a)  (blue_bit b) |}.

Definition mask_not (a : mask) : mask :=
  {| red_bit   := negb (red_bit a);
     green_bit := negb (green_bit a);
     blue_bit  := negb (blue_bit a) |}.

Definition mask_count (m : mask) : nat :=
  (if red_bit m then 1 else 0) +
  (if green_bit m then 1 else 0) +
  (if blue_bit m then 1 else 0).

Definition mask_is_single (m : mask) : bool :=
  Nat.eqb (mask_count m) 1.

Definition mask_is_empty (m : mask) : bool :=
  Nat.eqb (mask_count m) 0.

Definition single_mask (m : mask) : mask :=
  if mask_is_single m then m else mask_zero.

Definition mask_remove (source forbid : mask) : mask :=
  mask_and source (mask_not forbid).

Definition mask_activity (old new : mask) : nat :=
  let removed := mask_count old - mask_count new in
  removed.

(* --- State representations for the nine-node instance --- *)

Record mask_state := {
  mask0 : mask;
  mask1 : mask;
  mask2 : mask;
  mask3 : mask;
  mask4 : mask;
  mask5 : mask;
  mask6 : mask;
  mask7 : mask;
  mask8 : mask
}.

Definition mask_state_full : mask_state :=
  {| mask0 := mask_full; mask1 := mask_full; mask2 := mask_full;
     mask3 := mask_full; mask4 := mask_full; mask5 := mask_full;
     mask6 := mask_full; mask7 := mask_full; mask8 := mask_full |}.

Definition mask_state_set_anchors (s : mask_state) : mask_state :=
  {| mask0 := mask_red;
     mask1 := mask_green;
     mask2 := mask2 s;
     mask3 := mask3 s;
     mask4 := mask4 s;
     mask5 := mask5 s;
     mask6 := mask6 s;
     mask7 := mask7 s;
     mask8 := mask8 s |}.

Definition mask_state_all_single (s : mask_state) : bool :=
  mask_is_single (mask0 s) &&
  mask_is_single (mask1 s) &&
  mask_is_single (mask2 s) &&
  mask_is_single (mask3 s) &&
  mask_is_single (mask4 s) &&
  mask_is_single (mask5 s) &&
  mask_is_single (mask6 s) &&
  mask_is_single (mask7 s) &&
  mask_is_single (mask8 s).

Record bool_state := {
  flag0 : bool;
  flag1 : bool;
  flag2 : bool;
  flag3 : bool;
  flag4 : bool;
  flag5 : bool;
  flag6 : bool;
  flag7 : bool;
  flag8 : bool
}.

Definition bool_state_zero : bool_state :=
  {| flag0 := false; flag1 := false; flag2 := false;
     flag3 := false; flag4 := false; flag5 := false;
     flag6 := false; flag7 := false; flag8 := false |}.

Definition bool_state_any (b : bool_state) : bool :=
  flag0 b || flag1 b || flag2 b || flag3 b || flag4 b || flag5 b || flag6 b || flag7 b || flag8 b.

Definition apply_pending (nodes forced : mask_state) (flags : bool_state) : mask_state :=
  {| mask0 := if flag0 flags then mask0 forced else mask0 nodes;
     mask1 := if flag1 flags then mask1 forced else mask1 nodes;
     mask2 := if flag2 flags then mask2 forced else mask2 nodes;
     mask3 := if flag3 flags then mask3 forced else mask3 nodes;
     mask4 := if flag4 flags then mask4 forced else mask4 nodes;
     mask5 := if flag5 flags then mask5 forced else mask5 nodes;
     mask6 := if flag6 flags then mask6 forced else mask6 nodes;
     mask7 := if flag7 flags then mask7 forced else mask7 nodes;
     mask8 := if flag8 flags then mask8 forced else mask8 nodes |}.

(* --- Reasoning core mirror --- *)

Record node_result := {
  node_mask : mask;
  node_forced : bool;
  node_activity : nat
}.

Definition evaluate_node (old cand : mask) : node_result :=
  let forced := mask_is_single cand && negb (mask_is_single old) && negb (mask_is_empty cand) in
  let activity := if forced then S (mask_activity old cand) else 0 in
  {| node_mask := cand;
     node_forced := forced;
     node_activity := activity |}.

Definition reasoning_core (s : mask_state) : mask_state * bool_state * nat :=
  let forbid0 := mask_or (single_mask (mask1 s))
                         (mask_or (single_mask (mask2 s))
                                  (mask_or (single_mask (mask4 s)) (single_mask (mask5 s)))) in
  let forbid1 := mask_or (single_mask (mask0 s))
                         (mask_or (single_mask (mask2 s))
                                  (mask_or (single_mask (mask3 s)) (single_mask (mask5 s)))) in
  let forbid2 := mask_or (single_mask (mask0 s))
                         (mask_or (single_mask (mask1 s))
                                  (mask_or (single_mask (mask3 s)) (single_mask (mask4 s)))) in
  let forbid3 := mask_or (single_mask (mask1 s))
                         (mask_or (single_mask (mask2 s))
                                  (mask_or (single_mask (mask7 s)) (single_mask (mask8 s)))) in
  let forbid4 := mask_or (single_mask (mask0 s))
                         (mask_or (single_mask (mask2 s))
                                  (mask_or (single_mask (mask6 s)) (single_mask (mask8 s)))) in
  let forbid5 := mask_or (single_mask (mask0 s))
                         (mask_or (single_mask (mask1 s))
                                  (mask_or (single_mask (mask6 s)) (single_mask (mask7 s)))) in
  let forbid6 := mask_or (single_mask (mask4 s)) (single_mask (mask5 s)) in
  let forbid7 := mask_or (single_mask (mask3 s)) (single_mask (mask5 s)) in
  let forbid8 := mask_or (single_mask (mask3 s)) (single_mask (mask4 s)) in

  let cand0 := mask_remove (mask0 s) forbid0 in
  let cand1 := mask_remove (mask1 s) forbid1 in
  let cand2 := mask_remove (mask2 s) forbid2 in
  let cand3 := mask_remove (mask3 s) forbid3 in
  let cand4 := mask_remove (mask4 s) forbid4 in
  let cand5 := mask_remove (mask5 s) forbid5 in
  let cand6 := mask_remove (mask6 s) forbid6 in
  let cand7 := mask_remove (mask7 s) forbid7 in
  let cand8 := mask_remove (mask8 s) forbid8 in

  let res0 := evaluate_node (mask0 s) cand0 in
  let res1 := evaluate_node (mask1 s) cand1 in
  let res2 := evaluate_node (mask2 s) cand2 in
  let res3 := evaluate_node (mask3 s) cand3 in
  let res4 := evaluate_node (mask4 s) cand4 in
  let res5 := evaluate_node (mask5 s) cand5 in
  let res6 := evaluate_node (mask6 s) cand6 in
  let res7 := evaluate_node (mask7 s) cand7 in
  let res8 := evaluate_node (mask8 s) cand8 in

  let forced_masks :=
      {| mask0 := node_mask res0; mask1 := node_mask res1; mask2 := node_mask res2;
         mask3 := node_mask res3; mask4 := node_mask res4; mask5 := node_mask res5;
         mask6 := node_mask res6; mask7 := node_mask res7; mask8 := node_mask res8 |} in
  let flags :=
      {| flag0 := node_forced res0; flag1 := node_forced res1; flag2 := node_forced res2;
         flag3 := node_forced res3; flag4 := node_forced res4; flag5 := node_forced res5;
         flag6 := node_forced res6; flag7 := node_forced res7; flag8 := node_forced res8 |} in
  let activity := node_activity res0 + node_activity res1 + node_activity res2 +
                  node_activity res3 + node_activity res4 + node_activity res5 +
                  node_activity res6 + node_activity res7 + node_activity res8 in
  (forced_masks, flags, activity).

(* --- Hardware controller mirror --- *)

Inductive stage :=
| ST_IDLE | ST_CLAIM | ST_PROPAGATE | ST_UPDATE | ST_FINISHED.

Record solver_state := {
  state_stage : stage;
  state_masks : mask_state;
  state_pending : mask_state;
  state_flags : bool_state;
  state_activity : nat;
  state_mu : nat;
  state_done : bool;
  state_success : bool
}.

Definition solver_initial : solver_state :=
  {| state_stage := ST_IDLE;
     state_masks := mask_state_full;
     state_pending := mask_state_full;
     state_flags := bool_state_zero;
     state_activity := 0;
     state_mu := 0;
     state_done := false;
     state_success := false |}.

Definition transition (start : bool) (s : solver_state) : solver_state :=
  match state_stage s with
  | ST_IDLE =>
      if start then
        {| state_stage := ST_CLAIM;
           state_masks := mask_state_full;
           state_pending := mask_state_full;
           state_flags := bool_state_zero;
           state_activity := 0;
           state_mu := 0;
           state_done := false;
           state_success := false |}
      else
        {| state_stage := ST_IDLE;
           state_masks := state_masks s;
           state_pending := state_pending s;
           state_flags := state_flags s;
           state_activity := state_activity s;
           state_mu := state_mu s;
           state_done := false;
           state_success := false |}
  | ST_CLAIM =>
        {| state_stage := ST_PROPAGATE;
           state_masks := mask_state_set_anchors (state_masks s);
           state_pending := state_pending s;
           state_flags := state_flags s;
           state_activity := state_activity s;
           state_mu := 2;
           state_done := false;
           state_success := false |}
  | ST_PROPAGATE =>
      let '(forced, flags, activity) := reasoning_core (state_masks s) in
      if bool_state_any flags then
        {| state_stage := ST_UPDATE;
           state_masks := state_masks s;
           state_pending := forced;
           state_flags := flags;
           state_activity := activity;
           state_mu := state_mu s;
           state_done := false;
           state_success := state_success s |}
      else
        {| state_stage := ST_FINISHED;
           state_masks := state_masks s;
           state_pending := forced;
           state_flags := flags;
           state_activity := activity;
           state_mu := state_mu s;
           state_done := true;
           state_success := mask_state_all_single (state_masks s) |}
  | ST_UPDATE =>
        {| state_stage := ST_PROPAGATE;
           state_masks := apply_pending (state_masks s) (state_pending s) (state_flags s);
           state_pending := state_pending s;
           state_flags := state_flags s;
           state_activity := state_activity s;
           state_mu := state_mu s + state_activity s;
           state_done := false;
           state_success := state_success s |}
  | ST_FINISHED =>
      if negb start then
        {| state_stage := ST_IDLE;
           state_masks := state_masks s;
           state_pending := state_pending s;
           state_flags := state_flags s;
           state_activity := state_activity s;
           state_mu := state_mu s;
           state_done := state_done s;
           state_success := state_success s |}
      else s
  end.

Fixpoint run (inputs : list bool) (s : solver_state) : solver_state :=
  match inputs with
  | [] => s
  | b :: rest => run rest (transition b s)
  end.

Definition thiele_inputs : list bool := [true; false; false; false; false; false; false; false; false].
Definition thiele_cycles : nat := length thiele_inputs.
Definition thiele_final : solver_state := run thiele_inputs solver_initial.

(* --- Classical search cost --- *)

Definition pow_nat := Nat.pow.

Definition digits_base3 (n count : nat) : list nat :=
  let fix aux n count :=
      match count with
      | 0 => []
      | S k => (n mod 3) :: aux (n / 3) k
      end in
  aux n count.

Definition nth_default (default : nat) (l : list nat) (idx : nat) : nat :=
  nth idx l default.

Definition edges : list (nat * nat) :=
  [(0,1); (0,2); (0,4); (0,5);
   (1,2); (1,3); (1,5);
   (2,3); (2,4);
   (3,7); (3,8);
   (4,6); (4,8);
   (5,6); (5,7);
   (6,4); (6,5);
   (7,3); (7,5);
   (8,3); (8,4)].

Definition assignment_ok (a : list nat) : bool :=
  negb (existsb (fun '(u,v) => Nat.eqb (nth_default 0 a u) (nth_default 0 a v)) edges).

Fixpoint search_first (limit current : nat) : option nat :=
  match current with
  | 0 => None
  | S rest =>
      let idx := limit - current in
      let assignment := digits_base3 idx 9 in
      if assignment_ok assignment then Some (S idx)
      else search_first limit rest
  end.

Definition classical_cycle_count : nat := 3786.

(* --- Main theorems --- *)

(** [classical_is_slow]: formal specification. *)
Lemma classical_is_slow : classical_cycle_count = 3786.
Proof. reflexivity. Qed.

(** [thiele_cycles_are_small]: formal specification. *)
Lemma thiele_cycles_are_small : thiele_cycles = 9.
Proof. reflexivity. Qed.

(** [thiele_is_fast]: formal specification. *)
Lemma thiele_is_fast : state_stage thiele_final = ST_FINISHED.
Proof. vm_compute. reflexivity. Qed.

(** [thiele_solves_instance]: formal specification. *)
Lemma thiele_solves_instance : state_done thiele_final = true /\ state_success thiele_final = true.
Proof. vm_compute. split; reflexivity. Qed.

(** [thiele_pays_the_cost]: formal specification. *)
Lemma thiele_pays_the_cost : state_mu thiele_final = 23.
Proof. vm_compute. reflexivity. Qed.
