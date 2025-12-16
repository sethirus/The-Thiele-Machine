From Coq Require Import List String Ascii ZArith Bool QArith PArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope Q_scope.

From ThieleMachine Require Import BellInequality.

(** Receipt-layer CHSH semantics.

    This module defines a *canonical decoding* from receipt metadata strings into
    CHSH trials, plus simple tally/probability helpers.

    Important: this is receipt-only. It does not interpret the kernel CSR-based
    certification channel. The kernel channel is handled in coq/kernel/*. *)

Record Trial : Type := {
  t_x : Bit;
  t_y : Bit;
  t_a : Bit;
  t_b : Bit
}.

Definition bit_eqb (x y : Bit) : bool :=
  match x, y with
  | B0, B0 => true
  | B1, B1 => true
  | _, _ => false
  end.

Definition bit_of_bool (b : bool) : Bit := if b then B1 else B0.

Definition bit_of_char01 (c : ascii) : option Bit :=
  if Ascii.eqb c "0"%char then Some B0
  else if Ascii.eqb c "1"%char then Some B1
  else None.

Definition trial_of_payload4 (payload : string) : option Trial :=
  match payload with
  | String.String x (String.String y (String.String a (String.String b String.EmptyString))) =>
        match bit_of_char01 x, bit_of_char01 y, bit_of_char01 a, bit_of_char01 b with
        | Some bx, Some by0, Some ba0, Some bb0 =>
          Some {| t_x := bx; t_y := by0; t_a := ba0; t_b := bb0 |}
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition trial_of_metadata (meta : string) : option Trial :=
  let has_len := Nat.eqb (String.length meta) 9 in
  let has_prefix := String.eqb (String.substring 0 5 meta) "CHSH_" in
  if (has_len && has_prefix)%bool then
    trial_of_payload4 (String.substring 5 4 meta)
  else None.

Fixpoint trials_of_metadata_list (metas : list string) : list Trial :=
  match metas with
  | [] => []
  | m :: ms =>
      match trial_of_metadata m with
      | Some t => t :: trials_of_metadata_list ms
      | None => trials_of_metadata_list ms
      end
  end.

Definition trial_eqb (t1 t2 : Trial) : bool :=
  bit_eqb t1.(t_x) t2.(t_x)
    && bit_eqb t1.(t_y) t2.(t_y)
    && bit_eqb t1.(t_a) t2.(t_a)
    && bit_eqb t1.(t_b) t2.(t_b).

Fixpoint count_trial (t : Trial) (ts : list Trial) : nat :=
  match ts with
  | [] => 0
  | u :: us => (if trial_eqb t u then 1 else 0)%nat + count_trial t us
  end.

Definition total_for_setting (x y : Bit) (ts : list Trial) : nat :=
  (
    count_trial {| t_x := x; t_y := y; t_a := B0; t_b := B0 |} ts +
    count_trial {| t_x := x; t_y := y; t_a := B0; t_b := B1 |} ts +
    count_trial {| t_x := x; t_y := y; t_a := B1; t_b := B0 |} ts +
    count_trial {| t_x := x; t_y := y; t_a := B1; t_b := B1 |} ts
  )%nat.

Definition p_from_trials (ts : list Trial) (a b x y : Bit) : Q :=
  let num := Z.of_nat (count_trial {| t_x := x; t_y := y; t_a := a; t_b := b |} ts) in
  match total_for_setting x y ts with
  | O => 0
  | Datatypes.S den' => (num # (Pos.of_succ_nat den'))
  end.

Definition raw_box_of_trials (ts : list Trial) : (Bit -> Bit -> Bit -> Bit -> Q) :=
  fun a b x y => p_from_trials ts a b x y.

(** For artefact pinning we often want a full [Box]. Constructing [Box] requires
    no-signaling, which is not derivable from finite samples without additional
    assumptions. For a *fixed*, deterministically generated trace we can prove it
    by computation in a witness module.

    This file intentionally stops at [raw_box_of_trials]. *)

Definition chsh_of_trials (ts : list Trial) : Q :=
  let Braw := raw_box_of_trials ts in
  (* Turn raw probabilities into a Box-shaped record by reusing BellInequality's
     definitions via a small adapter (without proofs). We keep it raw here. *)
  (sum_bit2 (fun a b => (inject_Z ((sgn a * sgn b)%Z)) * Braw a b B1 B1)) +
   (sum_bit2 (fun a b => (inject_Z ((sgn a * sgn b)%Z)) * Braw a b B1 B0)) +
   (sum_bit2 (fun a b => (inject_Z ((sgn a * sgn b)%Z)) * Braw a b B0 B1)) -
   (sum_bit2 (fun a b => (inject_Z ((sgn a * sgn b)%Z)) * Braw a b B0 B0)).

(* Export a few names for consumers. *)

