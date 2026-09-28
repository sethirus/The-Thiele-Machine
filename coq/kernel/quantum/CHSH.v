(** This file extracts CHSH trial records and proves a finite deterministic bound.
    [CHSHExtraction.v] handles the separate trace-to-trial extraction path.
    Here a [Trial] list supplies the settings and outcome bits, the code computes the four correlators, and the proof checks all 16 deterministic response tables.
    The result is a bound for that finite response-table model; it is not a statistical confidence theorem or a physical Bell-test theorem. *)

From Coq Require Import List Bool Arith.PeanoNat ZArith QArith Lia.
Require Import Coq.QArith.Qabs.
Import ListNotations.
Open Scope Q_scope.

From Kernel Require Import VMStep.

(* SCOPE NOTE: foundation connectivity, bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

Module KernelCHSH.

Import VMStep.VMStep.

(** [Trial] stores two setting bits and two outcome bits extracted from a CHSH instruction.
    This record does not authenticate the source instruction or prove a physical interpretation; receipt-integrity claims belong to the receipt layer. *)
Record Trial : Type := {
  t_x : nat;
  t_y : nat;
  t_a : nat;
  t_b : nat;
}.

(** [is_trial_instr] keeps an [instr_chsh_trial] only when its four data fields pass [chsh_bits_ok].
    Other instructions and malformed trial records map to [None]. *)
Definition is_trial_instr (i : vm_instruction) : option Trial :=
  match i with
  | instr_chsh_trial x y a b _ =>
      if chsh_bits_ok x y a b then Some {| t_x := x; t_y := y; t_a := a; t_b := b |}
      else None
  | _ => None
  end.

(** [trials_of_receipts] recursively filters a trace to the valid trial records returned by [is_trial_instr].
    The recursion is structural on the instruction list, so the operation makes one pass and preserves the order of accepted trials. *)
Fixpoint trials_of_receipts (rs : list vm_instruction) : list Trial :=
  match rs with
  | [] => []
  | i :: tl =>
      match is_trial_instr i with
      | Some t => t :: trials_of_receipts tl
      | None => trials_of_receipts tl
      end
  end.

(** [sign_z] maps the accepted outcome bit [0] to [-1] and [1] to [+1].
    Other natural numbers also map to [-1] by definition, although the parser rejects them as trial fields. *)
Definition sign_z (bit : nat) : Z :=
  if Nat.eqb bit 1 then 1%Z else (-1)%Z.

(** [trial_value_z] is the product of the two signed outcome values for one trial.
    The CHSH correlator code averages this contribution over trials with matching settings. *)
Definition trial_value_z (t : Trial) : Z :=
  (sign_z t.(t_a) * sign_z t.(t_b))%Z.

(** [count_setting] counts the trials whose two setting fields equal the supplied pair.
    It makes one structural pass over the list and returns zero when no record matches. *)
Fixpoint count_setting (x y : nat) (ts : list Trial) : nat :=
  match ts with
  | [] => 0
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then 1 else 0)
        + count_setting x y tl
  end.

(** [sum_setting_z] sums the signed outcome products for trials with the supplied setting pair.
    It uses the same structural scan as [count_setting], returning zero when no record matches. *)
Fixpoint sum_setting_z (x y : nat) (ts : list Trial) : Z :=
  match ts with
  | [] => 0%Z
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then trial_value_z t else 0%Z)
        + sum_setting_z x y tl
  end.

(** [expectation] divides [sum_setting_z] by [count_setting] for one setting pair.
    The empty-setting case returns rational zero by convention; this definition does not supply a statistical confidence interval. *)
Definition expectation (x y : nat) (ts : list Trial) : Q :=
  match count_setting x y ts with
  | 0%nat => 0
  | S n' => (sum_setting_z x y ts) # (Pos.of_succ_nat n')
  end.

(** [chsh] combines the four rational correlators in the repository's chosen sign convention.
    The later local-strategy theorem supplies the finite deterministic bound; this definition does not certify an experiment or establish a statistical or physical conclusion. *)
Definition chsh (ts : list Trial) : Q :=
  expectation 1 1 ts + expectation 1 0 ts + expectation 0 1 ts - expectation 0 0 ts.

(** ------------------------------------------------------------------------- *)
(** The local-strategy section packages one deterministic response table as four bits and proves the bound for the corresponding four-setting dataset. *)

(** [LocalStrategy] is a four-field response table with one outcome for each setting at each side.
    The fields are natural numbers, and [local_bits_ok] is the separate predicate restricting them to bits.
    The local-bound theorem enumerates the 16 response tables satisfying that predicate. *)
Record LocalStrategy : Type := {
  a0 : nat;
  a1 : nat;
  b0 : nat;
  b1 : nat;
}.

(** [trial_of_local] looks up the two responses in [s] and returns the corresponding trial record.
    For fixed [s], [x], and [y], the function is deterministic. *)
Definition trial_of_local (s : LocalStrategy) (x y : nat) : Trial :=
  {| t_x := x;
     t_y := y;
     t_a := if Nat.eqb x 0 then s.(a0) else s.(a1);
     t_b := if Nat.eqb y 0 then s.(b0) else s.(b1) |}.

(** [trials_of_local] builds the four records for settings [(0,0)], [(0,1)], [(1,0)], and [(1,1)].
    This is the finite dataset used when the deterministic response-table theorem computes the CHSH value. *)
Definition trials_of_local (s : LocalStrategy) : list Trial :=
  [ trial_of_local s 0 0;
    trial_of_local s 0 1;
    trial_of_local s 1 0;
    trial_of_local s 1 1 ].

(** [local_bits_ok] requires all four response-table fields to satisfy [is_bit]. *)
Definition local_bits_ok (s : LocalStrategy) : Prop :=
  is_bit s.(a0) = true /\ is_bit s.(a1) = true /\
  is_bit s.(b0) = true /\ is_bit s.(b1) = true.

(** [is_bit_true_cases] turns a successful [is_bit] check into the two explicit natural-number cases used by the finite proof. *)
Lemma is_bit_true_cases :
  forall n, is_bit n = true -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n H.
  (* Step 1: Unfold is_bit *)
  unfold is_bit in H.
  (* Step 2: Case analysis on n *)
  destruct n as [|n].
  - (* Case n = 0 *)
    left. reflexivity.
  - (* Case n = S n *)
    destruct n as [|n].
    + (* Subcase n = 1 *)
      right. reflexivity.
    + (* Subcase n ≥ 2: Contradicts is_bit = true *)
      simpl in H. discriminate.
Qed.

(** [count_setting_trials_of_local] proves that each of the four valid setting pairs occurs once in [trials_of_local]. *)
Lemma count_setting_trials_of_local :
  forall s (x y : nat),
    (x = 0%nat \/ x = 1%nat) ->
    (y = 0%nat \/ y = 1%nat) ->
    count_setting x y (trials_of_local s) = 1%nat.
Proof.
  intros s x y Hx Hy.
  (* Step 1: Case split on all combinations of (x,y) ∈ {0,1} × {0,1} *)
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy]; subst;
  (* Step 2: Compute trials_of_local, count_setting explicitly *)
  vm_compute; reflexivity.
Qed.

(** [expectation_trials_of_local] rewrites the rational expectation using the one-record count proved above. *)
Lemma expectation_trials_of_local :
  forall s (x y : nat),
    (x = 0%nat \/ x = 1%nat) ->
    (y = 0%nat \/ y = 1%nat) ->
    expectation x y (trials_of_local s) = (sum_setting_z x y (trials_of_local s))#1.
Proof.
  intros s x y Hx Hy.
  (* Step 1: Unfold expectation *)
  unfold expectation.
  (* Step 2: Rewrite count to 1 using previous lemma *)
  rewrite (count_setting_trials_of_local s x y Hx Hy).
  (* Step 3: Simplify match: S 0 case *)
  simpl.
  reflexivity.
Qed.

(** The next theorem proves the finite deterministic CHSH bound by enumerating the valid response tables. *)

(** [chsh_local_z] is the closed-form integer CHSH expression for one response table. *)
Definition chsh_local_z (s : LocalStrategy) : Z :=
  let A0 := sign_z s.(a0) in
  let A1 := sign_z s.(a1) in
  let B0 := sign_z s.(b0) in
  let B1 := sign_z s.(b1) in
  (A1 * B1 + A1 * B0 + A0 * B1 - A0 * B0)%Z.

(** [local_strategy_chsh_between_neg2_2] proves the stated integer interval for every response table satisfying [local_bits_ok].
    The proof reduces each field to zero or one and evaluates the resulting 16 cases.
    Connecting this finite model to sampled experiments requires assumptions that are outside this theorem. *)
Theorem local_strategy_chsh_between_neg2_2 :
  forall s,
    local_bits_ok s ->
    (-2 <= chsh_local_z s <= 2)%Z.
Proof.
  intros [A0 A1 B0 B1] Hbits.
  (* Step 1: Extract bit validity for each field *)
  unfold local_bits_ok in Hbits.
  destruct Hbits as [Ha0 [Ha1 [Hb0 Hb1]]].

  (* Step 2: Reduce each response bit to concrete 0/1 cases *)
  destruct (is_bit_true_cases A0 Ha0) as [HA0|HA0];
  destruct (is_bit_true_cases A1 Ha1) as [HA1|HA1];
  destruct (is_bit_true_cases B0 Hb0) as [HB0|HB0];
  destruct (is_bit_true_cases B1 Hb1) as [HB1|HB1];

  (* Step 3: Compute CHSH value for each case (all 16 combinations) *)
  (* Avoid computing inside Z.le (which uses comparisons). Compute separately. *)
  set (v := chsh_local_z {| a0 := A0; a1 := A1; b0 := B0; b1 := B1 |});
  subst A0 A1 B0 B1;
  change (-2 <= v <= 2)%Z;

  (* Step 4: Verify v ∈ {-2, +2} by vm_compute *)
  assert (Hv : v = 2%Z \/ v = (-2)%Z)
    by (unfold v; vm_compute; first [left; reflexivity | right; reflexivity]);

  (* Step 5: Apply bound using computed value *)
  destruct Hv as [Hv|Hv]; rewrite Hv; split; lia.
Qed.

(** [local_strategy_chsh_abs_le_2_z] restates the preceding interval as an absolute-value bound. *)
Corollary local_strategy_chsh_abs_le_2_z :
  forall s,
    local_bits_ok s ->
  (* SAFE: Bounded arithmetic operation with explicit domain *)
    (Z.abs (chsh_local_z s) <= 2)%Z.
Proof.
  intros s Hbits.
  (* Step 1: Get double inequality from main theorem *)
  pose proof (local_strategy_chsh_between_neg2_2 s Hbits) as Hbounds.
  (* Step 2: Convert to absolute value form *)
  apply (proj2 (Z.abs_le (chsh_local_z s) 2)).
  (* Step 3: Exact match with hypothesis *)
  exact Hbounds.
Qed.

End KernelCHSH.
