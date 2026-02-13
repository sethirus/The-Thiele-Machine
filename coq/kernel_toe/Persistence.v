From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.

Module Persistence.

(** ====================================================================== *)
(** Fuel overlay (does not modify vm_step)                                  *)
(** ====================================================================== *)

Record FuelState := {
  fs_state : VMState;
  fs_fuel : nat
}.

Definition Dead (fs : FuelState) : Prop :=
  (vm_err (fs_state fs) = true) \/ (fs_fuel fs = 0).

Definition fuel_cost (i : vm_instruction) : nat := instruction_cost i.

Definition fuel_reward (i : vm_instruction) : nat :=
  match i with
  | _ => 0
  end.

Inductive fuel_step : FuelState -> vm_instruction -> FuelState -> Prop :=
| fuel_step_ok : forall s s' i fuel,
    vm_step s i s' ->
    fuel_cost i <= fuel ->
    fuel_step
      {| fs_state := s; fs_fuel := fuel |}
      i
      {| fs_state := s'; fs_fuel := (fuel - fuel_cost i) + fuel_reward i |}
| fuel_step_oom : forall s i fuel,
    fuel_cost i > fuel ->
    fuel_step
      {| fs_state := s; fs_fuel := fuel |}
      i
      {| fs_state := {| vm_graph := s.(vm_graph);
                        vm_csrs := s.(vm_csrs);
                        vm_regs := s.(vm_regs);
                        vm_mem := s.(vm_mem);
                        vm_pc := s.(vm_pc);
                        vm_mu := s.(vm_mu);
                        vm_err := true |};
         fs_fuel := 0 |}.

(** ====================================================================== *)
(** Contextual betting game overlay                                         *)
(** ====================================================================== *)

Definition CBettingStrategy : Type := FuelState -> list vm_instruction -> vm_instruction -> nat.

Definition cbet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (i : vm_instruction) : nat :=
  S fs choices i.

Definition ctotal_bet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) : nat :=
  fold_left Nat.add (map (cbet S fs choices) choices) 0.

Definition cavailable_after_reveal
  (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (oracle : vm_instruction)
  : nat :=
  (fs_fuel fs - ctotal_bet S fs choices) + cbet S fs choices oracle.

(** Decidable equality for vm_instruction (needed for membership checks). *)
Definition vm_instruction_eq_dec : forall (x y : vm_instruction), {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply string_dec;
    try (apply list_eq_dec; try apply Nat.eq_dec; try apply string_dec);
    try (decide equality; apply string_dec).
Qed.

(** Uniform strategy: split fuel across choice set.
    Special-case |choices|=1 to avoid Nat.div simplification churn.
*)
Definition UniformStrategy : CBettingStrategy :=
  fun fs choices i =>
    match List.length choices with
    | 0 => 0
    | 1 => if in_dec vm_instruction_eq_dec i choices then fs_fuel fs else 0
    | n => if in_dec vm_instruction_eq_dec i choices then fs_fuel fs / n else 0
    end.

Inductive game_stepC
  (S : CBettingStrategy)
  (choices : list vm_instruction)
  (oracle : vm_instruction)
  : FuelState -> FuelState -> Prop :=
| game_stepC_survive : forall fs s',
    In oracle choices ->
    cbet S fs choices oracle > 0 ->
    vm_step (fs_state fs) oracle s' ->
    fuel_cost oracle <= cavailable_after_reveal S fs choices oracle ->
    let fuel' := (cavailable_after_reveal S fs choices oracle - fuel_cost oracle) + fuel_reward oracle in
    fuel' > 0 ->
    game_stepC S choices oracle fs
      {| fs_state := s'; fs_fuel := fuel' |}
| game_stepC_die_zero_bet : forall fs,
    In oracle choices ->
    cbet S fs choices oracle = 0 ->
    game_stepC S choices oracle fs
      {| fs_state := {| vm_graph := (fs_state fs).(vm_graph);
                        vm_csrs := (fs_state fs).(vm_csrs);
                        vm_regs := (fs_state fs).(vm_regs);
                        vm_mem := (fs_state fs).(vm_mem);
                        vm_pc := (fs_state fs).(vm_pc);
                        vm_mu := (fs_state fs).(vm_mu);
                        vm_err := true |};
         fs_fuel := 0 |}.

Inductive game_exec_schedule
  (S : CBettingStrategy)
  : FuelState -> list (list vm_instruction * vm_instruction) -> FuelState -> Prop :=
| game_exec_schedule_nil : forall fs,
    game_exec_schedule S fs [] fs
| game_exec_schedule_cons : forall fs0 fs1 fsN choices oracle rest,
    game_stepC S choices oracle fs0 fs1 ->
    game_exec_schedule S fs1 rest fsN ->
    game_exec_schedule S fs0 ((choices, oracle) :: rest) fsN.

(** ====================================================================== *)
(** Expanding choice adversary + Uniformity is Fatal                        *)
(** ====================================================================== *)

Definition pnew_inst (n : nat) : vm_instruction := instr_pnew [n] 0.

Definition pnew_choices (n : nat) : list vm_instruction :=
  map pnew_inst (seq 0 n).

Definition schedule_expanding (fuel0 : nat) : list (list vm_instruction * vm_instruction) :=
  [(pnew_choices (S fuel0), pnew_inst 0)].

Lemma in_pnew_choices_0 : forall n,
  0 < n -> In (pnew_inst 0) (pnew_choices n).
Proof.
  intros n Hn.
  unfold pnew_choices.
  apply in_map.
  apply in_seq.
  split; [lia|lia].
Qed.

Lemma uniform_bet_zero_when_choices_exceed_fuel : forall fs choices oracle,
  In oracle choices ->
  List.length choices > fs_fuel fs ->
  cbet UniformStrategy fs choices oracle = 0.
Proof.
  intros fs choices oracle Hin Hlen.
  unfold cbet, UniformStrategy.
  destruct (List.length choices) as [|n] eqn:Hn.
  - apply List.length_zero_iff_nil in Hn.
    subst choices.
    contradiction.
  - destruct n as [|n'].
    + (* length = 1 *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * assert (fs_fuel fs = 0) by (rewrite <- Hn in Hlen; lia).
        now rewrite H.
      * exfalso. exact (Hcontra Hin).
    + (* length >= 2 *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * apply Nat.div_small.
        rewrite <- Hn in Hlen.
        lia.
      * exfalso. exact (Hcontra Hin).
Qed.

Theorem Uniform_Strategy_Dies : forall s0 fuel0,
  fuel0 > 0 ->
  exists fsN,
    game_exec_schedule UniformStrategy
      {| fs_state := s0; fs_fuel := fuel0 |}
      (schedule_expanding fuel0)
      fsN
    /\
    Dead fsN.
Proof.
  intros s0 fuel0 _.
  unfold schedule_expanding.
  exists
    {| fs_state := {| vm_graph := s0.(vm_graph);
                      vm_csrs := s0.(vm_csrs);
                      vm_regs := s0.(vm_regs);
                      vm_mem := s0.(vm_mem);
                      vm_pc := s0.(vm_pc);
                      vm_mu := s0.(vm_mu);
                      vm_err := true |};
       fs_fuel := 0 |}.
  split.
  - eapply game_exec_schedule_cons.
    + eapply game_stepC_die_zero_bet.
      * apply in_pnew_choices_0.
        apply Nat.lt_0_succ.
      * apply uniform_bet_zero_when_choices_exceed_fuel.
        -- apply in_pnew_choices_0.
           apply Nat.lt_0_succ.
        -- unfold pnew_choices.
           rewrite map_length, seq_length.
           unfold fs_fuel.
           simpl.
           apply Nat.lt_succ_diag_r.
    + constructor.
  - unfold Dead.
    right. reflexivity.
Qed.

End Persistence.
