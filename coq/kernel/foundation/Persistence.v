(** This file adds a fuel-bounded transition relation on top of [vm_step].
    Successful steps deduct the declared instruction cost and failed budget checks set the VM error flag.
    The later betting definitions are a separate game overlay; neither layer changes [vm_step]. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.

Module Persistence.

(** The fuel overlay leaves [vm_step] unchanged. *)

(** [FuelState] pairs a VM state with a remaining natural-number budget. *)
Record FuelState := {
  fs_state : VMState;
  fs_fuel : nat
}.

(** [Dead] marks a fuel state whose VM error flag is set or whose budget is zero.
    It is an operational terminal predicate for this overlay, not a thermodynamic definition. *)
Definition Dead (fs : FuelState) : Prop :=
  (vm_err (fs_state fs) = true) \/ (fs_fuel fs = 0).

(** [fuel_cost] is exactly the VM's declared [instruction_cost].
    This is an operational correspondence; it does not calibrate natural-number cost to joules or thermodynamic irreversibility. *)
Definition fuel_cost (i : vm_instruction) : nat := instruction_cost i.

(** [fuel_reward] is the current refund policy and returns zero for every instruction. *)
Definition fuel_reward (i : vm_instruction) : nat :=
  match i with
  | _ => 0
  end.

(** [fuel_step] either applies [vm_step] when the budget covers the instruction or records an out-of-budget error with zero remaining fuel. *)
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
                        vm_mu_tensor := s.(vm_mu_tensor);
                        vm_err := true;
                        vm_logic_acc := s.(vm_logic_acc);
                        vm_mstatus := s.(vm_mstatus);
                        vm_witness := s.(vm_witness);
                        vm_certified := s.(vm_certified) |};
         fs_fuel := 0 |}.

(** The following definitions describe a separate contextual betting game over [FuelState]. *)

(** [CBettingStrategy] assigns a natural-number bet to a state, choice list, and selected instruction.
    The game rules and any comparison with prediction or information must be read from the later definitions and theorems; this type alone makes no such claim. *)
Definition CBettingStrategy : Type := FuelState -> list vm_instruction -> vm_instruction -> nat.

(** [cbet] applies a betting strategy to one instruction. *)
Definition cbet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (i : vm_instruction) : nat :=
  S fs choices i.

(** [ctotal_bet] sums the bets over the supplied choice list. *)
Definition ctotal_bet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) : nat :=
  fold_left Nat.add (map (cbet S fs choices) choices) 0.

(** [cavailable_after_reveal] returns uncommitted fuel plus the bet on the revealed instruction. *)
Definition cavailable_after_reveal
  (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (oracle : vm_instruction)
  : nat :=
  (fs_fuel fs - ctotal_bet S fs choices) + cbet S fs choices oracle.

(** Structural equality on instructions is used for membership checks in [UniformStrategy]. *)
(** Decidable equality for vm_instruction (needed for membership checks). *)
Definition vm_instruction_eq_dec : forall (x y : vm_instruction), {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply string_dec;
    try (apply list_eq_dec; try apply Nat.eq_dec; try apply string_dec);
    try (decide equality; apply string_dec).
Qed.

(** [UniformStrategy] divides the available fuel evenly across the supplied choices, with explicit cases for empty and singleton lists. *)
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

(** [game_stepC] describes one betting-game transition: a positive bet may permit a VM step when the revealed instruction is affordable, while a zero bet produces the terminal error state. *)
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
                        vm_mu_tensor := (fs_state fs).(vm_mu_tensor);
                        vm_err := true;
                        vm_logic_acc := (fs_state fs).(vm_logic_acc);
                        vm_mstatus := (fs_state fs).(vm_mstatus);
                        vm_witness := (fs_state fs).(vm_witness);
                        vm_certified := (fs_state fs).(vm_certified) |};
         fs_fuel := 0 |}.

(** [game_exec_schedule] folds [game_stepC] over a list of choice and oracle pairs; the empty schedule leaves the fuel state unchanged, and the cons case records one step before the remaining schedule. *)
Inductive game_exec_schedule
  (S : CBettingStrategy)
  : FuelState -> list (list vm_instruction * vm_instruction) -> FuelState -> Prop :=
| game_exec_schedule_nil : forall fs,
    game_exec_schedule S fs [] fs
| game_exec_schedule_cons : forall fs0 fs1 fsN choices oracle rest,
    game_stepC S choices oracle fs0 fs1 ->
    game_exec_schedule S fs1 rest fsN ->
    game_exec_schedule S fs0 ((choices, oracle) :: rest) fsN.

(** [pnew_inst] constructs the one-module [PNEW] instruction used by the finite betting example. The definition records the instruction shape; it does not add a separate physical interpretation. *)
Definition pnew_inst (n : nat) : vm_instruction := instr_pnew [n] 0.

(** [pnew_choices] lists the first [n] instances of [pnew_inst]. When the list is longer than the available fuel, the uniform natural-number split rounds each bet down to zero. *)
Definition pnew_choices (n : nat) : list vm_instruction :=
  map pnew_inst (seq 0 n).

(** [schedule_expanding] is the one-round schedule used by the uniform-bet counterexample: it presents [S fuel0] choices and reveals [pnew_inst 0]. *)
Definition schedule_expanding (fuel0 : nat) : list (list vm_instruction * vm_instruction) :=
  [(pnew_choices (S fuel0), pnew_inst 0)].

(** This lemma proves that the revealed instruction [pnew_inst 0] is one of the choices whenever the choice list is nonempty. *)
Lemma in_pnew_choices_0 : forall n,
  0 < n -> In (pnew_inst 0) (pnew_choices n).
Proof.
  intros n Hn.
  (* Step 1: Unfold pnew_choices to map + seq *)
  unfold pnew_choices.
  (* Step 2: Reduce membership to seq membership *)
  apply in_map.
  (* Step 3: 0 is in seq 0 n when n > 0 *)
  apply in_seq.
  split; [lia|lia].
Qed.

(** If the revealed choice list is longer than the available fuel, [UniformStrategy] assigns zero to the revealed instruction. The proof uses the empty, singleton, and longer-list cases of natural-number division. *)
Lemma uniform_bet_zero_when_choices_exceed_fuel : forall fs choices oracle,
  In oracle choices ->
  List.length choices > fs_fuel fs ->
  cbet UniformStrategy fs choices oracle = 0.
Proof.
  intros fs choices oracle Hin Hlen.
  (* Expose the strategy and its membership test. *)
  unfold cbet, UniformStrategy.
  (* Split on the length of the choice list. *)
  destruct (List.length choices) as [|n] eqn:Hn.
  - (* An empty list cannot contain the oracle. *)
    apply List.length_zero_iff_nil in Hn.
    subst choices.
    contradiction.
  - (* Case |choices| = S n *)
    destruct n as [|n'].
    + (* A singleton longer than the fuel forces zero fuel. *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * assert (fs_fuel fs = 0) by (rewrite <- Hn in Hlen; lia).
        now rewrite H.
      * exfalso. exact (Hcontra Hin).
    + (* For a longer list, the denominator exceeds the numerator. *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * apply Nat.div_small.
        rewrite <- Hn in Hlen.
        lia.
      * exfalso. exact (Hcontra Hin).
Qed.

(** For every positive initial fuel value, this theorem supplies a one-round expanding schedule on which [UniformStrategy] reaches a state with zero fuel. The result is about this explicit integer-bet game; it is not a general theorem about search, complexity, or thermodynamics. *)
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
  (* Use the VM state with the same data and its error flag set, paired with zero fuel. *)
  unfold schedule_expanding.
  exists
    {| fs_state := {| vm_graph := s0.(vm_graph);
                      vm_csrs := s0.(vm_csrs);
                      vm_regs := s0.(vm_regs);
                      vm_mem := s0.(vm_mem);
                      vm_pc := s0.(vm_pc);
                      vm_mu := s0.(vm_mu);
                      vm_mu_tensor := s0.(vm_mu_tensor);
                      vm_err := true;
                      vm_logic_acc := s0.(vm_logic_acc);
                      vm_mstatus := s0.(vm_mstatus);
                      vm_witness := s0.(vm_witness);
                      vm_certified := s0.(vm_certified) |};
       fs_fuel := 0 |}.
  split.
  (* Prove the one-round schedule and then the terminal condition. *)
  - (* Apply the one-step schedule constructor. *)
    eapply game_exec_schedule_cons.
    + (* The revealed instruction receives a zero bet. *)
      eapply game_stepC_die_zero_bet.
      * (* The revealed instruction is in the choice list. *)
        apply in_pnew_choices_0.
        apply Nat.lt_0_succ.
      * (* The list length exceeds the available fuel. *)
        apply uniform_bet_zero_when_choices_exceed_fuel.
        -- (* Repeat the membership premise for the betting lemma. *)
           apply in_pnew_choices_0.
           apply Nat.lt_0_succ.
        -- (* The generated list has length [S fuel0]. *)
           unfold pnew_choices.
           rewrite map_length, seq_length.
           unfold fs_fuel.
           simpl.
           apply Nat.lt_succ_diag_r.
    + (* The rest of the schedule is empty. *)
      constructor.
  (* The resulting fuel value is zero. *)
  - unfold Dead.
    right. reflexivity.
Qed.

End Persistence.
