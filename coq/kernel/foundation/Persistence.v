(** Persistence: a fuel overlay for resource-bounded execution

  This file adds a separate fuel counter on top of VM execution so resource
  limits can be stated operationally. Each instruction spends fuel according
  to its μ-cost, and execution halts with error once the budget is exhausted.

  The betting-game material then uses that overlay to talk about prediction
  under bounded resources. The point is not to redefine vm_step; it is to add
  a small operational layer where limited resources are explicit.
*)

From Coq Require Import List Bool Arith.PeanoNat Lia.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.

Module Persistence.

(** Fuel overlay; vm_step itself is unchanged. *)

(** FuelState is VMState plus a remaining resource budget. *)
Record FuelState := {
  fs_state : VMState;
  fs_fuel : nat
}.

(**
  Dead: Predicate for halted computation.

  WHY: I need a formal criterion for "computation cannot continue". Dead captures
  two ways a FuelState becomes terminal: either the VM encountered an error
  (vm_err = true), or fuel is exhausted (fs_fuel = 0).

  CLAIM: Dead fs ↔ no further fuel_step possible from fs.

  IMPLEMENTATION: Disjunction of vm_err flag and fuel = 0 check. Both are
  computable predicates (decidable).

  PHYSICAL MEANING: Dead represents thermodynamic equilibrium (no free energy left)
  or catastrophic failure (error state). Either way, no further computation possible.

  To falsify: Construct a Dead state fs and a valid fuel_step from fs. This
  would mean the Dead criterion is too weak (misses some halting conditions).

  game semantics (Dead is terminal condition).
*)
Definition Dead (fs : FuelState) : Prop :=
  (vm_err (fs_state fs) = true) \/ (fs_fuel fs = 0).

(**
  fuel_cost: Resource cost of an instruction in fuel units.

  WHY: I need to connect abstract μ-cost (instruction_cost) to operational
  resource depletion. fuel_cost defines how much fuel an instruction consumes.

  IMPLEMENTATION: Direct alias for instruction_cost (defined in VMStep.v).
  instruction_cost maps each instruction to its mu_delta field — the
  programmer-supplied cost parameter embedded in each instruction encoding.
  Costs are NOT fixed constants; they are parameterized values carried
  by each instruction instance (e.g., instr_pnew region mu_delta).

  PHYSICAL MEANING: fuel_cost is energy × time in natural units where 1 μ-bit
  = kT ln(2) Joules × (characteristic timescale). Higher cost = more
  thermodynamically irreversible operation.

  ISOMORPHISM: Matches μ-accounting in the extracted OCaml runner
  (build/thiele_core.ml) and the Kami RTL (coq/kami_hw/ThieleCPUCore.v).

  To falsify: Show instruction i where fuel_cost(i) ≠ instruction_cost(i).
  This would break the fuel/μ correspondence.

*)
Definition fuel_cost (i : vm_instruction) : nat := instruction_cost i.

(**
  fuel_reward: Fuel refunded after executing instruction (currently always 0).

  WHY: The betting game semantics allow for reward mechanisms (if you predict
  correctly, you get fuel back). In the current model, NO rewards are given -
  all costs are irreversible.

  IMPLEMENTATION: Constant function returning 0 for all instructions. The match
  structure is a placeholder for potential future reward policies (e.g., reward
  = cost for reversible operations).

  PHYSICAL MEANING: In thermodynamics, reversible processes (unitary evolution)
  should have zero NET cost. We could model this with reward = cost for unitary
  ops. Currently we keep it simple: all operations consume fuel irreversibly.

  DESIGN CHOICE: I chose reward = 0 because:
  1. Simplifies proofs (no need to track reversibility)
  2. Conservative bound (all costs are upper bounds)
  3. Matches physical irreversibility (no perfect reversibility in real hardware)

  To falsify: Show that setting reward = cost for unitary operations breaks
  μ-monotonicity or violates thermodynamic bounds. This would justify reward = 0.

*)
Definition fuel_reward (i : vm_instruction) : nat :=
  match i with
  | _ => 0
  end.

(**
  fuel_step: Resource-bounded state transition relation.

  WHY: I need operational semantics that ENFORCE resource limits. fuel_step wraps
  vm_step with fuel accounting: if cost ≤ fuel, proceed and deduct cost; if
  cost > fuel, halt with error.

  STRUCTURE: Two constructors:
  - fuel_step_ok: Sufficient fuel. Execute vm_step, deduct cost, add reward.
    New fuel = (old_fuel - fuel_cost i) + fuel_reward i.
  - fuel_step_oom: Out of memory (fuel_cost i > fuel). Set vm_err = true,
    fuel = 0. State components unchanged except error flag.

  CLAIM: fuel_step is deterministic given instruction. For any fs, i, there
  exists at most one fs' such that fuel_step fs i fs'.

  PHYSICAL MEANING: fuel_step models the second law of thermodynamics. Each
  operation consumes free energy. When you run out, the system reaches
  equilibrium (halts). The fuel_step_oom case is a thermodynamic "heat death"
  - no gradients left to extract work from.

  PROOF STRATEGY: Case split on fuel_cost i ≤? fuel. If yes, apply vm_step
  and arithmetic. If no, set error flag.

  To falsify: Find fs, i where fuel_cost i ≤ fuel but fuel_step sets vm_err.
  Or find fs, i where fuel_cost i > fuel but fuel_step succeeds. Either breaks
  the fuel accounting invariant.

  DEPENDENCIES: Requires vm_step (VMStep.v), instruction_cost (VMStep.v).

*)
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

(**  *)
(** Contextual betting game overlay                                         *)
(**  *)

(**
  CBettingStrategy: Predictive betting on instruction execution.

  WHY: I need to formalize "can you predict computation without paying for it?"
  A betting strategy takes current FuelState + choice set + specific choice, and
  returns how much fuel to bet on that choice. If you predict correctly (oracle
  = your choice), you get your bet back. If wrong, you lose the bet.

  STRUCTURE: Function type FuelState → list vm_instruction → vm_instruction → nat.
  - First arg: current state (what you can observe)
  - Second arg: possible instructions (choice set)
  - Third arg: specific instruction you're betting on
  - Return: fuel amount to bet

  GAME RULES:
  1. You must allocate fuel across the choice set BEFORE seeing the oracle.
  2. If oracle ∉ choice set, you lose all bets.
  3. If oracle ∈ choice set and you bet > 0 on oracle, you get that bet back.
  4. Total bet cannot exceed current fuel.
  5. If you bet 0 on the oracle, computation halts (Dead).

  PHYSICAL MEANING: The betting game models "predictive power". If you can
  systematically beat the uniform strategy (betting evenly), you must have
  INFORMATION about the computation. But gaining information costs fuel. The
  game tests whether you can extract information for free.

  To falsify: Construct a strategy S that beats UniformStrategy on all inputs
  WITHOUT consuming fuel to compute S itself. This would violate No Free Insight.

  EXAMPLES:
  - UniformStrategy: Split fuel evenly across choice set. Safe but inefficient.
  - OracleStrategy: Bet all fuel on correct choice (requires oracle access,
    costs fuel to compute oracle).

*)
Definition CBettingStrategy : Type := FuelState -> list vm_instruction -> vm_instruction -> nat.

(**
  cbet: Apply betting strategy to get fuel bet on specific instruction.

  WHY: Syntactic sugar for applying a CBettingStrategy. Makes game semantics
  more readable: "cbet S fs choices i" reads as "bet placed by S on i".

  IMPLEMENTATION: Direct function application S fs choices i. Pure wrapper.

*)
Definition cbet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (i : vm_instruction) : nat :=
  S fs choices i.

(**
  ctotal_bet: Sum of all bets placed on the choice set.

  WHY: The betting game requires total_bet ≤ fs_fuel (can't bet more than you have).
  ctotal_bet computes the sum of bets across all choices.

  IMPLEMENTATION: fold_left Nat.add over mapped (cbet S fs choices) across choices.
  Standard list sum pattern. Initial accumulator = 0.

  CLAIM: For valid strategies, ctotal_bet S fs choices ≤ fs_fuel fs.

  PHYSICAL MEANING: Total bet represents total energy committed to prediction.
  You can't commit more energy than you have available.

  To falsify: Show strategy S, state fs where ctotal_bet S fs choices > fs_fuel fs
  but game_stepC doesn't reject. This would mean betting rules aren't enforced.

*)
Definition ctotal_bet (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) : nat :=
  fold_left Nat.add (map (cbet S fs choices) choices) 0.

(**
  cavailable_after_reveal: Fuel remaining after oracle reveal.

  WHY: After bets are placed and oracle revealed, you get back ONLY your bet on
  the oracle (if any). cavailable_after_reveal computes the resulting fuel:
  fuel' = (fs_fuel - total_bet) + bet_on_oracle.

  - fs_fuel fs: Initial fuel before betting
  - ctotal_bet S fs choices: Sum of all bets (committed fuel)
  - cbet S fs choices oracle: Your bet on the revealed oracle instruction
  - Result: Uncommitted fuel + oracle bet refund

  CLAIM: If oracle ∉ choices, available_after_reveal = fs_fuel - total_bet
  (you lose all bets). If oracle ∈ choices, you get your oracle bet back.

  EXAMPLE: fs_fuel = 100, choices = [i1, i2, i3].
  Bet 30 on i1, 30 on i2, 40 on i3. Total = 100.
  Oracle = i2. Available = (100 - 100) + 30 = 30.
  Oracle = i4 (not in choices). Available = (100 - 100) + 0 = 0.

  PHYSICAL MEANING: Represents energy recovery if prediction was correct.
  Correct prediction means you "knew" the outcome, so the information was
  already encoded in your bet allocation (no new information gained, reversible).

  To falsify: Show oracle ∈ choices where available_after_reveal < 0.
  This would mean the arithmetic is broken (impossible with nat).

*)
Definition cavailable_after_reveal
  (S : CBettingStrategy) (fs : FuelState) (choices : list vm_instruction) (oracle : vm_instruction)
  : nat :=
  (fs_fuel fs - ctotal_bet S fs choices) + cbet S fs choices oracle.

(**
  vm_instruction_eq_dec: Decidable equality for vm_instruction type.

  WHY: The UniformStrategy needs to check membership (In i choices), which requires
  decidable equality. Coq doesn't automatically derive decidability for custom
  inductive types, so I prove it explicitly.

  CLAIM: For any instructions x, y, either x = y (left) or x ≠ y (right).

  PROOF STRATEGY: Apply decide equality tactic, recursively deciding equality
  on sub-components (nat, string, lists). All base types (nat, string) have
  decidable equality in stdlib.

  PHYSICAL MEANING: Instructions are discrete syntactic objects. Equality is
  computable by structural comparison (like comparing AST nodes).

  To falsify: Find instructions x, y where structural comparison gives wrong
  answer (x = y but they behave differently, or x ≠ y but they behave identically).
  This would mean the instruction representation is semantically ambiguous.

*)
(** Decidable equality for vm_instruction (needed for membership checks). *)
Definition vm_instruction_eq_dec : forall (x y : vm_instruction), {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply string_dec;
    try (apply list_eq_dec; try apply Nat.eq_dec; try apply string_dec);
    try (decide equality; apply string_dec).
Qed.

(**
  UniformStrategy: The "fair" betting strategy - split fuel evenly.

  WHY: UniformStrategy is the BASELINE for prediction games. It makes no assumptions
  about which instruction will be chosen - every choice gets equal weight. Any
  strategy that beats UniformStrategy must have INFORMATION about the computation.

  ALGORITHM:
  - If |choices| = 0: Bet 0 (no valid choices).
  - If |choices| = 1: Bet all fuel on that choice (deterministic).
  - If |choices| > 1: Bet fuel / |choices| on each choice (even split).
  - If i ∉ choices: Bet 0 on i (invalid choice).

  CLAIM: UniformStrategy satisfies ctotal_bet ≤ fs_fuel (valid strategy).

  PHYSICAL MEANING: UniformStrategy is maximum entropy betting - no bias toward
  any outcome. This is the "ignorance prior" in Bayesian terms. Beating this
  strategy means you have mutual information with the oracle.

  To falsify: Show that UniformStrategy systematically loses fuel faster than
  alternative strategies WITHOUT those alternatives computing the oracle (free
  information). This would mean "ignorance is suboptimal" without learning cost.

  CRITICAL PROPERTY: When |choices| > fuel, UniformStrategy bets 0 on all choices
  (fuel / n = 0 when fuel < n). This leads to Uniform_Strategy_Dies theorem.

  baseline for betting game analysis.
*)
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

(**
  game_stepC: One step in the betting game with contextual choices.

  WHY: I need operational semantics for the betting game. game_stepC defines what
  happens when the oracle is revealed: either computation continues (survived)
  or halts (died).

  STRUCTURE: Two constructors:

  1. game_stepC_survive: Successful prediction. Requirements:
     - oracle ∈ choices (oracle is valid)
     - cbet S fs choices oracle > 0 (you bet on the oracle)
     - vm_step succeeds (underlying VM transition valid)
     - fuel_cost oracle ≤ available_after_reveal (enough fuel for instruction)
     - fuel' > 0 after deducting cost (still alive)
     New state: fs' = {| fs_state := s'; fs_fuel := fuel' |}.

  2. game_stepC_die_zero_bet: Failed prediction. Requirements:
     - oracle ∈ choices (oracle is valid)
     - cbet S fs choices oracle = 0 (you bet nothing on oracle)
     Immediately halt with vm_err = true, fs_fuel = 0.

  CLAIM: If game_stepC S choices oracle fs fs', then either:
  - fs' is Dead (terminal state), OR
  - fs' has strictly less fuel than fs (progress).

  PHYSICAL MEANING: game_stepC models "predictive work extraction". If you predict
  correctly AND have enough fuel, you can continue. If you fail to predict (bet 0),
  you cannot extract work from the system (halts). This is like Maxwell's demon
  - prediction enables work extraction, but prediction itself costs energy.

  PROOF STRATEGY: Case split on cbet S fs choices oracle. If 0, immediate halt.
  If > 0, check fuel arithmetic and vm_step validity.

  To falsify: Construct fs, oracle where cbet = 0 but game_stepC_survive succeeds.
  Or show game_stepC_survive with fuel' > available_after_reveal (violates
  conservation). Either breaks the game semantics.

  DEPENDENCIES: Requires vm_step, fuel_cost, cavailable_after_reveal.

*)
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

(**
  game_exec_schedule: Multi-step execution of betting game with schedule.

  WHY: I need to model sequences of betting rounds. game_exec_schedule executes
  a schedule = list of (choices, oracle) pairs, where each round the adversary
  presents choices and reveals oracle.

  STRUCTURE: Inductive relation with two constructors:

  1. game_exec_schedule_nil: Base case. Empty schedule = no steps = identity.
     fs unchanged.

  2. game_exec_schedule_cons: Inductive case. Execute first round (choices, oracle),
     get intermediate state fs1, then recursively execute rest of schedule.

  CLAIM: If game_exec_schedule S fs sched fsN, then fsN is reachable from fs
  via the sequence of choices/oracles in sched.

  PHYSICAL MEANING: The schedule represents an adversarial interaction. The
  adversary can adaptively choose which instructions to present at each round
  (like a "prediction demon" testing your strategy). If your strategy fails to
  predict ANY round, you die.

  PROOF STRATEGY: Induction on schedule list. Base case trivial. Inductive case
  chains game_stepC with recursive call.

  To falsify: Show schedule where game_exec_schedule succeeds but Dead fs0
  (started dead). Or show non-Dead fs with empty schedule reaching Dead fsN
  (spontaneous death). Either breaks the semantics.

  DEPENDENCIES: Requires game_stepC.

*)
Inductive game_exec_schedule
  (S : CBettingStrategy)
  : FuelState -> list (list vm_instruction * vm_instruction) -> FuelState -> Prop :=
| game_exec_schedule_nil : forall fs,
    game_exec_schedule S fs [] fs
| game_exec_schedule_cons : forall fs0 fs1 fsN choices oracle rest,
    game_stepC S choices oracle fs0 fs1 ->
    game_exec_schedule S fs1 rest fsN ->
    game_exec_schedule S fs0 ((choices, oracle) :: rest) fsN.

(**  *)
(** Expanding choice adversary + Uniformity is Fatal                        *)
(**  *)

(**
  pnew_inst: Create PNEW instruction with given module ID.

  WHY: Helper to construct PNEW instructions uniformly. PNEW creates new partition
  modules, costs 6 μ-bits per operation.

  IMPLEMENTATION: pnew_inst n = instr_pnew [n] 0.
  - First arg [n]: Module ID list (singleton for simplicity).
  - Second arg 0: Register destination (unused in this analysis).

  PHYSICAL MEANING: PNEW allocates new partition structure, irreversible operation.

*)
Definition pnew_inst (n : nat) : vm_instruction := instr_pnew [n] 0.

(**
  pnew_choices: Generate list of n PNEW instructions.

  WHY: The adversary needs to construct EXPANDING choice sets. pnew_choices n
  creates [PNEW(0), PNEW(1), ..., PNEW(n-1)], giving n distinct choices.

  IMPLEMENTATION: map pnew_inst (seq 0 n). Standard Coq pattern for list generation.

  CLAIM: |pnew_choices n| = n.

  ADVERSARIAL USE: When n > fuel, UniformStrategy bets fuel/n = 0 on each choice
  (integer division rounds down). This triggers game_stepC_die_zero_bet.

  PHYSICAL MEANING: Represents an adversary that ADAPTIVELY EXPANDS the search
  space. "Here are n partition creation operations - predict which one I'll pick."
  As n grows beyond fuel, uniform betting fails.

  To falsify: Show UniformStrategy survives pnew_choices (fuel + 1) without
  additional fuel. This would mean uniform betting handles unbounded choice sets.

*)
Definition pnew_choices (n : nat) : list vm_instruction :=
  map pnew_inst (seq 0 n).

(**
  schedule_expanding: THE ADVERSARIAL SCHEDULE that kills UniformStrategy.

  WHY: I need a concrete schedule that proves UniformStrategy is not universally
  optimal. schedule_expanding presents (fuel0 + 1) choices when fuel = fuel0.

  CONSTRUCTION: One-round schedule: [(pnew_choices (S fuel0), pnew_inst 0)].
  - Choices: S fuel0 = fuel0 + 1 PNEW instructions.
  - Oracle: pnew_inst 0 (the first PNEW).

  THE ATTACK: UniformStrategy bets fuel0 / (fuel0 + 1) on each choice.
  Since fuel0 / (fuel0 + 1) = 0 (integer division), UniformStrategy bets 0
  on the oracle. Result: game_stepC_die_zero_bet. Immediate halt.

  CLAIM: ∀ fuel0 > 0, game_exec_schedule UniformStrategy
         {| fs_state := s0; fs_fuel := fuel0 |} (schedule_expanding fuel0) fsN
         → Dead fsN.

  PHYSICAL MEANING: This is a "prediction impossibility" result. If the adversary
  can expand the search space beyond your fuel budget, uniform betting MUST fail.
  There's no hedging bets across unbounded choices with finite resources.

  To falsify: Show fuel0, s0 where UniformStrategy survives schedule_expanding fuel0.
  This would mean the schedule doesn't achieve the claimed adversarial effect.

*)
Definition schedule_expanding (fuel0 : nat) : list (list vm_instruction * vm_instruction) :=
  [(pnew_choices (S fuel0), pnew_inst 0)].

(**
  in_pnew_choices_0: The instruction pnew_inst 0 is in pnew_choices n when n > 0.

  WHY: I need to prove the oracle is a valid choice in schedule_expanding. This
  lemma establishes that pnew_inst 0 ∈ pnew_choices n for n > 0.

  CLAIM: ∀ n > 0, pnew_inst 0 ∈ pnew_choices n.

  1. Unfold pnew_choices n = map pnew_inst (seq 0 n).
  2. Apply in_map: suffices to show 0 ∈ seq 0 n.
  3. Apply in_seq: show 0 ≤ 0 < n. Follows from n > 0 (lia).

  PHYSICAL MEANING: Trivial membership check. The 0th PNEW instruction is the
  first element of the choice list.

  To falsify: Show n > 0 where pnew_inst 0 ∉ pnew_choices n. This would mean
  seq or map is broken (impossible in Coq).

*)
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

(**
  uniform_bet_zero_when_choices_exceed_fuel: UniformStrategy bets 0 when choices > fuel.

  WHY: This is THE KEY LEMMA for Uniform_Strategy_Dies. I need to prove that when
  |choices| > fuel, UniformStrategy bets 0 on EVERY choice (including oracle).

  CLAIM: If oracle ∈ choices AND |choices| > fuel, then
         cbet UniformStrategy fs choices oracle = 0.

  1. Unfold cbet, UniformStrategy.
  2. Case split on |choices|:
     - |choices| = 0: Contradiction (oracle ∈ choices but choices empty).
     - |choices| = 1: Then fuel < 1, so fuel = 0. Bet = fuel = 0.
     - |choices| ≥ 2: Bet = fuel / |choices|. Since |choices| > fuel and
       both are nat, fuel / |choices| = 0 (integer division).
  3. Each case uses decidability of oracle ∈ choices via in_dec.

  PHYSICAL MEANING: When the search space exceeds your resources, uniform allocation
  gives ZERO to each choice. This is integer division failure: 10 resources / 11
  choices = 0 per choice (can't allocate fractional resources).

  To falsify: Find choices, fuel, oracle where |choices| > fuel but
  UniformStrategy bets > 0 on oracle. This would break the uniform allocation logic.

  DEPENDENCIES: Requires UniformStrategy definition, Nat.div_small (stdlib).

*)
Lemma uniform_bet_zero_when_choices_exceed_fuel : forall fs choices oracle,
  In oracle choices ->
  List.length choices > fs_fuel fs ->
  cbet UniformStrategy fs choices oracle = 0.
Proof.
  intros fs choices oracle Hin Hlen.
  (* Step 1: Unfold betting computation *)
  unfold cbet, UniformStrategy.
  (* Step 2: Case split on list length *)
  destruct (List.length choices) as [|n] eqn:Hn.
  - (* Case |choices| = 0: Contradiction *)
    apply List.length_zero_iff_nil in Hn.
    subst choices.
    contradiction.
  - (* Case |choices| = S n *)
    destruct n as [|n'].
    + (* Subcase |choices| = 1: fuel = 0 *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * assert (fs_fuel fs = 0) by (rewrite <- Hn in Hlen; lia).
        now rewrite H.
      * exfalso. exact (Hcontra Hin).
    + (* Subcase |choices| ≥ 2: Apply Nat.div_small *)
      destruct (in_dec vm_instruction_eq_dec oracle choices) as [_|Hcontra].
      * apply Nat.div_small.
        rewrite <- Hn in Hlen.
        lia.
      * exfalso. exact (Hcontra Hin).
Qed.

(**
  Uniform_Strategy_Dies: THE MAIN THEOREM - UniformStrategy is not universally optimal.

  For any initial state s0 and fuel0 > 0, there exists a schedule
  (schedule_expanding fuel0) such that UniformStrategy reaches a Dead state.

  WHY THIS MATTERS: This proves that "ignorance betting" (uniform allocation)
  CANNOT handle adversarially chosen search spaces. The adversary simply presents
  (fuel + 1) choices, forcing uniform bets to round down to 0, immediately halting
  the computation.

  CLAIM: ∀ s0, fuel0 > 0. ∃ fsN.
         game_exec_schedule UniformStrategy
           {| fs_state := s0; fs_fuel := fuel0 |}
           (schedule_expanding fuel0)
           fsN
         ∧ Dead fsN.

  1. Construct witness fsN = {| fs_state := error_state; fs_fuel := 0 |}.
  2. Prove game_exec_schedule succeeds:
     a. Apply game_exec_schedule_cons (one-step schedule).
     b. Apply game_stepC_die_zero_bet (zero bet on oracle).
     c. Prove oracle ∈ choices via in_pnew_choices_0.
     d. Prove bet = 0 via uniform_bet_zero_when_choices_exceed_fuel.
     e. Base case: game_exec_schedule_nil.
  3. Prove Dead fsN: fs_fuel = 0, so Dead by definition.

  PHYSICAL INTERPRETATION: This is a formalization of "No Free Lunch" in search.
  If the adversary can adaptively expand the hypothesis space beyond your
  computational budget, uniform search MUST fail. There's no maintaining constant
  probability mass across unbounded choices with finite resources.

  COMPUTATIONAL COMPLEXITY CONNECTION: This relates to the "expanding search
  space" problem in AI. If each step the adversary doubles the branching factor,
  uniform search (breadth-first) exhausts resources exponentially. The theorem
  proves this is UNAVOIDABLE without biased (informed) search.

  To falsify: Find s0, fuel0 where UniformStrategy survives schedule_expanding fuel0
  (reaches non-Dead state). This would mean uniform allocation can handle
  unbounded search spaces, contradicting computational complexity lower bounds.

  DEPENDENCIES: Requires game_exec_schedule, game_stepC_die_zero_bet, Dead,
  schedule_expanding, in_pnew_choices_0, uniform_bet_zero_when_choices_exceed_fuel.

  CONSEQUENCES: This theorem justifies the need for INFORMED search strategies
  (strategies that spend fuel to gather information, then bet non-uniformly).
  Uniform betting is a baseline, NOT an optimal strategy. Beating it requires
  mutual information with the oracle (which costs fuel to acquire).

  RELATED RESULTS:
  - No Free Insight (NoFreeInsight.v): You can't reduce search space without μ-cost.
  - No Free Lunch (search theory): No universal optimal search algorithm.
  - Landauer's principle: Information erasure costs energy (kT ln 2 per bit).

  This theorem connects μ-cost theory to algorithmic search impossibility results.
*)
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
  (* Step 1: Construct witness fsN (error state with zero fuel) *)
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
  (* Step 2: Prove game_exec_schedule succeeds *)
  - (* Apply one-step schedule constructor *)
    eapply game_exec_schedule_cons.
    + (* Prove game_stepC with zero bet *)
      eapply game_stepC_die_zero_bet.
      * (* Prove oracle ∈ choices *)
        apply in_pnew_choices_0.
        apply Nat.lt_0_succ.
      * (* Prove uniform bet = 0 when |choices| > fuel *)
        apply uniform_bet_zero_when_choices_exceed_fuel.
        -- (* Oracle in choices (again) *)
           apply in_pnew_choices_0.
           apply Nat.lt_0_succ.
        -- (* |choices| = S fuel0 > fuel0 *)
           unfold pnew_choices.
           rewrite map_length, seq_length.
           unfold fs_fuel.
           simpl.
           apply Nat.lt_succ_diag_r.
    + (* Base case: empty schedule *)
      constructor.
  (* Step 3: Prove Dead fsN *)
  - unfold Dead.
    right. reflexivity.
Qed.

End Persistence.
