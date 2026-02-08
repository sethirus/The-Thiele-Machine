From Coq Require Import List Bool Arith.PeanoNat ZArith QArith Lia.
Require Import Coq.QArith.Qabs.
Import ListNotations.
Open Scope Q_scope.

Require Import VMStep.

(** * CHSH: Computing the CHSH statistic from execution receipts

    WHY THIS EXISTS:
    The Thiele Machine produces cryptographic receipts for every instruction.
    This file defines how to extract CHSH statistics from those receipts,
    turning abstract correlation bounds into CONCRETE, VERIFIABLE tests.

    THE SETUP:
    Execution trace contains instr_chsh_trial(x,y,a,b) records. Each record is:
    - x,y: Alice and Bob's measurement settings (0 or 1)
    - a,b: Alice and Bob's outcomes (0 or 1)

    These are NON-FORGEABLE. The kernel guarantees they came from actual execution.

    THE CHSH STATISTIC:
    S = E(1,1) + E(1,0) + E(0,1) - E(0,0)

    where E(x,y) = average of sign(a)*sign(b) over all trials with settings (x,y).
    sign(0)=-1, sign(1)=+1. This gives correlations in [-1,+1].

    THE BOUNDS (proven elsewhere):
    - Local strategies: |S| ≤ 2 (MinorConstraints.v)
    - Quantum: |S| ≤ 2√2 (AlgebraicCoherence.v)
    - No-signaling: |S| ≤ 4 (BoxCHSH.v)

    This file proves the LOCAL BOUND directly by exhaustive enumeration:
    There are 16 possible deterministic strategies (4 bits: a0,a1,b0,b1).
    For each one, compute S. Check all 16 give |S| ≤ 2. Done.

    FALSIFICATION:
    Find a deterministic local strategy with |S| > 2. There are only 16.
    Check them all. None exceed 2. QED.
*)

Module KernelCHSH.

Import VMStep.VMStep.

(**
  Trial: One measurement record in a Bell/CHSH experiment.

  WHY: I need a structured representation of experimental data. Each Trial records
  the settings (x,y) chosen by Alice and Bob, and the outcomes (a,b) they observed.

  STRUCTURE:
  - t_x: Alice's measurement setting (0 or 1)
  - t_y: Bob's measurement setting (0 or 1)
  - t_a: Alice's outcome (0 or 1)
  - t_b: Bob's outcome (0 or 1)

  PHYSICAL MEANING: A Trial is ONE SHOT of the experiment. Alice chooses to measure
  observable X₀ or X₁ (x ∈ {0,1}), Bob chooses Y₀ or Y₁ (y ∈ {0,1}). They each
  get a bit (a,b). These are SPACELIKE SEPARATED (Alice can't influence Bob's
  result, Bob can't influence Alice's result). Repeat this many times to estimate
  E(x,y) = ⟨ab⟩ = correlation.

  CRYPTOGRAPHIC GUARANTEE: Trials come from instr_chsh_trial receipts. The kernel
  guarantees these are NON-FORGEABLE. You cannot fake CHSH > 2√2 by manipulating
  receipts - the hash chain prevents tampering.

  EXAMPLE: {| t_x := 1; t_y := 1; t_a := 0; t_b := 1 |} means Alice measured X₁,
  got outcome 0; Bob measured Y₁, got outcome 1.

  FALSIFICATION: Show that manipulated Trial records can yield CHSH > 2√2 when
  checked by this module. This would mean the receipt integrity check is broken.

  USED BY: trials_of_receipts, trial_value_z, count_setting, sum_setting_z,
  expectation, chsh, trial_of_local.
*)
Record Trial : Type := {
  t_x : nat;
  t_y : nat;
  t_a : nat;
  t_b : nat;
}.

(**
  is_trial_instr: Extract Trial from VM instruction (if it's a CHSH trial).

  WHY: Execution traces contain MIXED instructions (ALU ops, memory ops, CHSH trials).
  I need to filter out the CHSH trial records specifically.

  ALGORITHM:
  - If instruction is instr_chsh_trial x y a b _:
    * Check chsh_bits_ok x y a b (all values are 0 or 1)
    * If valid, return Some {| Trial record |}
    * If invalid, return None (malformed trial)
  - If instruction is anything else: return None

  VALIDATION: chsh_bits_ok enforces x,y,a,b ∈ {0,1}. This prevents corrupted
  data from entering the CHSH computation.

  PHYSICAL MEANING: The kernel can emit arbitrary instructions. Only those matching
  the instr_chsh_trial pattern with valid bits represent actual measurements.

  FALSIFICATION: Construct a valid instr_chsh_trial where chsh_bits_ok fails but
  the trial should be accepted. Or show a non-trial instruction that gets parsed
  as a trial. Either breaks the filtering logic.

  USED BY: trials_of_receipts (maps this over instruction list).
*)
Definition is_trial_instr (i : vm_instruction) : option Trial :=
  match i with
  | instr_chsh_trial x y a b _ =>
      if chsh_bits_ok x y a b then Some {| t_x := x; t_y := y; t_a := a; t_b := b |}
      else None
  | _ => None
  end.

(**
  trials_of_receipts: Extract all valid CHSH trials from execution trace.

  WHY: The VM execution trace is a list of vm_instructions. I need to filter this
  down to ONLY the CHSH trial records, discarding all other instructions.

  ALGORITHM: Recursively scan instruction list:
  - Empty list: return []
  - i :: tl: Apply is_trial_instr to i.
    * Some t: Prepend t to trials_of_receipts tl
    * None: Skip i, continue with trials_of_receipts tl

  TERMINATION: Structural recursion on list. Each recursive call has strictly
  smaller list (tl < i :: tl).

  CLAIM: ∀ rs. trials_of_receipts rs contains ONLY valid Trials (all fields ∈ {0,1}).

  PHYSICAL MEANING: This is the DATA EXTRACTION step. After running a Bell
  experiment on the Thiele Machine, you have a trace of millions of instructions.
  trials_of_receipts gives you the experimental dataset: list of (x,y,a,b) records.

  EXAMPLE: Input: [instr_add ..., instr_chsh_trial 0 0 1 1 _, instr_load ...,
                    instr_chsh_trial 1 0 0 1 _, ...]
           Output: [{| t_x:=0; t_y:=0; t_a:=1; t_b:=1 |},
                    {| t_x:=1; t_y:=0; t_a:=0; t_b:=1 |}]

  FALSIFICATION: Show trials_of_receipts rs contains invalid trial (x > 1 or y > 1
  or a > 1 or b > 1). This would mean is_trial_instr validation failed.

  COMPUTATIONAL COMPLEXITY: O(|rs|) time, O(number of trials) space. Linear scan.

  USED BY: chsh (applies this to get trial list, then computes statistic).
*)
Fixpoint trials_of_receipts (rs : list vm_instruction) : list Trial :=
  match rs with
  | [] => []
  | i :: tl =>
      match is_trial_instr i with
      | Some t => t :: trials_of_receipts tl
      | None => trials_of_receipts tl
      end
  end.

(**
  sign_z: Convert measurement outcome bit to ±1 correlation sign.

  WHY: CHSH correlations are defined as E(x,y) = ⟨sign(a)·sign(b)⟩ where sign(0) = -1,
  sign(1) = +1. This matches quantum mechanics convention (eigenvalues ±1).

  ALGORITHM: If bit = 1, return +1. Else (bit = 0), return -1.

  PHYSICAL MEANING: In quantum mechanics, measurement outcomes are eigenvalues of
  observables. For spin-1/2 particles (qubits), measuring σz gives outcomes ±1
  (not 0/1). The 0/1 encoding is computational convenience; sign_z converts to
  physical eigenvalues.

  EXAMPLE: Measuring qubit in |0⟩ gives outcome 0 (computational basis), which
  corresponds to eigenvalue -1 of σz. Measuring |1⟩ gives 1 → +1.

  FALSIFICATION: Show quantum CHSH experiment where outcomes are {0,1} instead of
  {-1,+1} and the correlation formula changes. This would mean the sign_z
  encoding doesn't match physical reality.

  USED BY: trial_value_z (computes a·b product of signs).
*)
Definition sign_z (bit : nat) : Z :=
  if Nat.eqb bit 1 then 1%Z else (-1)%Z.

(**
  trial_value_z: Compute correlation value for a single trial: sign(a) × sign(b).

  WHY: The CHSH correlation E(x,y) is the AVERAGE of trial_value_z over all trials
  with settings (x,y). This function computes the per-trial contribution.

  ALGORITHM: trial_value_z t = sign_z(t.a) × sign_z(t.b).
  Possible values: (+1)×(+1) = +1, (+1)×(-1) = -1, (-1)×(+1) = -1, (-1)×(-1) = +1.
  So trial_value_z ∈ {-1, +1}.

  CLAIM: ∀ t. trial_value_z t = +1 or trial_value_z t = -1.

  PHYSICAL MEANING: This is the CORRELATION PRODUCT. When Alice and Bob get the
  same outcome (both 0 or both 1), trial_value = +1 (correlated). When different
  outcomes (one 0, one 1), trial_value = -1 (anti-correlated).

  EXAMPLE: t = {| t_x:=1; t_y:=1; t_a:=1; t_b:=0 |}.
           sign_z(1) = +1, sign_z(0) = -1. Product = +1 × -1 = -1.

  FALSIFICATION: Show trial t where trial_value_z t ∉ {-1, +1}. This would mean
  the sign_z mapping is broken (impossible given sign_z definition).

  USED BY: sum_setting_z (sums trial_value_z over filtered trials).
*)
Definition trial_value_z (t : Trial) : Z :=
  (sign_z t.(t_a) * sign_z t.(t_b))%Z.

(**
  count_setting: Count trials matching specific settings (x,y).

  WHY: To compute E(x,y), I need the NUMBER of trials with those settings. This
  is the denominator in the average: E(x,y) = (sum of values) / (count).

  ALGORITHM: Recursively scan trial list:
  - Empty list: return 0
  - t :: tl: If t.x = x AND t.y = y, return 1 + count_setting x y tl.
              Else, return count_setting x y tl (skip this trial).

  TERMINATION: Structural recursion on list.

  CLAIM: count_setting x y ts = |{t ∈ ts | t.x = x ∧ t.y = y}| (cardinality of
  filtered set).

  PHYSICAL MEANING: In a Bell experiment, you randomly choose settings. If you
  run 1000 trials, maybe 250 have (x,y) = (0,0), 250 have (0,1), etc. count_setting
  tells you how many trials had each setting combination.

  EXAMPLE: ts = [{|x:=0;y:=0;...|}, {|x:=1;y:=0;...|}, {|x:=0;y:=0;...|}].
           count_setting 0 0 ts = 2, count_setting 1 0 ts = 1, count_setting 1 1 ts = 0.

  FALSIFICATION: Show ts where count_setting x y ts ≠ number of matching trials.
  This would mean the filtering logic is broken.

  COMPUTATIONAL COMPLEXITY: O(|ts|) time. Linear scan.

  USED BY: expectation (divides sum by count to get average).
*)
Fixpoint count_setting (x y : nat) (ts : list Trial) : nat :=
  match ts with
  | [] => 0
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then 1 else 0)
        + count_setting x y tl
  end.

(**
  sum_setting_z: Sum trial values for trials matching settings (x,y).

  WHY: To compute E(x,y), I need the SUM of trial_value_z over matching trials.
  This is the numerator in the average: E(x,y) = (sum) / (count).

  ALGORITHM: Recursively scan trial list:
  - Empty list: return 0
  - t :: tl: If t.x = x AND t.y = y, return trial_value_z(t) + sum_setting_z x y tl.
              Else, return sum_setting_z x y tl (skip this trial).

  TERMINATION: Structural recursion on list.

  CLAIM: sum_setting_z x y ts = Σ_{t ∈ ts : t.x=x ∧ t.y=y} trial_value_z(t).

  PHYSICAL MEANING: This accumulates the correlation products for a specific
  setting pair. If you had 250 trials with (x,y) = (0,0), and 150 gave +1 and
  100 gave -1, then sum_setting_z 0 0 ts = 150 - 100 = 50.

  EXAMPLE: ts = [{|x:=0;y:=0;a:=1;b:=1|}, {|x:=0;y:=0;a:=0;b:=0|}, {|x:=1;y:=0;a:=1;b:=0|}].
           sum_setting_z 0 0 ts = trial_value_z(ts[0]) + trial_value_z(ts[1])
                                  = (+1)×(+1) + (-1)×(-1) = +1 + +1 = +2.

  FALSIFICATION: Show ts where sum_setting_z x y ts ≠ actual sum of matching
  trial values. This would mean the accumulation logic is broken.

  COMPUTATIONAL COMPLEXITY: O(|ts|) time. Linear scan.

  USED BY: expectation (divides this by count_setting to get average).
*)
Fixpoint sum_setting_z (x y : nat) (ts : list Trial) : Z :=
  match ts with
  | [] => 0%Z
  | t :: tl =>
      (if (Nat.eqb t.(t_x) x && Nat.eqb t.(t_y) y)%bool then trial_value_z t else 0%Z)
        + sum_setting_z x y tl
  end.

(**
  expectation: Compute E(x,y) = average correlation for setting pair (x,y).

  WHY: The CHSH statistic is defined as S = E(1,1) + E(1,0) + E(0,1) - E(0,0).
  expectation computes each E(x,y) term from experimental data.

  ALGORITHM:
  - Count trials with settings (x,y): n = count_setting x y ts.
  - If n = 0: No trials with these settings, return 0 (undefined, use 0 as default).
  - If n > 0: Return (sum_setting_z x y ts) / n as a rational number.

  RATIONAL ARITHMETIC: Uses Coq's Q (rationals). sum_setting_z ∈ Z, n ∈ nat.
  Division: (Z # Pos) constructor. Pos.of_succ_nat n' converts S n' to positive.

  CLAIM: If count_setting x y ts > 0, then expectation x y ts ∈ [-1, +1].
  This follows because sum_setting_z ∈ [-n, +n] (each trial contributes ±1).

  PHYSICAL MEANING: expectation is the EMPIRICAL AVERAGE of correlations. In
  quantum mechanics, E(x,y) = ⟨ψ| Â_x ⊗ B̂_y |ψ⟩ (expectation value). With finite
  trials, you get a statistical estimate of this quantum expectation.

  EXAMPLE: 100 trials with (x,y) = (1,1). 75 give +1, 25 give -1.
           sum = 75 - 25 = 50. expectation 1 1 ts = 50/100 = 1/2.

  FALSIFICATION: Show trials ts where expectation x y ts > +1 or < -1 with
  count > 0. This would violate the correlation bound (impossible given ±1 values).

  EDGE CASE: If no trials have settings (x,y), returning 0 is arbitrary. Could
  return None (option type) instead. Current choice: 0 (neutral correlation).

  USED BY: chsh (computes S from four expectation values).
*)
Definition expectation (x y : nat) (ts : list Trial) : Q :=
  match count_setting x y ts with
  | 0%nat => 0
  | S n' => (sum_setting_z x y ts) # (Pos.of_succ_nat n')
  end.

(**
  chsh: THE CHSH STATISTIC - S = E(1,1) + E(1,0) + E(0,1) - E(0,0).

  WHY: This is THE CORE FUNCTION of the file. chsh computes the Bell inequality
  violation parameter from experimental data.

  FORMULA: S = E₁₁ + E₁₀ + E₀₁ - E₀₀, where E_xy = expectation x y ts.

  THE BOUNDS (proven elsewhere, referenced here):
  - Local hidden variables: |S| ≤ 2 (this file, line 178-199)
  - Quantum mechanics: |S| ≤ 2√2 ≈ 2.828 (AlgebraicCoherence.v)
  - No-signaling: |S| ≤ 4 (BoxCHSH.v)

  PHYSICAL MEANING: S measures "how quantum" the correlations are. Classical
  correlations (local hidden variables) satisfy |S| ≤ 2. Quantum entanglement
  can achieve S = 2√2 (Tsirelson's bound). S > 2√2 would require no-signaling
  theories beyond quantum mechanics (e.g., Popescu-Rohrlich boxes).

  CLAIM: For any trial list ts, -4 ≤ chsh ts ≤ +4 (no-signaling bound).

  FALSIFICATION: Find trial list where chsh ts > 4 or < -4. This would violate
  the no-signaling bound (impossible - proven in BoxCHSH.v).

  EXPERIMENTAL VERIFICATION: Run the Thiele Machine implementing a Bell experiment.
  Extract trials via trials_of_receipts. Compute chsh. If chsh > 2, local hidden
  variables are ruled out. If chsh ≈ 2√2, quantum mechanics is confirmed. If
  chsh > 2√2, quantum mechanics is FALSIFIED.

  EXAMPLE: Ideal quantum case with maximal entanglement:
           E(1,1) ≈ 1/√2, E(1,0) ≈ 1/√2, E(0,1) ≈ 1/√2, E(0,0) ≈ -1/√2.
           S = 3/√2 - (-1/√2) = 4/√2 = 2√2 ≈ 2.828.

  HISTORICAL NOTE: Aspect et al. (1982) measured S ≈ 2.7 ± 0.05, violating local
  realism. Modern experiments achieve S ≈ 2.82 (close to Tsirelson bound).

  USED BY: CHSH verification protocols, Bell inequality tests, quantum certification.
*)
Definition chsh (ts : list Trial) : Q :=
  expectation 1 1 ts + expectation 1 0 ts + expectation 0 1 ts - expectation 0 0 ts.

(** ------------------------------------------------------------------------- *)
(** Local deterministic strategies (one response table each)

    We package a *fully explicit* local strategy as four bits A0,A1,B0,B1.
    The associated "one trial per setting" dataset must satisfy |S| ≤ 2.
*)

(**
  LocalStrategy: Deterministic local hidden variable model.

  WHY: I need to formalize "local realism" - the idea that Alice and Bob each
  have pre-determined responses based on a hidden variable λ. A LocalStrategy
  is ONE INSTANCE of such a λ.

  STRUCTURE:
  - a0: Alice's response when she measures setting 0 (outcome ∈ {0,1})
  - a1: Alice's response when she measures setting 1 (outcome ∈ {0,1})
  - b0: Bob's response when he measures setting 0 (outcome ∈ {0,1})
  - b1: Bob's response when he measures setting 1 (outcome ∈ {0,1})

  LOCAL REALISM: Alice's responses {a0, a1} depend ONLY on the hidden variable λ,
  NOT on Bob's choice of setting or outcome. Bob's responses {b0, b1} depend ONLY
  on λ, NOT on Alice. This is Einstein's "spooky action at a distance" - he
  insisted correlations come from pre-existing properties (λ), not instantaneous
  influence.

  PHYSICAL MEANING: LocalStrategy is a "instruction sheet" given to Alice and Bob
  before they separate. "If you measure 0, say a0. If you measure 1, say a1."
  The correlations arise because they both received correlated instruction sheets
  (from shared source with hidden variable λ).

  FINITE ENUMERATION: There are 2^4 = 16 possible LocalStrategies (each bit
  is 0 or 1). The theorem local_strategy_chsh_between_neg2_2 (line 178) checks
  ALL 16 and verifies |S| ≤ 2 for each.

  EXAMPLE: s = {| a0 := 0; a1 := 1; b0 := 0; b1 := 1 |}.
           If (x,y) = (1,0), outcomes are (a1, b0) = (1, 0). Correlation = -1.

  FALSIFICATION: Construct a LocalStrategy where |chsh_local_z s| > 2. This
  would violate Bell's theorem (proven impossible - see line 178-199).

  USED BY: trial_of_local, trials_of_local, local_bits_ok, chsh_local_z,
  local_strategy_chsh_between_neg2_2.
*)
Record LocalStrategy : Type := {
  a0 : nat;
  a1 : nat;
  b0 : nat;
  b1 : nat;
}.

(**
  trial_of_local: Generate one trial from local strategy for settings (x,y).

  WHY: Given a LocalStrategy s and settings (x,y), I need to compute the
  deterministic outcomes (a,b) that this strategy produces.

  ALGORITHM:
  - a = if x = 0 then s.a0 else s.a1 (Alice's response for her setting)
  - b = if y = 0 then s.b0 else s.b1 (Bob's response for his setting)
  - Return Trial {| t_x := x; t_y := y; t_a := a; t_b := b |}

  DETERMINISM: For fixed s, same (x,y) always gives same (a,b). No randomness.

  PHYSICAL MEANING: This models the "instruction sheet" execution. Alice looks
  up x in her sheet, sees "output a". Bob looks up y, sees "output b". They
  don't communicate (spacelike separated), but their outputs are correlated
  because the sheets were prepared together (shared hidden variable λ).

  EXAMPLE: s = {| a0 := 1; a1 := 0; b0 := 1; b1 := 1 |}.
           trial_of_local s 0 1 = {| t_x := 0; t_y := 1; t_a := 1; t_b := 1 |}.
           (Alice measures 0 → output a0 = 1. Bob measures 1 → output b1 = 1.)

  FALSIFICATION: Show s, x, y where trial_of_local produces different trial on
  re-evaluation (non-determinism). This would mean the function is not pure.

  USED BY: trials_of_local (generates all 4 setting combinations).
*)
Definition trial_of_local (s : LocalStrategy) (x y : nat) : Trial :=
  {| t_x := x;
     t_y := y;
     t_a := if Nat.eqb x 0 then s.(a0) else s.(a1);
     t_b := if Nat.eqb y 0 then s.(b0) else s.(b1) |}.

(**
  trials_of_local: Generate complete trial dataset for local strategy.

  WHY: To compute CHSH for a LocalStrategy, I need trials for ALL FOUR setting
  combinations: (0,0), (0,1), (1,0), (1,1). This function generates them.

  ALGORITHM: Return [ trial_of_local s 0 0;
                       trial_of_local s 0 1;
                       trial_of_local s 1 0;
                       trial_of_local s 1 1 ].

  CLAIM: trials_of_local s has exactly 4 elements, one per setting combination.

  PHYSICAL MEANING: This is the "ideal" experimental dataset for hidden variable
  model s. In a real experiment, you'd run many trials and statistically estimate
  E(x,y). Here, we use the deterministic strategy directly (one trial per setting
  suffices because outcomes are deterministic).

  EXAMPLE: s = {| a0 := 0; a1 := 1; b0 := 1; b1 := 0 |}.
           trials_of_local s = [ {|x:=0;y:=0;a:=0;b:=1|},  (* E₀₀ = -1 *)
                                  {|x:=0;y:=1;a:=0;b:=0|},  (* E₀₁ = +1 *)
                                  {|x:=1;y:=0;a:=1;b:=1|},  (* E₁₀ = +1 *)
                                  {|x:=1;y:=1;a:=1;b:=0|} ] (* E₁₁ = -1 *)
           S = E₁₁ + E₁₀ + E₀₁ - E₀₀ = -1 + 1 + 1 - (-1) = +2.

  FALSIFICATION: Show s where trials_of_local s has ≠ 4 trials, or missing some
  setting combination. This would mean the list construction is broken.

  USED BY: count_setting_trials_of_local, expectation_trials_of_local,
  local_strategy_chsh_between_neg2_2 (computes CHSH from this list).
*)
Definition trials_of_local (s : LocalStrategy) : list Trial :=
  [ trial_of_local s 0 0;
    trial_of_local s 0 1;
    trial_of_local s 1 0;
    trial_of_local s 1 1 ].

(**
  local_bits_ok: Validation predicate for LocalStrategy.

  WHY: LocalStrategy fields should be 0 or 1 (measurement outcomes). I need a
  predicate to express "all fields are valid bits".

  CLAIM: local_bits_ok s ↔ s.a0 ∈ {0,1} ∧ s.a1 ∈ {0,1} ∧ s.b0 ∈ {0,1} ∧ s.b1 ∈ {0,1}.

  IMPLEMENTATION: Conjunction of four is_bit checks (defined in VMStep.v).

  PHYSICAL MEANING: Measurement outcomes are binary (yes/no, up/down, 0/1). A
  strategy with outcomes outside {0,1} is physically meaningless.

  USED BY: local_strategy_chsh_between_neg2_2 (assumes local_bits_ok to prove
  bound). The proof exhaustively checks all 2^4 = 16 valid strategies.
*)
Definition local_bits_ok (s : LocalStrategy) : Prop :=
  is_bit s.(a0) = true /\ is_bit s.(a1) = true /\
  is_bit s.(b0) = true /\ is_bit s.(b1) = true.

(**
  is_bit_true_cases: If is_bit n = true, then n ∈ {0, 1}.

  WHY: The is_bit predicate (from VMStep.v) enforces n ∈ {0,1}. I need to EXTRACT
  this knowledge as a disjunction for case analysis in proofs.

  CLAIM: ∀ n. is_bit n = true → (n = 0 ∨ n = 1).

  PROOF STRATEGY:
  1. Unfold is_bit definition (checks if n ≤ 1).
  2. Case split on n:
     - n = 0: Left disjunct, reflexivity.
     - n = S n': Case split on n':
       * n' = 0 (so n = 1): Right disjunct, reflexivity.
       * n' = S n'' (so n ≥ 2): Contradiction with is_bit = true (discriminate).

  PHYSICAL MEANING: Measurement outcomes are discrete {0,1}, not continuous.
  This lemma captures that discreteness formally.

  FALSIFICATION: Find n where is_bit n = true but n ∉ {0,1}. This would mean
  the is_bit definition is wrong.

  USED BY: local_strategy_chsh_between_neg2_2 (applies this to each strategy
  field to enable exhaustive enumeration).
*)
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

(**
  count_setting_trials_of_local: Each setting appears exactly once in trials_of_local.

  WHY: I need to prove that trials_of_local s produces exactly ONE trial for each
  setting combination (x,y). This is necessary to show expectation simplifies
  correctly.

  CLAIM: ∀ s, x ∈ {0,1}, y ∈ {0,1}. count_setting x y (trials_of_local s) = 1.

  PROOF STRATEGY:
  1. Assume x ∈ {0,1} (disjunction Hx) and y ∈ {0,1} (disjunction Hy).
  2. Case split on Hx × Hy (4 cases: (0,0), (0,1), (1,0), (1,1)).
  3. Each case: Substitute x, y values. Compute trials_of_local explicitly (vm_compute).
  4. Compute count_setting by evaluating list filters. Result = 1 in all cases.
     Conclude by reflexivity.

  PHYSICAL MEANING: The "ideal" dataset for a deterministic strategy has no
  repeated settings - each (x,y) appears once.

  FALSIFICATION: Find s, x, y where count_setting x y (trials_of_local s) ≠ 1.
  This would mean trials_of_local doesn't generate all 4 combinations exactly once.

  USED BY: expectation_trials_of_local (simplifies expectation denominator to 1).
*)
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

(**
  expectation_trials_of_local: Expectation simplifies to sum when count = 1.

  WHY: For deterministic strategies, expectation x y (trials_of_local s) should
  equal the single trial value (since there's exactly 1 trial per setting).

  CLAIM: ∀ s, x ∈ {0,1}, y ∈ {0,1}.
         expectation x y (trials_of_local s) = (sum_setting_z x y (trials_of_local s)) # 1.

  PROOF STRATEGY:
  1. Unfold expectation definition.
  2. Rewrite count_setting using count_setting_trials_of_local (count = 1).
  3. Simplify match: S 0 branch gives (sum_setting_z ...) # (Pos.of_succ_nat 0) = sum # 1.
  4. Conclude by reflexivity.

  PHYSICAL MEANING: For deterministic strategies, the "average" correlation is
  just the single correlation value (no statistical averaging needed).

  EXAMPLE: s with trial_of_local s 1 0 = {|a:=1; b:=0|}.
           expectation 1 0 (trials_of_local s) = (+1)×(-1) # 1 = -1.

  FALSIFICATION: Find s, x, y where expectation ≠ (sum # 1). This would mean
  count_setting ≠ 1 (contradicts count_setting_trials_of_local).

  USED BY: Local CHSH bound proof (simplifies expectation calculations).
*)
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

(** Classical CHSH bound for deterministic local strategies.

    Proof is by finite enumeration of the 16 possible response tables.
*)

(**
  chsh_local_z: Compute CHSH statistic directly from LocalStrategy in Z.

  WHY: For deterministic strategies, I can compute CHSH WITHOUT running trials -
  just use the strategy bits directly. chsh_local_z is the closed-form formula.

  FORMULA: S = A₁·B₁ + A₁·B₀ + A₀·B₁ - A₀·B₀, where:
  - A_x = sign_z(s.a_x) ∈ {-1, +1}
  - B_y = sign_z(s.b_y) ∈ {-1, +1}

  DERIVATION: From chsh definition:
  S = E(1,1) + E(1,0) + E(0,1) - E(0,0)
    = A₁·B₁ + A₁·B₀ + A₀·B₁ - A₀·B₀ (since each E(x,y) is one trial).

  CLAIM: ∀ s. local_bits_ok s → -2 ≤ chsh_local_z s ≤ +2.

  PHYSICAL MEANING: This is Bell's inequality in closed form. For ANY deterministic
  local strategy (hidden variable model), the CHSH parameter is bounded by ±2.
  Quantum entanglement can achieve 2√2 > 2, violating this bound.

  EXAMPLE: s = {| a0 := 0; a1 := 1; b0 := 1; b1 := 1 |}.
           A₀ = -1, A₁ = +1, B₀ = +1, B₁ = +1.
           S = (+1)(+1) + (+1)(+1) + (-1)(+1) - (-1)(+1)
             = +1 + 1 - 1 - (-1) = +2.

  FALSIFICATION: Find s with local_bits_ok s where |chsh_local_z s| > 2. This
  would violate Bell's theorem (impossible - proven in next theorem line 178).

  USED BY: local_strategy_chsh_between_neg2_2 (proves bound by exhaustive check).
*)
Definition chsh_local_z (s : LocalStrategy) : Z :=
  let A0 := sign_z s.(a0) in
  let A1 := sign_z s.(a1) in
  let B0 := sign_z s.(b0) in
  let B1 := sign_z s.(b1) in
  (A1 * B1 + A1 * B0 + A0 * B1 - A0 * B0)%Z.

(**
  local_strategy_chsh_between_neg2_2: THE BELL INEQUALITY THEOREM (local bound).

  THEOREM: For any deterministic local strategy s with valid bits,
           -2 ≤ chsh_local_z s ≤ +2.

  WHY THIS MATTERS: This is Bell's 1964 theorem, proven by EXHAUSTIVE ENUMERATION.
  There are 2^4 = 16 possible local strategies. I check ALL 16 and verify the
  bound holds for each. No probabilistic averaging, no continuous parameters -
  just finite case analysis.

  CLAIM: ∀ s. local_bits_ok s → (-2 ≤ chsh_local_z s ≤ +2)%Z.

  PROOF STRATEGY:
  1. Destructure s = {| a0 := A0; a1 := A1; b0 := B0; b1 := B1 |}.
  2. Extract Hbits: each field satisfies is_bit = true.
  3. Apply is_bit_true_cases to each field: A0 ∈ {0,1}, A1 ∈ {0,1}, etc.
  4. Case split on all 16 combinations (4 nested destruct, each field 0 or 1).
  5. For each case:
     a. Define v = chsh_local_z {| ...concrete values... |}.
     b. Compute v using vm_compute (evaluates sign_z, arithmetic).
     c. Result: v = +2 or v = -2 (proven by assert + vm_compute).
     d. Rewrite goal using v value. Apply lia to verify -2 ≤ v ≤ +2.

  THE 16 CASES (exhaustive):
  All strategies yield S ∈ {-2, +2}. None exceed the bound.

  PHYSICAL INTERPRETATION: Local realism (Einstein's "elements of reality") CANNOT
  reproduce quantum correlations exceeding S = 2. Quantum mechanics achieves
  S = 2√2 ≈ 2.828, experimentally confirmed. This proves quantum mechanics is
  NOT a local hidden variable theory.

  HISTORICAL CONTEXT: Bell (1964) derived this algebraically. Clauser et al. (1969)
  formulated the CHSH version. Aspect et al. (1982) experimentally confirmed
  S > 2, ruling out local realism. This proof formalizes Bell's original argument.

  FALSIFICATION: Find a 17th strategy (outside the 16 cases) where the bound fails.
  Impossible - the case analysis is complete (each bit has exactly 2 values).

  DEPENDENCIES: Requires is_bit_true_cases (field extraction), chsh_local_z
  (closed-form formula), vm_compute (symbolic evaluation), lia (arithmetic bounds).

  USED BY: local_strategy_chsh_abs_le_2_z (corollary using absolute value).
*)
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

(**
  local_strategy_chsh_abs_le_2_z: COROLLARY - local bound in absolute value form.

  COROLLARY: For any deterministic local strategy s with valid bits,
             |chsh_local_z s| ≤ 2.

  WHY: The absolute value form is often more convenient for stating bounds.
  This follows immediately from local_strategy_chsh_between_neg2_2.

  CLAIM: ∀ s. local_bits_ok s → (Z.abs (chsh_local_z s) ≤ 2)%Z.

  PROOF STRATEGY:
  1. Apply local_strategy_chsh_between_neg2_2: get -2 ≤ v ≤ +2.
  2. Apply Z.abs_le: |v| ≤ 2 ↔ -2 ≤ v ≤ +2.
  3. Conclude by exact match.

  PHYSICAL MEANING: Same as main theorem, but using |S| ≤ 2 notation (common
  in physics literature). Quantum violations are stated as |S| = 2√2 > 2.

  COMPARISON TO QUANTUM BOUND: This proves |S_classical| ≤ 2. AlgebraicCoherence.v
  proves |S_quantum| ≤ 2√2. The gap (2√2 - 2 ≈ 0.828) is the "quantum advantage"
  in Bell tests.

  FALSIFICATION: Same as main theorem - find strategy where |S| > 2.

  DIRECT CONSEQUENCE OF: local_strategy_chsh_between_neg2_2 (line 178).

  USED BY: CHSH verification protocols, quantum certification schemes.
*)
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
