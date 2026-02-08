From Coq Require Import List Lia Arith.PeanoNat.

From Kernel Require Import Definitions.
From Kernel Require Import VMStep.
From Kernel Require Import VMState.
From Kernel Require Import EntropyImpossibility.

Import ListNotations.

(** * KernelTOE: minimal no-go theorems

    WHY THIS FILE EXISTS:
    I claim the weight laws (empty, sequential, disjoint_commutes) from
    Definitions.v are NOT sufficient to uniquely determine μ-cost. There
    exists an INFINITE FAMILY of different weight functions, all satisfying
    the laws, all giving different costs for the same trace.

    THE PROOF STRATEGY:
    Construct w_scale(k)(t) = k * length(t) for any k ∈ ℕ. This family has:
    1. Every w_scale(k) satisfies weight_laws (proven in w_scale_laws)
    2. Different k give different costs (w_scale(1) ≠ w_scale(2))
    3. Therefore, the laws don't force a unique weight function

    WHY THIS MATTERS:
    This proves μ-cost is NOT derivable from locality/additivity alone. You
    MUST add extra structure (singleton_uniform + unit_normalization) to pin
    down the scale. Without these, you get a 1-parameter family (any k works).

    THE POSITIVE RESULT (Weight_Unique_Under_UniformSingletons):
    If you ADD:
    - singleton_uniform: all single instructions cost the same
    - unit_normalization: w([halt 0]) = 1 (fixes the scale)
    THEN w(t) = length(t) is uniquely determined (proven).

    PHYSICAL INTERPRETATION:
    The weight laws say "cost is conserved and local", but they don't say
    HOW MUCH. You need symmetry (singleton_uniform: all ops cost equally)
    plus scale-fixing (unit_normalization: pick units) to get a unique answer.
    This is like measuring distances: rotation + scale = length, but without
    scale choice, you only get "proportional to length".

    FALSIFICATION:
    Prove the weight laws ALONE (without singleton_uniform or unit_normalization)
    uniquely determine w(t). This would contradict CompositionalWeightFamily_Infinite,
    which exhibits infinitely many solutions. Or find an error in the w_scale
    proofs (they're simple arithmetic, but worth checking).

    This is a "negative" result (impossibility) - it tells us what we CAN'T do
    without extra assumptions. The positive side: with those assumptions, we
    get uniqueness (proven in Weight_Unique_Under_UniformSingletons).
*)

(** ** A one-parameter family of weights preserving all explicit laws *)

(** w_scale: Scaled weight function parameterized by k

    DEFINITION: w_scale(k)(t) = k · length(t) for any natural number k.

    STRUCTURE: For each k ∈ ℕ, this defines a weight function that multiplies
    trace length by k. Examples:
    - w_scale(0)(t) = 0 (everything costs zero - degenerate)
    - w_scale(1)(t) = length(t) (our actual μ-cost)
    - w_scale(2)(t) = 2·length(t) (double-cost model)
    - w_scale(k)(t) = k·length(t) (k-times-cost model)

    WHY THIS MATTERS: This is a COUNTEREXAMPLE to uniqueness. If the weight
    laws (empty, sequential, disjoint_commutes) were sufficient to uniquely
    determine μ-cost, there would be only ONE weight function satisfying them.
    But w_scale(k) gives INFINITELY MANY (one for each k), all satisfying the
    laws but giving different costs.

    PHYSICAL INTERPRETATION: The weight laws say "cost is additive and local"
    but don't specify the UNIT. It's like saying "distance is additive" without
    saying whether you measure in meters, feet, or light-years. Every unit
    choice (k) gives a valid "distance" (weight), all proportional to length.

    To fix the unit, you need TWO additional constraints:
    1. singleton_uniform: all single instructions cost the same (symmetry)
    2. unit_normalization: w([halt 0]) = 1 (sets the scale to k=1)

    These constraints force k = 1, making w_scale(1) = length the unique solution.

    RELATION TO PHYSICS: This is analogous to gauge freedom in physics. The
    physical laws (Maxwell's equations) don't uniquely fix the electromagnetic
    potential A_μ - you can add any gradient ∇λ (gauge transformation). To
    make predictions, you pick a gauge (like Lorenz gauge). Here, weight_laws
    don't fix the gauge (k), so you pick a gauge (singleton_uniform + unit_norm).

    FALSIFICATION: Prove that weight_laws alone force k = 1 without singleton_uniform
    or unit_normalization. This would contradict the explicit construction of
    w_scale(k) for k ≠ 1, which satisfies weight_laws (proven in w_scale_laws).
*)
Definition w_scale (k : nat) : Weight :=
  fun t => k * length t.

(** w_scale_empty: Empty trace has zero weight (for any k)

    LEMMA: w_scale(k)([]) = 0 for all k.

    PROOF: w_scale(k)([]) = k · length([]) = k · 0 = 0 by arithmetic. QED.

    WHY THIS WORKS: The empty trace has length 0. Multiplying by any k gives 0.
    This shows w_scale respects the weight_empty law: no operations = no cost.

    PHYSICAL INTERPRETATION: Doing nothing costs nothing, regardless of your
    cost scale. Whether you measure in μ-units, double-μ-units, or k-μ-units,
    zero operations = zero cost. This is universally true.

    FALSIFICATION: Find k where w_scale(k)([]) ≠ 0. This would violate basic
    arithmetic (k · 0 = 0 for all k).
*)
Lemma w_scale_empty : forall k, weight_empty (w_scale k).
Proof.
  intro k. unfold weight_empty, w_scale. simpl. lia.
Qed.

(** w_scale_sequential: Costs add under concatenation (for any k)

    LEMMA: w_scale(k)(t1 ++ t2) = w_scale(k)(t1) + w_scale(k)(t2) for all k.

    PROOF:
    w_scale(k)(t1 ++ t2) = k · length(t1 ++ t2)   (by definition)
                         = k · (length(t1) + length(t2))  (by app_length)
                         = k · length(t1) + k · length(t2)  (distributivity)
                         = w_scale(k)(t1) + w_scale(k)(t2)  (by definition)
    QED.

    WHY THIS WORKS: Concatenation adds lengths. Multiplication distributes
    over addition. Therefore w_scale respects additivity for any k.

    PHYSICAL INTERPRETATION: Running two programs sequentially costs the sum
    of their individual costs. This is independent of the cost scale k - if
    one program costs 3 and another costs 5, the total is 8, whether you
    measure in μ-units (k=1), double-μ (k=2), or k-μ.

    This is the CORE of locality: costs don't interact, they just add. True
    for any k, proving it's not a special property of k=1.

    FALSIFICATION: Find k, t1, t2 where w_scale(k)(t1 ++ t2) ≠ w_scale(k)(t1) + w_scale(k)(t2).
    This would violate distributivity of multiplication over addition.
*)
Lemma w_scale_sequential : forall k, weight_sequential (w_scale k).
Proof.
  intro k. unfold weight_sequential, w_scale.
  intros t1 t2. rewrite app_length. lia.
Qed.

(** w_scale_disjoint_commutes: Disjoint traces can be reordered (for any k)

    LEMMA: If t1, t2 are disjoint, w_scale(k)(t1 ++ t2) = w_scale(k)(t2 ++ t1).

    PROOF: Both sides = k · (length(t1) + length(t2)) = k · (length(t2) + length(t1))
    by commutativity of addition. Disjointness is not even used! Length is
    commutative regardless. QED.

    WHY THIS WORKS: Concatenation preserves length regardless of order. Since
    w_scale only depends on length (not structure), reordering doesn't change cost.

    PHYSICAL INTERPRETATION: If two operations don't interfere (disjoint registers),
    running them in either order costs the same. This is locality + commutativity.
    The k-scaling doesn't affect this - it's true for any cost scale.

    SUBTLETY: The full weight_disjoint_commutes requires disjointness as a premise,
    but for w_scale, it's always true (even for non-disjoint traces) because
    w_scale ignores trace content and only looks at length. This is actually
    STRONGER than required - w_scale over-satisfies the law.

    FALSIFICATION: Find k, t1, t2 where w_scale(k)(t1 ++ t2) ≠ w_scale(k)(t2 ++ t1).
    This would violate commutativity of addition (length(t1) + length(t2) ≠ length(t2) + length(t1)).
*)
Lemma w_scale_disjoint_commutes : forall k, weight_disjoint_commutes (w_scale k).
Proof.
  intro k. unfold weight_disjoint_commutes, w_scale.
  intros t1 t2 _.
  rewrite !app_length. lia.
Qed.

(** w_scale_laws: w_scale(k) satisfies all weight laws for any k

    THEOREM: For every k ∈ ℕ, w_scale(k) satisfies weight_laws.

    PROOF: Combine the three lemmas above:
    - weight_empty: w_scale_empty
    - weight_sequential: w_scale_sequential
    - weight_disjoint_commutes: w_scale_disjoint_commutes
    All proven, so weight_laws holds. QED.

    WHY THIS IS THE KEY RESULT: This proves the weight laws are NOT sufficient
    to pin down μ-cost uniquely. Every k gives a different cost function:
    - k=1: w([halt 0]) = 1
    - k=2: w([halt 0]) = 2
    - k=100: w([halt 0]) = 100

    All satisfy the same laws! This means weight_laws is underdetermined - you
    need additional constraints (singleton_uniform, unit_normalization) to get
    uniqueness.

    PHYSICAL INTERPRETATION: The laws specify the STRUCTURE of cost (additive,
    local) but not the SCALE. It's like measuring temperature: Celsius and
    Fahrenheit both satisfy "additive" (ΔT(A+B) = ΔT(A) + ΔT(B)) and "local"
    (thermometers don't interact), but give different numbers. You need to
    fix the scale (water freezes at 0°C, boils at 100°C) to get uniqueness.

    Here: weight_laws = "structure of cost"
          singleton_uniform = "all ops cost equally" (like "uniform thermal capacity")
          unit_normalization = "halt costs 1" (like "water freezes at 0°C")
    Together, these force k=1, making μ = length unique.

    RELATION TO NON-UNIQUENESS: CompositionalWeightFamily_Infinite (below) uses
    this to exhibit infinitely many distinct weight functions all satisfying
    weight_laws. This proves impossibility of deriving μ from laws alone.

    FALSIFICATION: Prove weight_laws contradicts w_scale(k) for some k ≠ 1.
    This would show the laws are STRONGER than I claimed - they secretly encode
    the scale. But the proofs above are trivial arithmetic, hard to refute.
*)
Lemma w_scale_laws : forall k, weight_laws (w_scale k).
Proof.
  intro k.
  unfold weight_laws.
  split.
  - apply w_scale_empty.
  - split.
    + apply w_scale_sequential.
    + apply w_scale_disjoint_commutes.
Qed.

(** CompositionalWeightFamily_Infinite: INFINITELY MANY VALID WEIGHT FUNCTIONS

    THEOREM: There exists an infinite family of weight functions {w(k) | k ∈ ℕ},
    where every member satisfies weight_laws, but different members disagree
    on costs.

    CLAIM: The weight laws do NOT uniquely determine μ-cost. There are infinitely
    many distinct solutions.

    PROOF STRUCTURE:
    1. Exhibit the family: w = w_scale (already defined)
    2. Prove every member satisfies laws: ∀k. weight_laws(w_scale(k)) ✓ (w_scale_laws)
    3. Prove members are distinct: ∀k1≠k2. ∃t. w_scale(k1)(t) ≠ w_scale(k2)(t)
       Witness: t = [halt 0]
       w_scale(k1)([halt 0]) = k1 · 1 = k1
       w_scale(k2)([halt 0]) = k2 · 1 = k2
       If k1 ≠ k2, then k1 ≠ k2 (trivially), so w_scale(k1)(t) ≠ w_scale(k2)(t) ✓
    QED.

    WHY THIS IS A "NO-GO" THEOREM:
    This proves you CANNOT derive μ-cost uniquely from weight_laws alone. Any
    claim that "μ is forced by locality and additivity" is FALSE - there are
    infinitely many local, additive cost functions.

    To get uniqueness, you MUST add structure beyond weight_laws. The sufficient
    structure is:
    - singleton_uniform (all single instructions cost equally)
    - unit_normalization (fix the scale: w([halt 0]) = 1)

    These constraints select k=1 from the infinite family, making μ = length unique.

    PHYSICAL INTERPRETATION:
    Weight laws = "cost is extensive (proportional to system size)"
    Uniqueness requires = "cost is also intensive (per-operation cost is fixed)"

    Extensive property example: mass of a composite system = sum of masses (additive).
    But this doesn't tell you the UNIT (grams, pounds, kilograms). You need to
    fix the unit (e.g., "1 gram = mass of 1 cm³ water at 4°C") to get uniqueness.

    Here: extensive = weight_laws (additivity)
          unit-fixing = singleton_uniform + unit_normalization
    Both needed for uniqueness.

    ALTERNATIVE INTERPRETATION (gauge freedom):
    The weight laws have a U(1) symmetry: w → k·w preserves the laws. This is
    a "gauge freedom" - physical predictions (whether cost is zero or nonzero)
    are gauge-invariant, but the numerical value is gauge-dependent. To make
    predictions, you "fix the gauge" by choosing k=1.

    RELATION TO INCOMPLETENESS:
    This is conceptually similar to Gödel's incompleteness: the axioms (weight_laws)
    don't pin down the model (weight function) uniquely. There are non-standard
    models (k ≠ 1) satisfying the axioms but disagreeing with the intended model
    (k = 1). To get the intended model, you need additional axioms (singleton_uniform).

    FALSIFICATION:
    Prove weight_laws forces k=1 without additional axioms. This would mean
    w_scale(k) doesn't actually satisfy weight_laws for k ≠ 1, contradicting
    w_scale_laws (which is a simple proof, hard to refute).

    Or show the family is FINITE (not infinite). This would mean only finitely
    many k work, suggesting the laws are stricter than I claimed. But k ranges
    over all ℕ (infinite), and the proofs work for all k, so this seems impossible.
*)
Theorem CompositionalWeightFamily_Infinite :
  exists w : nat -> Weight,
    (forall k, weight_laws (w k)) /\
    (forall k1 k2, k1 <> k2 -> exists t, w k1 t <> w k2 t).
Proof.
  exists w_scale.
  split.
  - intro k. apply w_scale_laws.
  - intros k1 k2 Hneq.
    exists [instr_halt 0].
    unfold w_scale. simpl.
    (* k1*1 <> k2*1 *)
    intro Heq. apply Hneq.
    lia.
Qed.

(** ** Stronger no-go statement: no unique weight is forced *)

(** KernelNoGo_UniqueWeight_FailsP: Statement of non-uniqueness

    DEFINITION: There exist two distinct weight functions w1, w2 that both
    satisfy weight_laws but disagree on some trace.

    FORMULA: ∃w1,w2. weight_laws(w1) ∧ weight_laws(w2) ∧ (∃t. w1(t) ≠ w2(t))

    WHY THIS MATTERS: This is the MINIMAL no-go statement. It doesn't require
    an infinite family (like CompositionalWeightFamily_Infinite), just TWO
    distinct solutions. If uniqueness held, there would be at most ONE weight
    function satisfying the laws. This proves there are AT LEAST TWO.

    PHYSICAL INTERPRETATION: The weight laws are UNDERDETERMINED - they allow
    multiple solutions. This is not a bug, it's a feature: the laws specify
    the structure (additivity, locality) without specifying the scale (units).
    Both are necessary for a complete specification.

    CONTRAST WITH CompositionalWeightFamily_Infinite:
    - Infinite: "There are infinitely many solutions" (stronger)
    - FailsP: "There are at least two solutions" (weaker, easier to prove)

    Both are no-go theorems, but Infinite gives more information (size of
    the solution space). FailsP is the minimal obstruction to uniqueness.

    FALSIFICATION: Prove weight_laws forces a unique weight. This would make
    FailsP false (there's at most one solution, not at least two). But we have
    explicit counterexamples (w_scale(1), w_scale(2)), so this is impossible.
*)
Definition KernelNoGo_UniqueWeight_FailsP : Prop :=
  exists w1 w2,
    weight_laws w1 /\
    weight_laws w2 /\
    (exists t, w1 t <> w2 t).

(** KernelNoGo_UniqueWeight_Fails: PROOF OF NON-UNIQUENESS

    THEOREM: The weight laws do not force a unique weight function.

    CLAIM: There exist w1, w2 satisfying weight_laws with w1 ≠ w2.

    PROOF:
    1. Let w1 = w_scale(1), w2 = w_scale(2)
    2. Prove weight_laws(w1): apply w_scale_laws ✓
    3. Prove weight_laws(w2): apply w_scale_laws ✓
    4. Find witness trace: t = [halt 0]
    5. Compute: w1([halt 0]) = 1·1 = 1, w2([halt 0]) = 2·1 = 2
    6. Verify: 1 ≠ 2 ✓
    QED.

    WHY THIS IS STRONGER THAN EXISTENCE:
    CompositionalWeightFamily_Infinite says "there exists a family". This theorem
    says "non-uniqueness HOLDS" (constructively). We exhibit two specific weights
    (k=1, k=2) and prove they differ. No existential quantifier left unwitnessed.

    PHYSICAL INTERPRETATION:
    Measuring cost in "μ-units" (k=1) vs "double-μ-units" (k=2) gives different
    numerical values but the same structure. The laws don't care about units,
    so both are valid. Uniqueness requires fixing units (unit_normalization).

    RELATION TO GAUGE THEORIES:
    In electromagnetism, Maxwell's equations don't uniquely fix the potential
    A_μ. You can shift A_μ → A_μ + ∂_μλ (gauge transformation) without changing
    physics. To make predictions, you choose a gauge (Lorenz, Coulomb, etc.).

    Here: weight_laws don't uniquely fix w. You can scale w → k·w (gauge
    transformation) without changing the structure. To make predictions, you
    choose a gauge (singleton_uniform + unit_normalization), forcing k=1.

    FALSIFICATION:
    Prove w_scale(1) and w_scale(2) actually compute the same value on [halt 0].
    This would mean 1 = 2 (arithmetic impossibility). Or prove one of them
    doesn't satisfy weight_laws (contradicts w_scale_laws, a simple proof).
*)
Theorem KernelNoGo_UniqueWeight_Fails : KernelNoGo_UniqueWeight_FailsP.
Proof.
  (* Pick two distinct points from the infinite family. *)
  exists (w_scale 1), (w_scale 2).
  split.
  - apply w_scale_laws.
  - split.
    + apply w_scale_laws.
    + exists [instr_halt 0].
      unfold w_scale. simpl. discriminate.
Qed.

(** ** Explicit "extra structure" sufficient to restore uniqueness

    If we add:
      - singleton uniformity (all single-instruction traces have equal weight)
      - unit normalization (pin that singleton to 1)
    then any law-abiding weight is forced to be length.
*)

(** Weight_Unique_Under_UniformSingletons: THE POSITIVE UNIQUENESS THEOREM

    THEOREM: If w satisfies weight_laws + singleton_uniform + unit_normalization,
    then w(t) = length(t) for all traces t.

    CLAIM: The three constraints together UNIQUELY determine μ-cost as trace length.

    PROOF TECHNIQUE (induction on trace structure):
    - Base case: w([]) = 0 by weight_empty. length([]) = 0. Equal ✓
    - Inductive case: Assume w(rest) = length(rest) (IH). Prove w(i::rest) = length(i::rest).
      Step 1: Rewrite i::rest as [i]++rest (cons is append of singleton)
      Step 2: Apply weight_sequential: w([i]++rest) = w([i]) + w(rest)
      Step 3: Apply singleton_uniform: w([i]) = w([halt 0]) (all singletons equal)
      Step 4: Apply unit_normalization: w([halt 0]) = 1
      Step 5: Apply IH: w(rest) = length(rest)
      Step 6: Combine: w(i::rest) = 1 + length(rest) = length(i::rest) ✓
    QED.

    WHY THREE CONSTRAINTS ARE NECESSARY:
    - weight_laws alone: infinitely many solutions (proven above)
    - weight_laws + singleton_uniform: still ambiguous (which value for singletons?)
    - weight_laws + unit_normalization: not enough (doesn't force uniformity)
    - All three together: UNIQUE solution (length)

    This is MINIMAL sufficiency: you need all three, no subset is enough.

    PHYSICAL INTERPRETATION:
    1. weight_laws = "cost is extensive and local" (structure)
    2. singleton_uniform = "all operations are equivalent" (symmetry)
    3. unit_normalization = "one operation costs 1 μ-unit" (scale)

    Together: "cost = number of operations, each costing 1 μ-unit, combining additively."
    This uniquely defines μ = length.

    WHY SINGLETON_UNIFORM:
    This says: halt, add, load, store, etc. all cost the same (1 μ-unit). This
    is a SYMMETRY assumption - all instructions are created equal in terms of
    information cost. Without it, you could have non-uniform costs (halt costs 1,
    add costs 2, etc.), breaking uniqueness.

    Physically: μ-cost measures "state space reduction" (how much search space
    is traversed). Every instruction transitions between states, reducing search
    space by one step. Hence all cost equally. This is not a postulate - it's
    derivable from state space structure (proven in MuInitiality.v).

    WHY UNIT_NORMALIZATION:
    This fixes the scale: "1 instruction = 1 μ-unit". Without it, you could
    scale by any factor k (as w_scale shows). Choosing k=1 gives natural units.

    RELATION TO NO-GO THEOREMS:
    - NoGo says: weight_laws insufficient
    - Positive says: weight_laws + singleton_uniform + unit_normalization sufficient
    - Together: characterize EXACTLY what's needed for uniqueness

    FALSIFICATION:
    Find w satisfying all three constraints but w ≠ length. This would mean
    the proof has an error (unlikely - it's straightforward induction on lists).
    Or show weight_laws + singleton_uniform + unit_normalization is inconsistent
    (has no solutions), contradicting the fact that w = length satisfies all three.
*)
Theorem Weight_Unique_Under_UniformSingletons :
  forall w,
    weight_laws w ->
    singleton_uniform w ->
    unit_normalization w ->
    forall t, w t = length t.
Proof.
  intros w [Hempty [Hseq _]] Hunif Hunit.
  induction t as [|i rest IH].
  - rewrite Hempty. reflexivity.
  - (* w (i::rest) = w([i]++rest) = w[i] + w rest = 1 + w rest *)
    replace (i :: rest) with ([i] ++ rest) by reflexivity.
    rewrite Hseq.
    specialize (Hunif i (instr_halt 0)).
    simpl in Hunif.
    rewrite Hunif.
    rewrite Hunit.
    rewrite IH.
    simpl. lia.
Qed.

(** ** Entropy obstruction: Dedekind-infinite observational classes *)

(** region_equiv_class_dedekind_infinite: OBSERVATIONAL CLASSES ARE INFINITE

    LEMMA: For any VM state s, there exists an injective function f : ℕ → VMState
    where every f(n) is observationally equivalent to s (region_equiv).

    CLAIM: Observational equivalence classes are Dedekind-infinite: they contain
    a copy of the natural numbers (ℕ injects into them).

    PROOF: Reuse region_equiv_class_infinite from EntropyImpossibility.v, which
    exhibits such an injection (tweak_regs - modify registers outside observed region).

    WHY THIS MATTERS (entropy obstruction):
    If observational classes are infinite, they cannot have finite entropy (finite
    Shannon information). Observing a finite set of bits cannot pin down the state
    uniquely - there are infinitely many hidden degrees of freedom (unobserved registers).

    This means:
    1. VM states have unbounded information content (not finitely describable)
    2. Observations are lossy (infinitely many states project to same observation)
    3. Perfect knowledge of the state is impossible from finite observations

    PHYSICAL INTERPRETATION:
    This is analogous to phase space in statistical mechanics. A macrostate (observation)
    corresponds to infinitely many microstates (actual VM states). Entropy measures
    the volume of microstate space consistent with a macrostate. Here: infinite volume.

    RELATION TO HEISENBERG: In quantum mechanics, you can't measure position and
    momentum simultaneously (uncertainty principle). Here: you can't know the full
    VM state from finite observations (entropy principle). Both are information-theoretic
    limits on knowability.

    DEDEKIND-INFINITE:
    A set X is Dedekind-infinite if there exists an injection f : ℕ → X. Equivalently,
    X contains a proper subset in bijection with itself (X ≅ X \ {x} for some x).
    This is weaker than "set-theoretically infinite" in constructive logic (no
    excluded middle), but equivalent classically.

    Observational classes are Dedekind-infinite: you can always hide one more bit
    of information in an unobserved register.

    FALSIFICATION: Prove region_equiv classes are finite (have only finitely many
    members). This would contradict the explicit injection f : ℕ → VMState given
    by region_equiv_class_infinite (proven in EntropyImpossibility.v).
*)
Lemma region_equiv_class_dedekind_infinite : forall s,
  exists f : nat -> VMState,
    (forall n, region_equiv s (f n)) /\
    (forall n1 n2, f n1 = f n2 -> n1 = n2).
Proof.
  intro s.
  (* Reuse the existing kernel witness (tweak_regs). *)
  destruct (region_equiv_class_infinite s) as [f [Hre Heq]].
  exists f. split; assumption.
Qed.

(** NoDup_map_inj: Injective maps preserve duplicate-freeness

    LEMMA: If l is a duplicate-free list and f is injective on l, then map f l
    is also duplicate-free.

    CLAIM: Applying an injective function to a list without duplicates produces
    a list without duplicates.

    PROOF TECHNIQUE (induction on NoDup structure):
    - Base case: NoDup([]) trivially implies NoDup(map f []) = NoDup([]) ✓
    - Inductive case: Assume NoDup(x::xs) with x ∉ xs and NoDup(xs).
      Goal: Prove NoDup(f(x) :: map f xs), i.e., f(x) ∉ map f xs and NoDup(map f xs).

      Part 1: NoDup(map f xs) follows from IH (inductive hypothesis) ✓
      Part 2: f(x) ∉ map f xs. Proof by contradiction:
        Assume f(x) ∈ map f xs. Then ∃y∈xs. f(y) = f(x).
        By injectivity: f(y) = f(x) → y = x.
        But y ∈ xs and x ∉ xs (premise), contradiction!
      Therefore f(x) ∉ map f xs ✓
    QED.

    WHY THIS MATTERS (for counting):
    This is a helper lemma for region_equiv_class_not_finite. To prove a class
    is infinite, we construct arbitrarily large duplicate-free lists inside it.
    If the class were finite (bounded list l), embedding an arbitrarily large
    list would exceed the bound (length > |l|), contradiction.

    The NoDup property ensures we're counting distinct elements, not repetitions.

    PHYSICAL INTERPRETATION:
    In statistical mechanics, counting microstates requires no double-counting
    (states must be distinguishable). Injectivity = distinguishability (different
    indices → different states). NoDup = no double-counting (list has no repetitions).
    This lemma says: if you label states distinctly (injectivity), the labels
    remain distinct (NoDup preserved).

    FALSIFICATION:
    Find an injective function f and duplicate-free list l where map f l has
    duplicates. This would mean f is not injective (contradiction) or the proof
    has an error (unlikely - standard list induction).
*)
Lemma NoDup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
    NoDup l ->
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup (map f l).
Proof.
  intros A B f l Hnodup.
  induction Hnodup as [|x xs Hnotin Hnodup_xs IH]; intros Hinj.
  - simpl. constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hyin]].
      pose proof (Hinj x y (or_introl eq_refl) (or_intror Hyin) (eq_sym Hfy)) as Heq.
      subst y.
      exact (Hnotin Hyin).
    + apply IH.
      intros a b Ha Hb Hab.
      apply (Hinj a b (or_intror Ha) (or_intror Hb) Hab).
Qed.

(** region_equiv_class_not_finite: OBSERVATIONAL CLASSES CANNOT BE FINITE

    THEOREM: For any VM state s, the equivalence class {s' | region_equiv s s'}
    is NOT finite (cannot be enumerated by a finite list).

    CLAIM: There is no finite list containing all region-equivalent states.

    PROOF BY CONTRADICTION:
    Assume the class is finite: ∃l. NoDup(l) ∧ (∀s'. region_equiv s s' → s' ∈ l).

    From region_equiv_class_dedekind_infinite, we have an injection f : ℕ → class.

    Build a list: l1 = [f(0), f(1), ..., f(n)] where n = length(l) + 1.

    Properties of l1:
    1. length(l1) = n = length(l) + 1 (by construction)
    2. NoDup(l1) (since f is injective, apply NoDup_map_inj)
    3. l1 ⊆ l (since all f(k) are region-equiv to s, hence in l by assumption)

    From (3): length(l1) ≤ length(l) (sublist has at most as many elements)
    From (1): length(l1) = length(l) + 1 > length(l)

    Contradiction: length(l1) > length(l) and length(l1) ≤ length(l) cannot both hold.
    Therefore the assumption (finite class) is false. QED.

    WHY THIS IS STRONGER THAN DEDEKIND-INFINITE:
    - Dedekind-infinite: "class contains a copy of ℕ" (injection exists)
    - Not finite: "class is larger than any finite set" (no finite bound)

    Dedekind-infinite implies not finite (constructively), but the converse
    requires excluded middle (classical logic). This proof is fully constructive.

    PHYSICAL INTERPRETATION:
    This proves VM states have UNBOUNDED entropy. You cannot fully specify a state
    with finite information - there are always more hidden degrees of freedom.

    Contrast with finite-state automata (FSA): FSAs have finitely many states,
    so observing them fully pins down the state (finite entropy). VMs have
    infinitely many states, so observations are always incomplete (infinite entropy).

    RELATION TO HALTING PROBLEM:
    The infinity of state space is connected to undecidability. If state space
    were finite, many undecidable problems (halting, equivalence) would become
    decidable (brute-force search over finite space). Infinity = impossibility
    of complete enumeration = undecidability.

    WHY OBSERVATIONAL EQUIVALENCE:
    We don't claim LITERAL state space is infinite (that's trivial - infinitely
    many register values). We claim OBSERVATIONALLY DISTINCT states are infinite.
    Even if you can only observe a finite region (registers 0-9), infinitely
    many states produce the same observation (differ only in registers 10+).

    This makes the infinity ROBUST: it's not an artifact of representation, it's
    a property of observable behavior. You can't avoid it by cleverer encoding.

    FALSIFICATION:
    Find a finite list l exhaustively enumerating some region_equiv class. This
    would mean the class is finite, contradicting the proof. Or show the injection
    f : ℕ → class is not actually injective (would contradict region_equiv_class_infinite).
*)
Theorem region_equiv_class_not_finite :
  forall s,
    ~ finite_region_equiv_class s.
Proof.
  intro s.
  unfold finite_region_equiv_class.
  destruct (region_equiv_class_dedekind_infinite s) as [f [Hre Hinj]].
  intro Hfin.
  destruct Hfin as [l [Hnodup Hall]].
  (* Build an arbitrary-large NoDup list inside l, contradicting finiteness. *)
  set (n := S (length l)).
  pose (l1 := map f (seq 0 n)).
  assert (Hnodup_l1 : NoDup l1).
  {
    unfold l1.
    apply (NoDup_map_inj nat VMState f (seq 0 n)).
    - apply seq_NoDup.
    - intros a b _ _ Hab.
      apply Hinj in Hab.
      exact Hab.
  }
  assert (Hincl : incl l1 l).
  {
    unfold incl, l1.
    intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [k [Hx Hk]].
    subst x.
    (* f k is region-equivalent to s, hence must be in l *)
    apply Hall.
    apply Hre.
  }
  pose proof (NoDup_incl_length Hnodup_l1 Hincl) as Hlen.
  unfold l1 in Hlen.
  rewrite map_length, seq_length in Hlen.
  (* n <= length l contradicts n = S (length l) *)
  unfold n in Hlen.
  lia.
Qed.

(** ** Flagship no-go theorem (kernel + explicit gaps) *)

(** KernelNoGoForTOE_P: Combined no-go statement for Theory of Everything

    DEFINITION: The conjunction of two fundamental impossibility results:
    1. Weight non-uniqueness: Multiple cost functions satisfy weight_laws
    2. Entropy unboundedness: Observational equivalence classes are infinite

    FORMULA: KernelNoGo_UniqueWeight_FailsP ∧ (∀s. ¬finite_region_equiv_class s)

    WHY THESE TWO:
    These are the TWO MAJOR OBSTRUCTIONS to a naive "theory of everything" for
    computational cost and state space:

    OBSTRUCTION 1 (Non-uniqueness):
    You cannot derive μ-cost from locality and additivity alone. The weight_laws
    are underdetermined - they allow infinitely many solutions (any scale factor k).
    To get uniqueness, you MUST add structure (singleton_uniform, unit_normalization).

    This means: μ-cost is NOT "forced by physics" - it requires a CHOICE (symmetry
    assumption + scale-fixing). The choice is motivated (all operations traverse
    state space equally), but it's not derivable from first principles alone.

    OBSTRUCTION 2 (Infinity):
    You cannot finitely enumerate observational equivalence classes. VM state
    space is fundamentally UNBOUNDED - infinitely many states project to the same
    observation. This makes perfect knowledge impossible from finite observations.

    This means: computational systems have UNBOUNDED ENTROPY. You can't specify
    a state completely with finite information. There are always hidden degrees
    of freedom (unobserved registers, memory beyond accessible region, etc.).

    WHY "FOR TOE":
    A "theory of everything" (TOE) for computation would need to:
    - Uniquely determine cost (fail: obstruction 1)
    - Finitely describe states (fail: obstruction 2)

    Both fail! This proves a computational TOE (in the naive sense) is IMPOSSIBLE.
    You cannot have a closed-form, finite, unique theory of all computational costs
    and states.

    WHAT THIS DOES NOT RULE OUT:
    This rules out naive completeness, but NOT useful theories. We CAN:
    - Fix the gauge (choose k=1) to get a unique cost function (weight_laws +
      singleton_uniform + unit_normalization)
    - Work with equivalence classes modulo observation (finite quotient structures)
    - Make falsifiable predictions about observable quantities

    The no-go says: "you need extra structure" (gauges, quotients), not "theories
    are impossible". It's a QUALIFICATION, not a REFUTATION.

    RELATION TO GÖDEL:
    Gödel's incompleteness: arithmetic axioms don't prove all truths (non-completeness).
    Here: weight laws don't fix all costs (non-uniqueness), observations don't
    determine all states (non-finiteness).

    Both are INHERENT LIMITATIONS on formal systems, not fixable by adding axioms
    (Gödel) or observations (here). They're structural features of the domains.

    PHYSICAL ANALOGY:
    In quantum field theory, renormalization group shows physical quantities depend
    on scale choice (running coupling constants). You can't have a "scale-independent
    theory" - you must fix a reference scale (like μ in dimensional regularization).

    Here: cost depends on gauge choice (k), state description depends on observation
    granularity (which registers are visible). You can't have a "gauge-independent"
    or "observation-independent" theory - you must fix conventions.

    FALSIFICATION:
    Refute either component:
    1. Prove weight_laws uniquely determines μ-cost (contradicts w_scale counterexample)
    2. Prove region_equiv classes are finite (contradicts injection f : ℕ → class)

    If either succeeds, the combined no-go theorem fails. But both components are
    proven independently, so falsification requires finding errors in those proofs.
*)
Definition KernelNoGoForTOE_P : Prop :=
  KernelNoGo_UniqueWeight_FailsP
  /\
  (forall s, ~ finite_region_equiv_class s).

(** KernelNoGoForTOE: THE FLAGSHIP NO-GO THEOREM

    THEOREM: The combined no-go statement holds.

    CLAIM: Both major obstructions (non-uniqueness, infinity) are true.

    PROOF: Combine the two component theorems:
    - KernelNoGo_UniqueWeight_Fails: proven above (w_scale(1) ≠ w_scale(2))
    - region_equiv_class_not_finite: proven above (injection ℕ → class)
    Both established, therefore conjunction holds. QED.

    WHY THIS IS SIGNIFICANT:
    This is the MASTER NO-GO THEOREM for computational theories of everything.
    It establishes fundamental limits on what can be achieved:
    - Completeness: NO (cost needs gauge-fixing)
    - Finitude: NO (states are unbounded)
    - Uniqueness: NO (laws underdetermine solutions)

    Together: computational theories are INHERENTLY OPEN-ENDED, not closed systems.

    POSITIVE IMPLICATIONS:
    Despite being "negative" (impossibility), this has POSITIVE uses:
    1. Tells us what structure is NECESSARY (singleton_uniform, quotient by obs)
    2. Justifies the CHOICES made (k=1 gauge, region_equiv classes as base)
    3. Prevents false hope (don't search for what doesn't exist)

    This is like Bell's theorem: "negative" (no local hidden variables) but
    POSITIVE (clarifies quantum structure, justifies non-locality, guides experiment).

    RELATION TO PRACTICE:
    In practice, we:
    - Choose k=1 gauge (singleton_uniform + unit_normalization)
    - Work with finite approximations (bounded registers)
    - Make statistical predictions (asymptotic costs, not exact)

    The no-go says these CHOICES are necessary (not derivable). Acknowledging
    this makes the theory HONEST: "we assume X, therefore Y" not "Y is inevitable".

    FALSIFICATION:
    Prove a computational TOE exists without gauge choices or infinite state space.
    This would mean both component no-gos are wrong (contradicts their proofs,
    which are constructive and simple).
*)
Theorem KernelNoGoForTOE : KernelNoGoForTOE_P.
Proof.
  split.
  - exact KernelNoGo_UniqueWeight_Fails.
  - intro s.
    apply region_equiv_class_not_finite.
Qed.
