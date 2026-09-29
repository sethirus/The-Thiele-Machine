(**
    MuCostDerivation: mu-cost lower-bound interfaces and consistency checks.

    This file gives a formal interface for relating state-space reduction,
    syntactic description cost, reversible partition operations, and VM
    instruction-cost formulas. It does not derive physical costs from Coq
    semantics alone. Physical calibration remains a bridge hypothesis in the
    files that cite Landauer-Unruh style assumptions.

    The local content is:
    (1) state-space reduction has a log2-size difference measure
        ([to_erasure], [information_cost_bits]);
    (2) LASSERT cost is represented as state reduction plus description bits
        ([lassert_total_cost]);
    (3) an equal-size input/output model has zero information-erasure cost
        ([positive_cost_exceeds_equal_size_erasure]);
    (4) [proposed_selected_cost] agrees with a supplied delta formula when
        the matching hypotheses are provided
        ([supplied_delta_schedule_consistent]);
    (5) a cost meeting both the state-term and the description-term premises
        is at least the LASSERT formula ([lassert_cost_from_component_floors],
        [lassert_cost_formula_lower_bound], [lassert_cost_is_its_formula]).
        The premises are not proved, and KnowledgeNarrowing shows the
        state-term premise is not forced by merge pricing.

    supplied_delta_schedule_consistent: consistency check for a supplied
    delta formula.
    mu_cost_thermodynamic_bound: normalized identity for the bit-cost model.

    LASSERT(formula) is modeled as reducing accessible states from Ω to Ω',
    measured by log2 differences, plus description_bits. PNEW/PSPLIT/PMERGE
    are assigned zero by the proposed selected schedule. This file does not
    prove that the VM operations are physically reversible.

    The lower-bound interface is conditional on the stated state-reduction and
    description-cost premises. A different physical calibration would be a
    different bridge premise, not a refutation of these arithmetic lemmas.

    log2_subtraction_valid proven by Nat.log2_le_mono + case analysis

    *)

From Coq Require Import List Lia Arith.PeanoNat Bool String Reals.
From Coq Require Import Nat.
Import ListNotations.

From Kernel Require Import VMState VMStep StateSpaceCounting SemanticMuCost.
(* SCOPE NOTE: cross-tier import for Erasure type linking mu-cost accounting
   to the normalized thermodynamic-cost interface. *)
From Thermodynamic Require Import LandauerDerived.


(** A partition refinement reduces the modeled size of state-space cells. The
    erasure reading is represented by the log2-size difference below. *)

(** State space size before and after an operation *)
Record StateSpaceChange := {
  omega_before : nat;
  omega_after : nat;
  reduction_valid : omega_after <= omega_before
}.

(** The information-theoretic cost of state space reduction *)
Definition information_cost_bits (change : StateSpaceChange) : nat :=
  let n_before := log2_nat (omega_before change) in
  let n_after := log2_nat (omega_after change) in
  n_before - n_after.

(** This matches the erasure definition from Landauer *)
Lemma log2_subtraction_valid : forall (omega_before omega_after : nat),
  omega_after <= omega_before ->
  log2_nat omega_after <= log2_nat omega_before.
Proof.
  intros omega_before omega_after Hle.
  unfold log2_nat.
  destruct omega_after as [|omega_after'].
  - (* omega_after = 0 *)
    lia.
  - (* omega_after = S omega_after' *)
    destruct omega_before as [|omega_before'].
    + (* omega_before = 0, contradiction with omega_after > omega_before *)
      lia.
    + (* Both positive: need to show Nat.log2 ceiling is monotonic *)
      (* Use Nat.log2_le_mono: forall a b, a <= b -> Nat.log2 a <= Nat.log2 b *)
      assert (Hlog2_mono : Nat.log2 (S omega_after') <= Nat.log2 (S omega_before')).
      { apply Nat.log2_le_mono. lia. }
      (* Now handle ceiling adjustment - four cases *)
      destruct (Nat.pow 2 (Nat.log2 (S omega_after')) =? S omega_after') eqn:Hafter_pow;
      destruct (Nat.pow 2 (Nat.log2 (S omega_before')) =? S omega_before') eqn:Hbefore_pow.
      * (* Both are powers of 2: log2(after) <= log2(before), no adjustment *)
        lia.
      * (* after is power of 2, before is not: log2(after) <= log2(before) + 1 *)
        lia.
      * (* after is not power of 2, before is power of 2: log2(after) + 1 <= log2(before) *)
        (* This case needs special handling: if before = 2^k then log2(before) = k
           and after < 2^k implies log2(after) <= k-1, so log2(after) + 1 <= k *)
        apply Nat.eqb_eq in Hbefore_pow.
        (* before = 2^(log2(before)) *)
        (* If after = before, then after would also be a power of 2, contradicting Hafter_pow *)
        assert (S omega_after' <> S omega_before').
        { intro Heq. rewrite Heq in Hafter_pow. rewrite Hbefore_pow in Hafter_pow.
          rewrite Nat.eqb_refl in Hafter_pow. discriminate. }
        (* Combined with <=, we get < *)
        assert (Hstrict : S omega_after' < S omega_before').
        { apply Nat.lt_eq_cases in Hle. destruct Hle as [Hlt | Heq].
          - assumption.
          - contradiction. }
        (* Rewrite before with power of 2 *)
        rewrite <- Hbefore_pow in Hstrict.
        (* Now use Nat.log2_lt_pow2: forall a n, 0 < a -> a < 2^n -> log2 a < n *)
        assert (Nat.log2 (S omega_after') < Nat.log2 (S omega_before')).
        { apply Nat.log2_lt_pow2. lia. exact Hstrict. }
        lia.
      * (* Neither is power of 2: log2(after) + 1 <= log2(before) + 1 *)
        lia.
Qed.

Definition to_erasure (change : StateSpaceChange) : Erasure :=
  let n_before := log2_nat (omega_before change) in
  let n_after := log2_nat (omega_after change) in
  mkErasure n_before n_after (log2_subtraction_valid _ _ (reduction_valid change)).

(** LASSERT adds a constraint that partitions the state space.

    Information-theoretic analysis:
    1. Before: Ω states are accessible
    2. Constraint eliminates some states (unsatisfiable)
    3. After: Ω' states remain accessible
    4. Information erased: log₂(Ω/Ω') bits

    Additionally, the constraint itself must be DESCRIBED, requiring
    description_bits to specify which constraint was applied.
*)

(** LASSERT state space change *)
Record LASSERTChange := {
  omega_pre : nat;
  omega_post : nat;
  omega_post_le : omega_post <= omega_pre;
  omega_post_pos : omega_post > 0;  (* Must leave at least one state *)

  (** The constraint description (e.g., "x > 5") *)
  description : Constraint;

  (** Description complexity (from SemanticMuCost.v) *)
  description_bits : nat;
  description_valid : description_bits = semantic_complexity_bits description
}.

(** Total information cost of LASSERT *)
Definition lassert_total_cost (change : LASSERTChange) : nat :=
  let state_reduction_cost := log2_nat (omega_pre change) - log2_nat (omega_post change) in
  state_reduction_cost + description_bits change.

(** NOTE: The formula adds two terms, and each term stands for a premise,
    not a theorem.

    1. The state term, log2(Ω) - log2(Ω'), charges for narrowing the set of
       states consistent with the constraint. KnowledgeNarrowing shows that
       narrowing what an observer knows can happen with no merge at all, so
       a merge price does not force this term. It is forced only when the
       narrowing has to be recorded in a way that merges machine states.
    2. The description term charges for writing the constraint down.

    The lemmas below show that a cost meeting both premises is at least the
    formula. That is addition. It does not show the premises hold. *)


(** The proposal reads the partition operations as reversible bookkeeping.

    - PNEW: creates a new partition (labels a region, undone by unlabeling)
    - PSPLIT: splits a partition into subregions (undone by PMERGE)
    - PMERGE: merges partitions (undone by PSPLIT)

    By Landauer, a reversible operation needs no erasure cost. That is the
    reason for the zeros in the proposed schedule below. This file does not
    prove the VM operations are reversible; the reading is the proposal.

    What it does prove is smaller. An equal-size abstraction has the same
    modeled number of input and output states. This record is deliberately
    not called a reversible operation: cardinality equality alone does not
    supply an inverse for a VM step. *)
Record EqualSizeErasureModel := {
  modeled_state_count : nat
}.

(** In the normalized erasure model, a positive candidate cost is strictly
    greater than the computed zero-bit erasure of an equal-size abstraction.
    This arithmetic fact neither assigns costs to partition instructions nor
    proves those instructions reversible. *)
Theorem positive_cost_exceeds_equal_size_erasure :
  forall (op : EqualSizeErasureModel) (cost : nat),
  cost > 0 ->
  cost > bits_erased {| input_bits := log2_nat (modeled_state_count op);
                        output_bits := log2_nat (modeled_state_count op);
                        output_leq := Nat.le_refl _ |}.
Proof.
  intros op cost Hpos.
  unfold bits_erased. simpl.
  rewrite Nat.sub_diag.
  exact Hpos.
Qed.


(** Link to LandauerDerived.v: normalized bit-cost interface. *)

(** Given an information cost in bits, compute the normalized cost. *)
Definition landauer_energy_bits (info_bits : nat) : nat := info_bits.

(** Normalized-units identity (k_B * T * ln(2) = 1). *)
Definition landauer_energy_bits_eq (info_bits : nat)
  : landauer_energy_bits info_bits = info_bits := eq_refl.

(** Theorem: in normalized units, the bit-cost function is at least the bit count. *)
Theorem mu_cost_thermodynamic_bound : forall (info_bits : nat),
  (* In normalized units where the conversion factor is 1: *)
  landauer_energy_bits info_bits >= info_bits.
Proof.
  intro info_bits.
  rewrite (landauer_energy_bits_eq info_bits).
  apply Nat.le_refl.
Qed.

(** Physical-unit readings require an external calibration hypothesis. *)


(** A proposed schedule for the selected partition and assertion cases. It is
    not the VM's complete [instruction_cost] schedule and is not derived from
    the operational semantics. *)
Definition proposed_selected_cost (instr : vm_instruction) : nat :=
  match instr with
  | instr_pnew _ _ => 0           (* Reversible *)
  | instr_psplit _ _ _ _ => 0     (* Reversible *)
  | instr_pmerge _ _ _ => 0       (* Reversible *)
  | instr_lassert _ _ _ flen delta =>
      (* The caller may separately relate delta to an information formula. *)
      flen * 8 + S delta
  | _ => 0  (* No claim about the omitted instruction cases. *)
  end.

(** [supplied_delta_schedule_consistent] is a consistency check, not an
    independence or necessity proof.

    If delta is supplied equal to the information expression, then the proposed
    selected schedule returns its syntactic result. The theorem does not prove
    that the expression uniquely forces delta.

    The stronger independence argument (that the formula determines mu_delta
    rather than describing a supplied delta) requires a physical calibration
    hypothesis (Landauer-Unruh) that cannot be derived from Coq semantics alone.
    That bridge is documented in NoFIToEinstein.v as
    mu_landauer_unruh_calibrated.

    This theorem checks consistency of the supplied cost formula with the
    supplied information expression. It does not derive the VM schedule from
    information theory; the calibration remains a separate bridge premise. *)
Theorem supplied_delta_schedule_consistent : forall (instr : vm_instruction),
  match instr with
  | instr_lassert fa ca k flen delta =>
      (* The supplied delta is checked against: *)
      (* 1. State space reduction log₂(Ω/Ω') *)
      (* 2. Description complexity semantic_complexity_bits(formula) *)
      forall omega_before omega_after (desc_bits : nat) (ast : Constraint),
        omega_after <= omega_before ->
        desc_bits = semantic_complexity_bits ast ->
        delta = 1 + (log2_nat omega_before - log2_nat omega_after) + desc_bits ->
        proposed_selected_cost instr = flen * 8 + S delta
  | instr_pnew _ delta =>
      delta = 0 -> proposed_selected_cost instr = delta
  | instr_psplit _ _ _ delta =>
      delta = 0 -> proposed_selected_cost instr = delta
  | instr_pmerge _ _ delta =>
      delta = 0 -> proposed_selected_cost instr = delta
  | _ => True
  end.
Proof.
  intro instr.
  destruct instr; unfold proposed_selected_cost; simpl; auto;
    (* Handle the four explicit cases *)
    try (intros; rewrite <- H; reflexivity);      (* PNEW, PSPLIT, PMERGE *)
    try (intros; rewrite <- H2; reflexivity).     (* LASSERT *)
Qed.


(** What the delta formula is.

    In the VM, instruction_cost reads the declared mu_delta. The formula
    above is a proposed value for it: for LASSERT,
    1 + log2(Ω/Ω') + semantic_complexity_bits(formula), and 0 for the
    partition operations. [supplied_delta_schedule_consistent] checks that
    the proposed selected schedule returns that value when the program
    declares it. Nothing here forces a program to declare it, and no theorem
    here identifies this proposal with the complete VM schedule. Whether
    physics forces the log2 term is the question KnowledgeNarrowing
    answers: narrowing knowledge does not by itself merge states, so merge
    pricing does not force it. *)

(** Bridge premise used by downstream physical readings

    A physical implementation may be related to the information-theoretic cost
    by an external calibration premise. This file does not introduce such an
    axiom; it only records the local cost formulas and lower-bound lemmas.

    Alternative cost assignments can be compared against the lower-bound
    premises below. Physical claims belong at BRIDGE tier.
*)


(** How MuInitiality.v can reference this file:

    The Initiality Theorem proves:
      "μ is unique among functionals consistent with instruction_cost"

    This file records:
      "selected instruction-cost formulas satisfy the stated information
       lower-bound interfaces"

    Together:
      "μ is unique relative to the chosen instruction_cost and the cited
       lower-bound interface"

    This keeps the cost assumptions explicit rather than hidden in prose.
*)

(** Connection to [VMStep.instruction_cost].

    The VM schedule reads encoded delta parameters and adds constructor-specific
    floors. This file does not determine those parameters. It records a proposed
    value for selected cases and proves conditional lower bounds when callers
    provide both component premises. [MuInitiality] therefore remains relative
    to the chosen VM schedule. *)


(**
   PROVEN locally:

   1. State space reduction has a log2-size difference measure
      (via [to_erasure] and [information_cost_bits]; equality holds by
      definition, so no separate lemma is required).
   2. LASSERT cost formula combines log₂(Ω/Ω') and description_bits
      (via [lassert_total_cost]; component lower bounds hold by [lia]
      after [unfold lassert_total_cost] at any caller).
   3. An equal-size abstraction has zero erasure cost
      ([positive_cost_exceeds_equal_size_erasure] says any positive candidate
      exceeds that zero-bit computation). No VM reversibility theorem follows.
   4. Normalized bit-cost identity ([mu_cost_thermodynamic_bound]).
   5. Cost formula consistency check
      ([supplied_delta_schedule_consistent]).
   6. Formula package: [lassert_cost_from_component_floors],
      [lassert_cost_formula_lower_bound], [lassert_cost_is_its_formula]: a cost
      meeting both premises is at least the formula.

   ALL PROVEN (zero Admitted):

   - log2_subtraction_valid: Proven by Nat.log2_le_mono + case analysis (Qed)

   Physical necessity and Landauer calibration remain bridge-level claims.
*)

(**

    BRIDGE CLOSURE:
    [supplied_delta_schedule_consistent] (Part 5) is a consistency check: if
    delta equals the information expression, then [proposed_selected_cost]
    returns the stated syntactic value. The remaining bridge question is
    whether the costs are physically necessary or merely consistent with
    the local model.

    LOCAL ANSWER:
    The LASSERT cost formula is a minimum under both stated premises:
    (a) the state term: the model charges log2(Ω/Ω') for narrowing the
        consistent states. This is a premise. Merge pricing does not force
        it, because narrowing what is known need not merge states.
    (b) Description complexity: specifying the constraint costs description_bits
        under the model.

    These are separate requirements in the interface. Therefore any model that
    satisfies both lower-bound premises pays at least lassert_total_cost.

    Within the Coq semantics this is addition over premises. A physical
    reading needs mu_landauer_unruh_calibrated (named hypothesis in
    NoFIToEinstein.v) and, for the state term, a merge the narrowing forces.
*)

(** lassert_cost_from_component_floors: if a cost pays at least the state
    term and at least the description term, it pays at least the formula.
    The premises are the content; the conclusion is their sum. *)
(* DEFINITIONAL HELPER *)
Theorem lassert_cost_from_component_floors :
  forall (change : LASSERTChange)
         (state_reduction_cost : nat)
         (description_cost : nat),
    state_reduction_cost >=
      log2_nat (omega_pre change) - log2_nat (omega_post change) ->
    description_cost >= description_bits change ->
    state_reduction_cost + description_cost >= lassert_total_cost change.
Proof.
  intros change src desc Hsrc Hdesc.
  unfold lassert_total_cost. lia.
Qed.

(** lassert_cost_formula_lower_bound: a total at least the sum of the two
    terms is at least the formula, because the formula is that sum. *)
(* DEFINITIONAL HELPER *)
Theorem lassert_cost_formula_lower_bound :
  forall (change : LASSERTChange) (total_cost : nat),
    total_cost >=
      (log2_nat (omega_pre change) - log2_nat (omega_post change)) +
       description_bits change ->
    total_cost >= lassert_total_cost change.
Proof.
  intros change total_cost H.
  unfold lassert_total_cost. lia.
Qed.

(** lassert_cost_is_its_formula: the formula equals the sum of its two
    terms, and any total at least that sum is at least the formula. Both
    halves hold by unfolding the definition. Whether a physical
    implementation must pay either term is the separate question the NOTE
    above answers. *)
Theorem lassert_cost_is_its_formula :
  forall (change : LASSERTChange),
    lassert_total_cost change =
      (log2_nat (omega_pre change) - log2_nat (omega_post change)) +
       description_bits change /\
    (forall (total_cost : nat),
       total_cost >=
         (log2_nat (omega_pre change) - log2_nat (omega_post change)) +
          description_bits change ->
       total_cost >= lassert_total_cost change).
Proof.
  intro change.
  split.
  - unfold lassert_total_cost. reflexivity.
  - intro total_cost. exact (lassert_cost_formula_lower_bound change total_cost).
Qed.


(** Check that our theorems don't use problematic axioms *)
Print Assumptions supplied_delta_schedule_consistent.
Print Assumptions lassert_cost_from_component_floors.
Print Assumptions lassert_cost_formula_lower_bound.
Print Assumptions lassert_cost_is_its_formula.

(** Expected: Only standard library axioms *)
