(** CHSHExtraction: Computing CHSH values from execution traces

    The Thiele Machine records measurement outcomes as [instr_chsh_trial]
    instructions. This file defines HOW to extract those outcomes from an
    executed trace and compute the CHSH statistic. It's pure accounting: follow
    the VM control flow, extract valid trials, compute correlations, sum them up.

    NO PHYSICS:
    This file makes ZERO assumptions about quantum mechanics, Tsirelson bounds,
    or correlation constraints. It's a MECHANICAL definition: given a list of
    (x,y,a,b) tuples, compute the number S = E00 + E01 + E10 - E11.

    THE COMPUTATION:
    1. Scan trace for instr_chsh_trial instructions
    2. Extract (x,y,a,b) from each trial
    3. Group by input pair (x,y)
    4. Compute correlation E_xy = (same - diff) / total
    5. Sum: S = E00 + E01 + E10 - E11

    That's it. No interpretation, no theory, no assumptions. Just arithmetic.

    By defining CHSH extraction independent of μ-cost, later files can ask
    questions about what different μ-cost classes can achieve. This file does
    not answer those questions. It just computes the number.

    Execute a trace with a known control path. Extract trials using these
    functions. Compute CHSH. If the result doesn't match hand calculation along
    that same path, these functions are wrong. The computation is deterministic,
    with no randomness and no interpretation.
*)

From Coq Require Import List QArith Qabs Lia Qround Qminmax Lra.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof MuCostModel.

(** CHSHTrial: One measurement in the Bell experiment.

    A CHSH test involves Alice and Bob making measurements. Each measurement
    produces 4 bits:
    - x: Alice's measurement choice (input)
    - y: Bob's measurement choice (input)
    - a: Alice's measurement result (output)
    - b: Bob's measurement result (output)

    This record bundles those four values into one trial. Validity is checked
    when extraction calls [chsh_bits_ok].

    THE INTERPRETATION:
    - Inputs (x,y): Which measurement basis/angle/setting was used
    - Outputs (a,b): What the detectors clicked (0 or 1)

    In quantum experiments: x and y are settings on Alice's and Bob's measurement
    devices. a and b are the outcomes (detector clicks).

    In the VM: x,y,a,b are just four nat values from the instr_chsh_trial
    instruction. No interpretation is needed here.
    extract_chsh_trials_from_trace produces a list of these. compute_correlation
    consumes them. This is the data structure flowing through the CHSH pipeline.
*)
Record CHSHTrial := {
  trial_x : nat;  (* Alice's input: 0 or 1 *)
  trial_y : nat;  (* Bob's input: 0 or 1 *)
  trial_a : nat;  (* Alice's output: 0 or 1 *)
  trial_b : nat   (* Bob's output: 0 or 1 *)
}.

(** extract_chsh_trials_from_trace: Execute trace and collect valid CHSH trials.

    WHY:
    The VM trace is a list of instructions. Some are instr_chsh_trial (x,y,a,b,mu).
    This function walks through the trace and extracts those trials.

    THE ALGORITHM:
    1. Look at current PC position in trace
    2. Step the current instruction using the actual vm_apply semantics
    3. If the executed instruction is a valid instr_chsh_trial: record (x,y,a,b)
    4. Otherwise: continue without recording a trial
    5. Repeat until fuel is exhausted or the current PC is outside the trace

    Coq requires proof of termination. Fuel bounds the number of steps. In
    practice, set fuel ≥ trace length.

    WHY USE vm_apply:
    CHSH extraction must follow the same control-flow and validity checks as the
    machine itself. JUMP/JNEZ/CALL/RET can change the PC, and invalid CHSH_TRIAL
    instructions latch an error without contributing a witness bucket. Using
    vm_apply keeps extraction aligned with actual execution rather than a simple
    linear scan.

    This is HOW trial records are extracted in Coq. Receipt integrity is handled
    in the receipt files; this function only follows VM execution and records
    valid CHSH instructions.

    Hand-simulate a trace with jumps, invalid trials, and fuel. If this function
    returns a different list of valid executed trials, the extractor is broken.
*)
Definition executed_chsh_trial_of_instruction (instr : vm_instruction) : option CHSHTrial :=
  match instr with
  | instr_chsh_trial x y a b _ =>
      if chsh_bits_ok x y a b then
        Some {| trial_x := x;
                trial_y := y;
                trial_a := a;
                trial_b := b |}
      else
        None
  | _ => None
  end.

(** Follow the VM for [fuel] steps and collect the valid CHSH trials that
    actually execute. *)
Fixpoint extract_chsh_trials_from_trace
  (fuel : nat) (trace : list vm_instruction) (s : VMState) : list CHSHTrial :=
  match fuel with
  | O => []
  | S fuel' =>
      match nth_error trace (s.(vm_pc)) with
      | None => []
      | Some instr =>
          let s' := vm_apply s instr in
          match executed_chsh_trial_of_instruction instr with
          | Some trial => trial :: extract_chsh_trials_from_trace fuel' trace s'
          | None => extract_chsh_trials_from_trace fuel' trace s'
          end
      end
  end.

(** A CHSH trial is valid exactly when all four fields are accepted bits. *)
Definition valid_chsh_trial (t : CHSHTrial) : Prop :=
  chsh_bits_ok t.(trial_x) t.(trial_y) t.(trial_a) t.(trial_b) = true.

(** Replay one extracted trial into the VM witness counters. *)
Definition record_extracted_trial (wc : WitnessCounts) (t : CHSHTrial) : WitnessCounts :=
  record_trial wc t.(trial_x) t.(trial_y) t.(trial_a) t.(trial_b).

(** If extraction returns a trial, then the instruction was a valid CHSH trial.
    Its μ-cost is still the instruction's declared cost; validity and pricing
    are separate facts. *)
Lemma executed_chsh_trial_of_instruction_valid :
  forall instr t,
    executed_chsh_trial_of_instruction instr = Some t ->
    valid_chsh_trial t.
Proof.
  intros instr t Hexec.
  destruct instr as
    [region cost
    | module left right cost
    | m1 m2 cost
    | module formula cert cost
    | cert1 cert2 cost
    | module cost
    | module evidence cost
    | dst src cost
    | dst imm cost
    | dst rs_addr cost
    | rs_addr src cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | target cost
    | rs target cost
    | target cost
    | cost
    | x y a b cost
    | dst addr cost
    | dst src cost
    | a b cost
    | dst src cost
    | module payload cost
    | module bits cert cost
    | cost
    | label cost
    | dst channel_idx value bits cost
    | channel_idx src cost
    | dst rs_addr cost
    | rs_addr src cost
    | delta_mu
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst imm cost
    | module i j value cost
    | dst module i j cost
    (** Phase 7: categorical instructions *)
    | dst src_mod dst_mod coupling_idx mu_delta
    | dst m1_id m2_id mu_delta
    | dst module mu_delta
    | morph_id mu_delta
    | morph_id property cert mu_delta
    | dst f_id g_id mu_delta
    | dst morph_id selector mu_delta]; simpl in Hexec; try discriminate.
  destruct (chsh_bits_ok _ _ _ _) eqn:Hok; inversion Hexec; subst.
  unfold valid_chsh_trial. exact Hok.
Qed.

Lemma executed_chsh_trial_of_instruction_implies_valid :
  forall instr t,
    executed_chsh_trial_of_instruction instr = Some t ->
    valid_chsh_trial t.
Proof.
  intros instr t Hexec.
  exact (executed_chsh_trial_of_instruction_valid instr t Hexec).
Qed.

Lemma executed_chsh_trial_of_instruction_updates_witness :
  forall instr s t,
    executed_chsh_trial_of_instruction instr = Some t ->
    (vm_apply s instr).(vm_witness) = record_extracted_trial s.(vm_witness) t.
Proof.
  intros instr s t Hexec.
  destruct instr as
    [region cost
    | module left right cost
    | m1 m2 cost
    | module formula cert cost
    | cert1 cert2 cost
    | module cost
    | module evidence cost
    | dst src cost
    | dst imm cost
    | dst rs_addr cost
    | rs_addr src cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | target cost
    | rs target cost
    | target cost
    | cost
    | x y a b cost
    | dst addr cost
    | dst src cost
    | a b cost
    | dst src cost
    | module payload cost
    | module bits cert cost
    | cost
    | label cost
    | dst channel_idx value bits cost
    | channel_idx src cost
    | dst rs_addr cost
    | rs_addr src cost
    | delta_mu
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst rs1 rs2 cost
    | dst imm cost
    | module i j value cost
    | dst module i j cost
    (** Phase 7: categorical instructions *)
    | dst src_mod dst_mod coupling_idx mu_delta
    | dst m1_id m2_id mu_delta
    | dst module mu_delta
    | morph_id mu_delta
    | morph_id property cert mu_delta
    | dst f_id g_id mu_delta
    | dst morph_id selector mu_delta]; simpl in Hexec; try discriminate.
  destruct (chsh_bits_ok _ _ _ _) eqn:Hok; inversion Hexec; subst; simpl.
  rewrite Hok.
  reflexivity.
Qed.

Lemma no_executed_chsh_trial_of_instruction_preserves_witness :
  forall instr s,
    executed_chsh_trial_of_instruction instr = None ->
    (vm_apply s instr).(vm_witness) = s.(vm_witness).
Proof.
  intros instr s Hnone.
  destruct instr.
  all: simpl in Hnone |- *;
       unfold advance_state, advance_state_reveal,
         advance_state_rm, jump_state, jump_state_rm in *;
       simpl in *;
       repeat match goal with
       | H : context [let '(_, _) := ?p in _] |- _ => destruct p eqn:?; simpl in *
       | |- context [let '(_, _) := ?p in _] => destruct p eqn:?; simpl in *
      | H : context [match ?m with _ => _ end] |- _ => destruct m eqn:?; simpl in *
      | |- context [match ?m with _ => _ end] => destruct m eqn:?; simpl in *
       end;
       try reflexivity;
       try discriminate.
  all: repeat match goal with
       | H : context [if ?b then _ else _] |- _ => destruct b eqn:?; simpl in *
       | |- context [if ?b then _ else _] => destruct b eqn:?; simpl in *
       end;
       try discriminate;
       reflexivity.
Qed.

(** Replay the extracted trials into a witness-counter state. *)
Fixpoint replay_trials_on_witness (trials : list CHSHTrial) (wc : WitnessCounts) : WitnessCounts :=
  match trials with
  | [] => wc
  | t :: ts => replay_trials_on_witness ts (record_extracted_trial wc t)
  end.

(** Running the VM updates witness counters exactly as replaying the extracted
    valid CHSH trials would. *)
Lemma run_vm_witness_equals_replayed_trials :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_witness) =
    replay_trials_on_witness (extract_chsh_trials_from_trace fuel trace s) s.(vm_witness).
Proof.
  induction fuel as [| fuel' IH]; intros trace s; simpl.
  - reflexivity.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl.
    + specialize (IH trace (vm_apply s instr)).
      destruct (executed_chsh_trial_of_instruction instr) as [trial|] eqn:Hexec; simpl in *.
      * rewrite <- (executed_chsh_trial_of_instruction_updates_witness instr s trial Hexec).
        exact IH.
      * rewrite <- (no_executed_chsh_trial_of_instruction_preserves_witness instr s Hexec).
        exact IH.
    + reflexivity.
Qed.

(** A successful [is_bit] check leaves only the two accepted bits. *)
Lemma is_bit_true_cases :
  forall n,
    is_bit n = true -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n Hbit.
  unfold is_bit in Hbit.
  apply Bool.orb_true_iff in Hbit.
  destruct Hbit as [Hz | Ho].
  - left. apply Nat.eqb_eq. exact Hz.
  - right. apply Nat.eqb_eq. exact Ho.
Qed.

(** A successful [chsh_bits_ok] check gives bit cases for all four fields. *)
Lemma chsh_bits_ok_true_cases :
  forall x y a b,
    chsh_bits_ok x y a b = true ->
    (x = 0%nat \/ x = 1%nat) /\
    (y = 0%nat \/ y = 1%nat) /\
    (a = 0%nat \/ a = 1%nat) /\
    (b = 0%nat \/ b = 1%nat).
Proof.
  intros x y a b Hok.
  unfold chsh_bits_ok in Hok.
  apply Bool.andb_true_iff in Hok.
  destruct Hok as [Hxy Hab].
  apply Bool.andb_true_iff in Hxy.
  apply Bool.andb_true_iff in Hab.
  destruct Hxy as [Hx Hy].
  destruct Hab as [Ha Hb].
  repeat split; apply is_bit_true_cases; assumption.
Qed.

(** Every trial emitted by the extractor passed [chsh_bits_ok]. *)
Lemma extract_chsh_trials_from_trace_valid :
  forall fuel trace s t,
    In t (extract_chsh_trials_from_trace fuel trace s) ->
    valid_chsh_trial t.
Proof.
  induction fuel as [| fuel' IH]; intros trace s t Hin; simpl in Hin.
  - contradiction.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl in Hin.
    + specialize (IH trace (vm_apply s instr) t).
      destruct (executed_chsh_trial_of_instruction instr) eqn:Htrial; simpl in Hin.
      * destruct Hin as [Heq | Hin'].
        -- inversion Heq; subst.
           eapply executed_chsh_trial_of_instruction_implies_valid; eauto.
        -- eapply IH; eauto.
      * eapply IH; eauto.
    + contradiction.
Qed.

(** filter_trials: Select trials with specific inputs (x,y).

    WHY:
    To compute E_00, E_01, E_10, E_11 separately, we need to group trials by
    their input pairs. This function filters a trial list to only those with
    matching (x,y).

    EXAMPLE:
    filter_trials all_trials 0 0 returns only trials where trial_x=0 AND trial_y=0.
*)
Definition filter_trials (trials : list CHSHTrial) (x y : nat) : list CHSHTrial :=
  filter (fun t => Nat.eqb t.(trial_x) x && Nat.eqb t.(trial_y) y) trials.

(** compute_correlation: Calculate E_xy from a list of trials.

    WHY:
    The correlation E_xy measures how aligned Alice's and Bob's outputs are
    for input pair (x,y). The formula:
    E_xy = (# trials where a=b) - (# trials where a≠b)
           --------------------------------------------
                      # total trials

    THE CALCULATION:
    - same_count: Count trials where outputs match (a=b)
    - diff_count: Count trials where outputs differ (a≠b)
    - total: Total number of trials
    - E = (same - diff) / total

    THE RANGE:
    - If all outputs match: E = (total - 0) / total = +1
    - If all outputs differ: E = (0 - total) / total = -1
    - Mixed outcomes: E ∈ [-1, +1]

    EDGE CASE:
    Empty trial list: return 0. No data means no correlation.

    This is the standard statistical correlation for binary outcomes. It's
    measuring alignment. +1 = perfect agreement, -1 = perfect disagreement,
    0 = random/uncorrelated.

    Given specific trials, compute E by hand. Compare with this function's
    output. Should match exactly (no rounding, pure rational arithmetic).
*)
Definition compute_correlation (trials : list CHSHTrial) : Q :=
  match trials with
  | [] => 0%Q
  | _ =>
      let same_count := length (filter (fun t => Nat.eqb t.(trial_a) t.(trial_b)) trials) in
      let diff_count := length (filter (fun t => negb (Nat.eqb t.(trial_a) t.(trial_b))) trials) in
      let total := length trials in
      (((Z.of_nat same_count # 1) - (Z.of_nat diff_count # 1)) / (Z.of_nat total # 1))%Q
  end.

(** chsh_from_trials: Compute the CHSH statistic from trial list.

    THE FORMULA:
    S = E00 + E01 + E10 - E11

    WHERE:
    - E00 = correlation for inputs (0,0)
    - E01 = correlation for inputs (0,1)
    - E10 = correlation for inputs (1,0)
    - E11 = correlation for inputs (1,1)

    This is the CHSH-Bell inequality test statistic. The specific combination
    (+ + + -) is what Bell and CHSH derived as maximally sensitive to
    nonlocal correlations.

    NO PHYSICS HERE:
    This is just arithmetic. Filter trials by inputs, compute correlations,
    sum them with that specific sign pattern. We're not interpreting what it
    means - just computing the number.

    THE OUTPUT:
    A rational number (Q). The function just computes. This file later proves
    the algebraic list-level bound |S| <= 4. Tighter classical or quantum bounds
    belong to other files and require additional hypotheses.

    Construct specific trials. Compute correlations by hand. Sum them. Compare
    with this function's output. Should match exactly.
*)
Definition chsh_from_trials (trials : list CHSHTrial) : Q :=
  let e00 := compute_correlation (filter_trials trials 0 0) in
  let e01 := compute_correlation (filter_trials trials 0 1) in
  let e10 := compute_correlation (filter_trials trials 1 0) in
  let e11 := compute_correlation (filter_trials trials 1 1) in
  (e00 + e01 + e10 - e11)%Q.

(** chsh_from_vm_trace: Top-level function - trace → CHSH value.

    WHY:
    This is the complete pipeline: trace → trials → correlations → CHSH.
    One function call to go from VM execution trace to final CHSH number.

    THE PIPELINE:
    1. extract_chsh_trials_from_trace: scan trace, collect trials
    2. chsh_from_trials: compute CHSH from trials
    Tests, verification, runtime. This is the function for computing CHSH
    from an executed VM trace.
*)
Definition chsh_from_vm_trace
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Q :=
  let trials := extract_chsh_trials_from_trace fuel trace s_init in
  chsh_from_trials trials.

(** Properties of CHSH Computation - Sanity Checks *)

Close Scope Q_scope.
Open Scope nat_scope.

(** trial_partition: Same-count + diff-count = total.

    For any list of trials, each trial either has matching outputs (a=b) or
    differing outputs (a≠b). There's no third option. So the counts must sum
    to the total.
    (# trials with a=b) + (# trials with a≠b) = (# total trials)
    Induction on trial list. Base case: empty list, 0+0=0. Inductive case:
    look at first trial - either a=b (add to same_count) or a≠b (add to
    diff_count). Either way, totals match.

    Proves that compute_correlation is well-defined. We're computing
    (same - diff) / total where same + diff = total. This lemma justifies
    that the denominator equals the numerator's components.

    Find a trial list where same_count + diff_count ≠ total. Can't happen -
    Boolean logic guarantees a=b OR a≠b for any a,b.
*)
Lemma trial_partition :
  forall trials,
    length (filter (fun t => Nat.eqb t.(trial_a) t.(trial_b)) trials) +
    length (filter (fun t => negb (Nat.eqb t.(trial_a) t.(trial_b))) trials) =
    length trials.
Proof.
  intro trials.
  induction trials as [|t ts IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb (trial_a t) (trial_b t)) eqn:Heq; simpl; lia.
Qed.

(** filter_length_le: Filtering can't increase length.

    WHY:
    Filtering a list removes elements that don't match the predicate. It can't
    add elements. So filtered length ≤ original length.
    Induction. Base case: empty list filters to empty. Inductive case: either
    predicate true (keep element, length stays same or increases by 1) or false
    (remove element, filtered length < original). Either way, bound holds.

    Sanity check for trial filtering. When we filter_trials for specific (x,y),
    the result can't be longer than the original list.
*)
Lemma filter_length_le :
  forall {A : Type} (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  intros A f l.
  induction l; simpl; [lia|].
  destruct (f a); simpl; lia.
Qed.

Close Scope nat_scope.
Open Scope Q_scope.

(** Qabs_4_triangle: Triangle inequality for sum of 4 terms.
    |a + b + c - d| ≤ |a| + |b| + |c| + |d|

    Standard triangle inequality: |x + y| ≤ |x| + |y|. Apply repeatedly:
    - |a + b + c - d| = |a + b + c + (-d)| ≤ |a + b + c| + |-d|
    - |a + b + c| ≤ |a + b| + |c|
    - |a + b| ≤ |a| + |b|
    Chain them together: |a + b + c - d| ≤ |a| + |b| + |c| + |d|.

    Used in chsh_algebraic_bound to prove CHSH ≤ 4. Since S = E00 + E01 + E10 - E11,
    we need a triangle inequality for this specific form (three plus, one minus).
    Rewrite a+b+c-d as a+b+c+(-d), apply triangle inequality three times,
    use |−d| = |d|, and chain the inequalities.

    Find a,b,c,d ∈ Q where |a+b+c-d| > |a|+|b|+|c|+|d|. Impossible - triangle
    inequality is a fundamental property of absolute value.
*)
Lemma Qabs_4_triangle :
  forall a b c d : Q,
    Qabs (a + b + c - d) <= Qabs a + Qabs b + Qabs c + Qabs d.
Proof.
  intros.
  (* Use standard triangle inequality lemmas *)
  assert (H_abc_d: Qabs (a + b + c + -d) <= Qabs (a + b + c) + Qabs (-d)).
  { apply Qabs_triangle. }
  assert (H_abc: Qabs (a + b + c) <= Qabs (a + b) + Qabs c).
  { apply Qabs_triangle. }
  assert (H_ab: Qabs (a + b) <= Qabs a + Qabs b).
  { apply Qabs_triangle. }
  (* Note: a + b + c - d = a + b + c + -d *)
  assert (Heq: a + b + c - d == a + b + c + -d).
  { unfold Qeq. simpl. ring. }
  (* Rewrite LHS *)
  assert (HLcompatible: Qabs (a + b + c - d) == Qabs (a + b + c + -d)).
  { apply Qabs_wd. exact Heq. }
  rewrite HLcompatible.
  rewrite Qabs_opp in H_abc_d.
  (* Now: Qabs (a + b + c + -d) <= Qabs (a + b + c) + Qabs d *)
  eapply Qle_trans. exact H_abc_d.
  (* Goal: Qabs (a + b + c) + Qabs d <= Qabs a + Qabs b + Qabs c + Qabs d *)
  apply Qplus_le_compat. 2: apply Qle_refl.
  eapply Qle_trans. exact H_abc.
  apply Qplus_le_compat. 2: apply Qle_refl.
  exact H_ab.
Qed.

Open Scope Q_scope.

(** correlation_bound_1: All correlations are bounded by ±1.
    For any trial list, |E_xy| ≤ 1, where E_xy = (same - diff) / total.

    The key insight: same + diff = total (proven in trial_partition). This means
    both 'same' and 'diff' are ≤ total. Therefore:
    - Maximum: same = total, diff = 0 → E = total/total = +1
    - Minimum: same = 0, diff = total → E = -total/total = -1
    - General: |same - diff| ≤ max(same + diff) = total → |E| ≤ 1

    THE PROOF STRUCTURE:
    1. Empty trials: correlation = 0, so |0| ≤ 1
    2. Non-empty trials:
       - Set same = # trials with a=b
       - Set diff = # trials with a≠b
       - Use trial_partition: same + diff = total
       - Prove |same - diff| ≤ total (arithmetic on naturals)
       - Therefore |(same - diff)/total| ≤ 1

    This is THE fundamental bound on correlations. Probability theory guarantees
    it. Without this bound, [chsh_algebraic_bound] would not hold. The ceiling
    comes from the fact that correlations can't exceed ±1.

    THE Z.abs USAGE:
    The proof uses Z.abs (integer absolute value) to prove |same - diff| ≤ total
    at the integer level, then lifts to rational Q via Qabs. Safe because we're
    proving a mathematical bound, not computing it at runtime.

    Construct trials where |E_xy| > 1. Impossible - would require same - diff > total,
    which violates same + diff = total (Boolean partition).
*)
Lemma correlation_bound_1 :
  forall trials,
    Qabs (compute_correlation trials) <= 1%Q.
Proof.
  intro trials.
  unfold compute_correlation.
  destruct trials as [| t ts]; simpl.
  - (* Empty trials list: correlation = 0 *)
    unfold Qabs, Qle. simpl. apply Z.leb_le. reflexivity.
  - (* Non-empty: (same-diff)/total where same+diff=total *)
    set (sf := filter (fun tr : CHSHTrial => Nat.eqb (trial_a tr) (trial_b tr)) (t :: ts)).
    set (df := filter (fun tr : CHSHTrial => negb (Nat.eqb (trial_a tr) (trial_b tr))) (t :: ts)).
    set (same := Z.of_nat (length sf)).
    set (diff := Z.of_nat (length df)).
    set (total := Z.of_nat (S (length ts))).
    
    (* Key: same + diff = total *)
    assert (Hpart: (length sf + length df = S (length ts))%nat).
    { unfold sf, df. apply trial_partition. }
    assert (Hsum: (same + diff = total)%Z).
    { unfold same, diff, total. lia. }
    
    (* total > 0 *)
    assert (Hpos: (0 < total)%Z) by (unfold total; lia).
    
    (* Prove: Qabs ((same - diff) / total) <= 1 *)
    (* Key: same + diff = total implies |same - diff| <= total *)
    
    (* First prove at Z level *)
    (* SAFE: Z.abs used in proven bound for correlation <=1 *)
    assert (Habs: (Z.abs (same - diff) <= total)%Z) by (unfold same, diff, total; apply Z.abs_le; lia).
    
    (* Convert Q goal to Z by unfolding *)
    unfold Qdiv, Qabs, Qle, Qmult, Qinv, inject_Z.
    simpl.
    
    (* The goal contains expanded filter expressions *)
    (* Replace them with sf and df which are cleaner *)
    replace (length (if (trial_a t =? trial_b t)%nat 
                     then t :: filter (fun t => (trial_a t =? trial_b t)%nat) ts
                     else filter (fun t => (trial_a t =? trial_b t)%nat) ts))
      with (length sf) by (unfold sf; reflexivity).
    replace (length (if negb (trial_a t =? trial_b t)%nat
                     then t :: filter (fun t => negb (trial_a t =? trial_b t)%nat) ts
                     else filter (fun t => negb (trial_a t =? trial_b t)%nat) ts))
      with (length df) by (unfold df; reflexivity).
    
    (* Simplify to use same/diff/total *)
    replace (Z.of_nat (length sf)) with same by reflexivity.
    replace (Z.of_nat (length df)) with diff by reflexivity.
    replace (Z.pos (Pos.of_succ_nat (length ts))) with total by (unfold total; reflexivity).
    
    (* Simplify multiplications *)
    replace ((same * 1 + - diff * 1) * 1)%Z with (same - diff)%Z by ring.
    (* SAFE: Z.abs simplification from proven bound *)
    replace (Z.abs (same - diff) * 1 * 1)%Z with (Z.abs (same - diff) * 1)%Z by ring.
    
    (* Simplify the remaining * 1 *)
    rewrite Z.mul_1_r.
    
    (* Complete using the proven bound *)
    unfold Z.le in Habs.
    unfold Z.le.
    exact Habs.
Qed.

(** chsh_algebraic_bound: CHSH is algebraically bounded by 4.
    For ANY trial list, |S| ≤ 4, where S = E00 + E01 + E10 - E11.

    This is the algebraic ceiling for this statistic. No physics, no quantum
    mechanics, no hidden variables. Just:
    1. Each correlation |E_xy| ≤ 1 (correlation_bound_1)
    2. Triangle inequality: |E00 + E01 + E10 - E11| ≤ |E00| + |E01| + |E10| + |E11|
    3. Therefore: |S| ≤ 1 + 1 + 1 + 1 = 4

    THE HIERARCHY:
    - Deterministic local bound: |S| ≤ 2, proved in CHSH.v
    - Symmetric rational Tsirelson-style cap: see AlgebraicCoherence.v
    - Algebraic list-level ceiling: |S| ≤ 4, this lemma
    1. Apply triangle inequality for 4 terms (Qabs_4_triangle)
    2. Bound each |E_xy| ≤ 1 using correlation_bound_1
    3. Sum the bounds: 1 + 1 + 1 + 1 = 4

    NO PHYSICS:
    This lemma makes ZERO assumptions about quantum mechanics, locality, causality,
    or hidden variables. It's pure correlation arithmetic.

    Establishes the absolute maximum for CHSH. If someone claims CHSH > 4, they're
    either computing wrong or violating probability theory (correlations exceeding ±1).

    Find trials where |S| > 4. Can't happen - would require some |E_xy| > 1, which
    violates correlation_bound_1.
*)
Lemma chsh_algebraic_bound :
  forall trials,
    Qabs (chsh_from_trials trials) <= 4.
Proof.
  intro trials.
  unfold chsh_from_trials.
  pose (e00 := compute_correlation (filter_trials trials 0 0)).
  pose (e01 := compute_correlation (filter_trials trials 0 1)).
  pose (e10 := compute_correlation (filter_trials trials 1 0)).
  pose (e11 := compute_correlation (filter_trials trials 1 1)).
  (* Apply triangle inequality *)
  eapply Qle_trans.
  { unfold e00, e01, e10, e11. apply Qabs_4_triangle. }
  (* Each correlation bounded by 1 *)
  replace 4 with (1 + 1 + 1 + 1) by reflexivity.
  unfold e00, e01, e10, e11.
  assert (H00: Qabs (compute_correlation (filter_trials trials 0 0)) <= 1) by apply correlation_bound_1.
  assert (H01: Qabs (compute_correlation (filter_trials trials 0 1)) <= 1) by apply correlation_bound_1.
  assert (H10: Qabs (compute_correlation (filter_trials trials 1 0)) <= 1) by apply correlation_bound_1.
  assert (H11: Qabs (compute_correlation (filter_trials trials 1 1)) <= 1) by apply correlation_bound_1.
  
  (* Sum the bounds: if a≤1, b≤1, c≤1, d≤1 then a+b+c+d ≤ 4 *)
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  - exact H00.
  - exact H01.
  - exact H10.
  - exact H11.
Qed.

Close Scope Q_scope.
Open Scope nat_scope.

(** locally_deterministic_strategy: Defining "local hidden variable models".

    WHAT THIS IS:
    A strategy is "local" if Alice's output depends ONLY on her input x (not on
    Bob's input y), and Bob's output depends ONLY on his input y (not on Alice's
    input x). This is the mathematical definition of "factorizable correlations"
    or "local realism".

    THE PROPERTIES:
    1. a_func x y1 = a_func x y2 for all y1, y2
       → Alice's function doesn't actually use the y argument
       → Her output is independent of Bob's input
    2. b_func x1 y = b_func x2 y for all x1, x2
       → Bob's function doesn't actually use the x argument
       → His output is independent of Alice's input

    This is the CLASSICAL world. No entanglement, no spooky action at a distance,
    no cross-input dependence. Alice makes a measurement, gets a result that depends
    only on what SHE chose to measure. Bob's choice doesn't affect her result.

    THE BELL INSIGHT:
    Bell's theorem says: local strategies satisfy CHSH ≤ 2. The tight bound is
    2 (proven in CHSH.v by exhaustive 16-case analysis). This definition is the
    local/deterministic side of that comparison.

    THE REPRESENTATION:
    We represent strategies as functions a_func(x,y) and b_func(x,y). For local
    strategies, these functions ignore their second argument:
    - a_func(x, y) = a(x) for some function a : nat → nat
    - b_func(x, y) = b(y) for some function b : nat → nat

    CONNECTION TO μ-COST:
    This definition itself does not mention μ. Any theorem connecting locality to
    μ=0 has to be proved elsewhere.

    Find a strategy satisfying this definition where CHSH > 2. Can't happen -
    Bell's inequality guarantees CHSH ≤ 2 for local strategies.
*)
Definition locally_deterministic_strategy (a_func b_func : nat -> nat -> nat) : Prop :=
  (* Alice's output depends only on her input x *)
  (* Bob's output depends only on his input y *)
  (forall x y1 y2, a_func x y1 = a_func x y2) /\
  (forall x1 x2 y, b_func x1 y = b_func x2 y).

Open Scope Q_scope.

(** chsh_local_bound: Local strategies satisfy the loose algebraic bound.
    If trials are generated by a locally_deterministic_strategy, then |CHSH| ≤ 4.

    WHY ONLY 4, NOT 2:
    This lemma proves the ALGEBRAIC bound (4), not the TIGHT classical bound (2).
    The tight bound CHSH ≤ 2 for local strategies is Bell's inequality, proven
    in coq/kernel/CHSH.v via exhaustive 16-case analysis over all deterministic
    strategies.

    This lemma is weaker than Bell's inequality. It is useful only when a caller
    needs the universal algebraic ceiling specialized to local-looking trials.
    Simply delegates to chsh_algebraic_bound. The locality assumption
    (locally_deterministic_strategy) is NOT USED in this proof because the
    algebraic bound holds for ALL correlations, not just local ones.

    Because chsh_algebraic_bound already did the work. This lemma just specializes
    it to the local case. The INTERESTING bound (CHSH ≤ 2 for local) requires
    much more work - see CHSH.v for that proof.

    WHAT THE ASSUMPTIONS MEAN:
    - locally_deterministic_strategy a_func b_func: The strategy is factorizable
    - forall t, In t trials → ...: Each trial's outputs come from the strategy
    - We pass O (zero) as the "irrelevant" argument because local strategies
      ignore it (Alice's a_func(x, _) doesn't use second arg, Bob's b_func(_, y)
      doesn't use first arg)

    THE ACTUAL CLASSICAL BOUND:
    For the tight bound CHSH ≤ 2 for local strategies, see:
    - coq/kernel/CHSH.v: Proves it via 16-case exhaustive search
    - coq/kernel/ClassicalBound.v: tracks achievability claims for the classical side

    Do not read this lemma as that theorem. It only proves <= 4.

    Find a local strategy with CHSH > 4. Impossible - would violate the algebraic
    bound chsh_algebraic_bound, which holds for all correlations.
 The proof delegates to chsh_algebraic_bound - short because the work
    is already done. The SAFE comment means Z.abs usage is in the delegated lemma,
    which has been verified.
*)
(** Direct specialization of [chsh_algebraic_bound]; the locality hypotheses are
    present for the interface but are not used by this proof. *)
(* SAFE: short proof because chsh_algebraic_bound already does the work; delegates to that lemma *)
Lemma chsh_local_bound :
  forall trials a_func b_func,
    locally_deterministic_strategy a_func b_func ->
    (* trials generated by local strategy *)
    (forall t, In t trials ->
       t.(trial_a) = a_func t.(trial_x) O /\
       t.(trial_b) = b_func O t.(trial_y)) ->
    Qabs (chsh_from_trials trials) <= 4%Q.
Proof.
  intros trials a_func b_func [Ha_local Hb_local] Htrials_from_strategy.
  (* Algebraic bound for CHSH expression *)
  (* Note: The tight classical bound is 2 (Bell's theorem), *)
  (* proven in coq/kernel/CHSH.v via exhaustive 16-case analysis *)
  (* Here we prove only the looser algebraic bound 4. *)
  
  apply chsh_algebraic_bound.
Qed.

(** ** Connection to VM μ-cost

    Key observation: CHSH computation above is INDEPENDENT of μ-ledger.
    
    This separation allows us to:
    1. Define μ=0 programs operationally (next file)
    2. Ask: what is max CHSH achievable with μ=0?
    3. Prove any answer in a file that actually states the μ-cost hypotheses.
       This extraction file only computes S.
    *)
