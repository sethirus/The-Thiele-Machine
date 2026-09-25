(** CHSHExtraction: compute the CHSH statistic from bounded VM execution.

    The file records the [instr_chsh_trial] payloads visited by a supplied
    fuel-bounded execution, groups them by input pair, computes the four
    correlations, and combines them as [E00 + E01 + E10 - E11].

    The definitions are arithmetic over extracted natural-number payloads.
    They do not model quantum mechanics, Tsirelson's bound, locality, or the
    physical meaning of a measurement. They also do not authenticate an
    externally supplied trace. Those claims, where made elsewhere, require
    separate hypotheses and proofs.

    The result is independent of the VM's [mu] accounting field. This file
    therefore supplies the list-level computation that later developments can
    combine with their own cost and semantic assumptions.
*)

From Coq Require Import List QArith Qabs Lia Qround Qminmax Lra.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof MuCostModel.

(** CHSHTrial bundles the four natural-number fields carried by one
    [instr_chsh_trial]: two input labels and two output labels.

    Extraction checks the representation-specific validity predicate before
    constructing this record. Within this file the fields are data values; no
    physical interpretation is built into the record. [compute_correlation]
    and [chsh_from_trials] consume the resulting list. *)
Record CHSHTrial := {
  trial_x : nat;  (* Alice's input: 0 or 1 *)
  trial_y : nat;  (* Bob's input: 0 or 1 *)
  trial_a : nat;  (* Alice's output: 0 or 1 *)
  trial_b : nat   (* Bob's output: 0 or 1 *)
}.

(** extract_chsh_trials_from_trace: execute the bounded VM run and collect
    valid CHSH trial payloads.

    The evaluator reads the instruction at the current PC, applies [vm_apply],
    and records only valid [instr_chsh_trial] instructions. Jumps and other
    control-flow instructions therefore affect which instruction is visited.
    Fuel bounds the recursion; this function does not claim unbounded
    termination or provide receipt authentication.

    The algorithm is:
    1. Look at current PC position in trace
    2. Step the current instruction using the actual vm_apply semantics
    3. If the executed instruction is a valid instr_chsh_trial: record (x,y,a,b)
    4. Otherwise: continue without recording a trial
    5. Repeat until fuel is exhausted or the current PC is outside the trace

    Coq requires proof of termination. Fuel bounds the number of steps. In
    practice, set fuel ≥ trace length.

    [vm_apply] supplies the same instruction semantics used by the VM. Invalid
    trial payloads are not recorded. Receipt integrity and any statistical
    interpretation are separate interfaces.
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
    (** categorical / morphism opcodes *)
    | dst src_mod dst_mod coupling_idx mu_delta
    | dst m1_id m2_id mu_delta
    | dst module mu_delta
    | morph_id mu_delta
    | morph_id property cert mu_delta
    | dst f_id g_id mu_delta
    | dst morph_id selector mu_delta
    | mu_delta
    | mu_delta
    | mu_delta same_g5 diff_g5
    | mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5
    | mu_delta same_g1 diff_g1 same_g2 diff_g2 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5]; simpl in Hexec; try discriminate.
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
    (** categorical / morphism opcodes *)
    | dst src_mod dst_mod coupling_idx mu_delta
    | dst m1_id m2_id mu_delta
    | dst module mu_delta
    | morph_id mu_delta
    | morph_id property cert mu_delta
    | dst f_id g_id mu_delta
    | dst morph_id selector mu_delta
    | mu_delta
    | mu_delta
    | mu_delta same_g5 diff_g5
    | mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5
    | mu_delta same_g1 diff_g1 same_g2 diff_g2 same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5]; simpl in Hexec; try discriminate.
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

(** filter_trials: retain the trials whose two input fields equal the supplied
    [x] and [y]. The four CHSH buckets are obtained by applying this function
    to the four input pairs. *)
Definition filter_trials (trials : list CHSHTrial) (x y : nat) : list CHSHTrial :=
  filter (fun t => Nat.eqb t.(trial_x) x && Nat.eqb t.(trial_y) y) trials.

(** [compute_correlation] counts matching and non-matching output pairs and
    returns their signed difference divided by the list length. The empty list
    is assigned correlation zero. The result is a rational number, so this
    definition performs no floating-point rounding and makes no claim about a
    sampling distribution. *)
Definition compute_correlation (trials : list CHSHTrial) : Q :=
  match trials with
  | [] => 0%Q
  | _ =>
      let same_count := length (filter (fun t => Nat.eqb t.(trial_a) t.(trial_b)) trials) in
      let diff_count := length (filter (fun t => negb (Nat.eqb t.(trial_a) t.(trial_b))) trials) in
      let total := length trials in
      (((Z.of_nat same_count # 1) - (Z.of_nat diff_count # 1)) / (Z.of_nat total # 1))%Q
  end.

(** [chsh_from_trials] filters the list into the four input buckets and returns
    the rational combination [E00 + E01 + E10 - E11]. The list-level bound
    proved below is the algebraic bound [|S| <= 4]; tighter bounds belong to
    developments that supply additional assumptions. *)
Definition chsh_from_trials (trials : list CHSHTrial) : Q :=
  let e00 := compute_correlation (filter_trials trials 0 0) in
  let e01 := compute_correlation (filter_trials trials 0 1) in
  let e10 := compute_correlation (filter_trials trials 1 0) in
  let e11 := compute_correlation (filter_trials trials 1 1) in
  (e00 + e01 + e10 - e11)%Q.

(** chsh_from_vm_trace: compose bounded trace extraction with the list-level
    CHSH calculation. The result is a rational value for the trials visited by
    the supplied fuel-bounded execution. *)
Definition chsh_from_vm_trace
  (fuel : nat) (trace : list vm_instruction) (s_init : VMState) : Q :=
  let trials := extract_chsh_trials_from_trace fuel trace s_init in
  chsh_from_trials trials.

(** Properties of CHSH Computation - Sanity Checks *)

Close Scope Q_scope.
Open Scope nat_scope.

(** [trial_partition] states that the matching-output and differing-output
    filters partition every trial list. The proof is induction on the list and
    a case split on the Boolean equality test. *)
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

(** filter_length_le: filtering a list does not increase its length.

    Filtering removes elements that do not match its predicate; it does not add
    elements. The proof is induction over the input list.
    Induction. Base case: empty list filters to empty. Inductive case: either
    predicate true (keep element, length stays same or increases by 1) or false
    (remove element, filtered length < original). Either way, bound holds.

    This lemma is used by the trial-bucket bounds.
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

(** [Qabs_4_triangle] is the rational four-term triangle inequality used by
    the list-level CHSH bound. It is obtained by repeated use of the ordinary
    triangle inequality and [Qabs_opp]. *)
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

(** [correlation_bound_1] bounds the rational correlation of every trial list by
    one in absolute value. The proof uses [trial_partition] to relate the two
    natural-number counts, then transfers the resulting integer inequality to
    rationals. The empty-list branch is handled directly by the definition. *)
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

(** [chsh_algebraic_bound] combines [Qabs_4_triangle] with
    [correlation_bound_1] to prove the list-level inequality [|S| <= 4]. It
    uses no locality, quantum, causal, or physical premise. The tighter local
    bound is proved separately in [CHSH.v]. *)
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

(** [locally_deterministic_strategy] records the factorization condition used by
    the interface below: Alice's output is unchanged when Bob's input changes,
    and Bob's output is unchanged when Alice's input changes. This predicate is
    a definition over two natural-valued functions. The tight classical CHSH
    theorem is proved in [CHSH.v]; this file does not derive it from this
    predicate. *)
Definition locally_deterministic_strategy (a_func b_func : nat -> nat -> nat) : Prop :=
  (* Alice's output depends only on her input x *)
  (* Bob's output depends only on his input y *)
  (forall x y1 y2, a_func x y1 = a_func x y2) /\
  (forall x1 x2 y, b_func x1 y = b_func x2 y).

Open Scope Q_scope.

(** [chsh_local_bound] exposes the algebraic [|S| <= 4] result under a local
    strategy interface. Its locality and generation hypotheses are not used by
    the proof because [chsh_algebraic_bound] already holds for every trial list.
    The distinct tight bound [|S| <= 2] is the result in [CHSH.v]. *)
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
