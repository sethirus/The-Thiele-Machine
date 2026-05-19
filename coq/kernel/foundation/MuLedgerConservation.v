From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** MuLedgerConservation: μ never decreases.

    The μ-ledger is the whole point. If it could decrease, No Free Insight would
    be meaningless — you could "borrow" μ-cost, use the structure, then get a
    refund. This file proves it can't happen. For any execution trace, the final
    μ equals the initial μ plus the sum of instruction costs that actually ran.
    A step changes μ by exactly its declared cost. No refund path exists in
    vm_apply: μ_final = μ_init + Σ(instruction_cost).

    vm_apply_mu: single step changes μ by exactly instruction_cost.
    vm_step_respects_mu_ledger: step relation preserves ledger conservation.
    ledger_conserved: inductive property over execution traces.
    bounded_model_mu_ledger_conservation: conservation law for bounded runs.

    Without conservation you could cheat. With conservation, every bit of
    structural insight costs μ, permanently. Irreversibility is built in.

    Find ANY instruction sequence where μ decreases. Find ANY execution where
    μ_final is not μ_init + Σ(costs of the executed instructions). If you can,
    the whole model breaks. The proofs won't compile if this is violated.

    *)

(** Ledger extraction from bounded executions. *)

Fixpoint ledger_entries (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          instruction_cost instr ::
          ledger_entries fuel' trace (vm_apply s instr)
      | None => []
      end
  end.

Fixpoint bounded_run (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : list VMState :=
  match fuel with
  | 0 => [s]
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          s :: bounded_run fuel' trace (vm_apply s instr)
      | None => [s]
      end
  end.

(** A bounded run is never empty. Even with zero fuel or a missing instruction,
    the current state is still the head of the trace. *)
Lemma bounded_run_head :
  forall fuel trace s,
    exists rest, bounded_run fuel trace s = s :: rest.
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - exists []. reflexivity.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
    + exists (bounded_run fuel trace (vm_apply s instr)). reflexivity.
    + exists []. reflexivity.
Qed.

(** vm_apply_mu: Every instruction changes μ by exactly its declared cost.
    This is the foundational lemma for μ-conservation. It states that when
    you apply ANY instruction to ANY state, the resulting μ value is the
    original μ plus the instruction's cost. No more, no less. If the cost is
    zero, μ stays put.

    Case analysis on the [vm_instruction] constructors. Each instruction's
    semantics in [VMStep.v] computes new_mu = old_mu + instruction_cost. This
    lemma extracts that fact from the executable function.

    WHY THE PROOF IS UGLY:
    Coq makes us handle every instruction separately. There are conditional
    branches for graph/morphism/tensor checks and certificate assertions, but
    in EVERY branch, the μ update is the same: add the cost. The proof cases
    through those branches and checks the arithmetic. It's mechanical, but
    this is the bolt that holds the ledger shut.
    - vm_step_respects_mu_ledger
    - bounded_model_mu_ledger_conservation
    - vm_mu_monotonic_single_step

    Find an instruction where vm_apply changes μ by something other than
    instruction_cost. The proof breaks. The whole conservation law breaks.
*)
Lemma vm_apply_mu :
  forall s instr,
    (vm_apply s instr).(vm_mu) = s.(vm_mu) + instruction_cost instr.
Proof.
  intros s instr.
  destruct instr; unfold vm_apply; simpl; try reflexivity;
  try (unfold advance_state; simpl; reflexivity);
  try (unfold advance_state_rm; simpl; reflexivity);
  try (unfold advance_state_reveal; simpl; reflexivity);
  try (destruct (graph_add_module _ _ _) as [? ?]; unfold advance_state; simpl; reflexivity);
  try (destruct (chsh_bits_ok _ _ _ _) eqn:?; simpl; reflexivity);
  try (destruct (VMStep.tensor_indices_ok _ _) eqn:?; simpl; reflexivity);
  try (destruct (graph_lookup s.(vm_graph) src_mod) as [?|] eqn:?; simpl;
       [destruct (graph_lookup s.(vm_graph) dst_mod) as [?|] eqn:?; simpl;
        [destruct (graph_add_morphism s.(vm_graph) src_mod dst_mod empty_coupling_data false) as [? ?];
         unfold advance_state_rm; simpl; reflexivity
        |unfold advance_state; simpl; reflexivity]
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_lookup _ _) as [?|] eqn:?; simpl;
       [destruct (graph_lookup _ _) as [?|] eqn:?; simpl;
        [destruct (graph_add_morphism _ _ _ _ _) as [? ?]; simpl;
         unfold advance_state_rm; simpl; reflexivity
        |unfold advance_state; simpl; reflexivity]
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_compose_morphisms _ _ _) as [[? ?]|] eqn:?; simpl;
       [unfold advance_state_rm; simpl; reflexivity
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_add_identity _ _) as [[? ?]|] eqn:?; simpl;
       [unfold advance_state_rm; simpl; reflexivity
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_delete_morphism _ _) as [?|] eqn:?; simpl;
       [unfold advance_state; simpl; reflexivity
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_lookup_morphism _ _) as [?|] eqn:?; simpl;
       [unfold advance_state_rm, advance_state; simpl; reflexivity
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_tensor_morphisms _ _ _) as [[? ?]|] eqn:?; simpl;
       [unfold advance_state_rm; simpl; reflexivity
       |unfold advance_state; simpl; reflexivity]);
  try (destruct (lassert_check_ok _ _ _ _); simpl; unfold apply_cost; simpl; reflexivity);
  (* CHSH_LASSERT: two branches on column_contractive_check_witness,
     both charge S mu_delta via apply_cost *)
  try (destruct (column_contractive_check_witness _); simpl; unfold apply_cost; simpl; reflexivity);
  (* CHSH_LASSERT_1AB: two branches on column_contractive_check_q1ab_kernel,
     both charge S mu_delta via apply_cost *)
  try (destruct (column_contractive_check_q1ab_kernel _); simpl; unfold apply_cost; simpl; reflexivity);
  (* CHSH_LASSERT_1AB_G5: two branches on q1ab_g5_full_integer_check_kernel,
     both charge S mu_delta via apply_cost *)
  try (destruct (q1ab_g5_full_integer_check_kernel _ _ _); simpl; unfold apply_cost; simpl; reflexivity);
  (* CHSH_LASSERT_1AB_G345: two branches on q1ab_g345_full_integer_check_kernel,
     both charge S mu_delta via apply_cost *)
  try (destruct (q1ab_g345_full_integer_check_kernel _ _ _ _ _ _ _); simpl; unfold apply_cost; simpl; reflexivity);
  (* CHSH_LASSERT_1AB_G12345: two branches on q1ab_g12345_full_integer_check_kernel,
     both charge S mu_delta via apply_cost *)
  try (destruct (q1ab_g12345_full_integer_check_kernel _ _ _ _ _ _ _ _ _ _ _); simpl; unfold apply_cost; simpl; reflexivity).
  (* JNEZ: two branches, both use apply_cost *)
  destruct (read_reg _ _ =? 0); simpl;
    [unfold advance_state; simpl; reflexivity
    | unfold jump_state; simpl; reflexivity].
Qed.

Fixpoint ledger_conserved (states : list VMState) (entries : list nat)
  : Prop :=
  match states, entries with
  | s :: s' :: rest, delta :: entries' =>
      s'.(vm_mu) = s.(vm_mu) + delta /\
      ledger_conserved (s' :: rest) entries'
  | [_], [] => True
  | _, _ => False
  end.

(** Opening a conserved ledger exposes either the next paid step or the
    finished one-state trace. There is no third shape hiding in the list. *)
Lemma ledger_conserved_tail :
  forall s states entries,
    ledger_conserved (s :: states) entries ->
    match states, entries with
    | s' :: rest_states, delta :: rest_entries =>
        s'.(vm_mu) = s.(vm_mu) + delta /\
        ledger_conserved (s' :: rest_states) rest_entries
    | [], [] => True
    | _, _ => False
    end.
Proof.
  intros s states entries H.
  destruct states as [|s' rest].
  - destruct entries as [|delta rest_entries]; simpl in *.
    + exact I.
    + now destruct H.
  - destruct entries as [|delta rest_entries]; simpl in *.
    + now destruct H.
    + destruct H as [Hstep Hrest]. split; auto.
Qed.

(** The next lemma isolates the per-instruction conservation law.
    It asserts that any single small-step transition must debit the
    µ-ledger by exactly the instruction's declared cost.  In particular
    a "free" step, one that changes [vm_mu] without the matching ledger
    delta, would violate [ledger_conserved]. So it cannot arise
    under the kernel semantics. *)

Theorem vm_step_respects_mu_ledger :
  forall s instr s',
    vm_step s instr s' ->
    ledger_conserved [s; s'] [instruction_cost instr].
Proof.
  intros s instr s' Hstep.
  simpl.
  split.
  - now apply vm_step_mu.
  - exact I.
Qed.

Fixpoint ledger_sum (entries : list nat) : nat :=
  match entries with
  | [] => 0
  | delta :: rest => delta + ledger_sum rest
  end.

(** ** Irreversibility counting

    Landauer's principle links logically irreversible operations to physical
    entropy production.  To expose that connection, we conservatively count
    irreversible bit events per VM instruction and show the µ-ledger lower
    bounds that count for any bounded execution.  The count is deliberately
    minimal: each instruction contributes at most one irreversible bit, and
    only when it charges a positive µ-cost. That keeps the ledger bound tied
    to the cost model instead of smuggling in extra physics. *)

Definition irreversible_bits (instr : vm_instruction) : nat :=
  if instruction_cost instr =? 0 then 0 else 1.

(** The irreversible-bit counter is intentionally weak: zero-cost instructions
    count as zero, and every positive-cost instruction has at least enough μ
    to pay for the single bit we count. *)
Lemma irreversible_bits_le_cost :
  forall instr, irreversible_bits instr <= instruction_cost instr.
Proof.
  intros instr. unfold irreversible_bits.
  destruct (instruction_cost instr =? 0) eqn:Hzero; simpl.
  - apply Nat.eqb_eq in Hzero. subst. lia.
  - apply Nat.eqb_neq in Hzero. lia.
Qed.

Fixpoint irreversible_count (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          irreversible_bits instr +
          irreversible_count fuel' trace (vm_apply s instr)
      | None => 0
      end
  end.

(** Summing per-step costs bounds the conservative irreversible-bit count. *)
Lemma ledger_sum_bounds_irreversible_count :
  forall fuel trace s,
    irreversible_count fuel trace s <= ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - lia.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl.
    + specialize (IH trace (vm_apply s instr)).
      pose proof (irreversible_bits_le_cost instr) as Hbound.
      lia.
    + lia.
Qed.

(** The µ-ledger can now be quoted directly as a bound on the irreversible
    bit events in any bounded execution.  Packaging the previous lemma with a
    more public-facing name makes the Landauer link explicit for downstream
    references. *)

Theorem mu_ledger_bounds_irreversible_events :
  forall fuel trace s,
    irreversible_count fuel trace s <= ledger_sum (ledger_entries fuel trace s).
Proof.
  apply ledger_sum_bounds_irreversible_count.
Qed.

(** Component-wise accumulation for sighted/blind decompositions.
    The caller supplies the projection, so this file only proves the arithmetic
    split. It does not decide which instructions are "blind" or "sighted." *)

Fixpoint ledger_component_sum (component : vm_instruction -> nat)
  (fuel : nat) (trace : list vm_instruction) (s : VMState) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          component instr +
          ledger_component_sum component fuel' trace (vm_apply s instr)
      | None => 0
      end
  end.

(** This is the file's main conservation theorem: the bounded trace is
    step-by-step ledger-conserved, and the final μ equals the initial μ plus
    the ledger sum. *)

Theorem bounded_model_mu_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s) /\
  (run_vm fuel trace s).(vm_mu) =
    s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - split; [exact I | rewrite Nat.add_0_r; reflexivity].
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl.
    + destruct (IH trace (vm_apply s instr)) as [IH_ledger IH_run].
      destruct (bounded_run_head fuel trace (vm_apply s instr)) as [rest Hrun].
      simpl.
      rewrite Hrun in IH_ledger.
      rewrite Hrun.
      split; [split; [apply vm_apply_mu | exact IH_ledger]
            | rewrite IH_run; rewrite vm_apply_mu; lia].
    + split; [exact I | rewrite Nat.add_0_r; reflexivity].
Qed.

(** The per-step half of [bounded_model_mu_ledger_conservation]. *)
Corollary bounded_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  apply (proj1 (bounded_model_mu_ledger_conservation fuel trace s)).
Qed.

(** The scalar μ balance from the main theorem, quoted without the trace proof. *)
Corollary run_vm_mu_conservation :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) =
    s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  apply (proj2 (bounded_model_mu_ledger_conservation fuel trace s)).
Qed.

(** The final μ has enough room to pay for every irreversible bit event counted
    by [irreversible_count]. *)
Corollary run_vm_mu_bounds_irreversibility :
  forall fuel trace s,
    s.(vm_mu) + irreversible_count fuel trace s <= (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  rewrite run_vm_mu_conservation.
  specialize (ledger_sum_bounds_irreversible_count fuel trace s) as Hbound.
  lia.
Qed.

(** Restating the bound as a delta makes it easier to line up with
    physical arguments about entropy production: the µ-ledger increase over
    an execution interval must dominate the number of irreversible bit
    events recorded by the conservative counter. *)

Theorem run_vm_irreversibility_gap :
  forall fuel trace s,
    irreversible_count fuel trace s <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s.
  rewrite run_vm_mu_conservation.
  specialize (ledger_sum_bounds_irreversible_count fuel trace s) as Hbound.
  lia.
Qed.

(** A quotable alias so downstream developments can refer to the same bound
    without unpacking the µ-delta notation.  The direction matters: the counted
    irreversible events force at least that much µ-growth. *)
Theorem vm_irreversible_bits_lower_bound :
  forall fuel trace s,
    irreversible_count fuel trace s <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  apply run_vm_irreversibility_gap.
Qed.

(** Any prefix is just another bounded run, so it gets the same μ balance. *)
Corollary bounded_prefix_mu_balance :
  forall fuel trace s k,
    k <= fuel ->
    (run_vm k trace s).(vm_mu) =
      s.(vm_mu) + ledger_sum (ledger_entries k trace s).
Proof.
  intros fuel trace s k _.
  apply run_vm_mu_conservation.
Qed.

(** ** Multi-step µ-monotonicity

    The µ-accumulator never decreases during execution. This follows from
    the fact that [instruction_cost] is a natural number: each step either
    preserves [vm_mu] or increases it. *)

Theorem vm_mu_monotonic_single_step :
  forall s instr,
    s.(vm_mu) <= (vm_apply s instr).(vm_mu).
Proof.
  intros s instr.
  rewrite vm_apply_mu.
  lia.
Qed.

(** Running the VM for a bounded number of steps cannot lower μ. *)
Theorem run_vm_mu_monotonic :
  forall fuel trace s,
    s.(vm_mu) <= (run_vm fuel trace s).(vm_mu).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - lia.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
    + specialize (IH trace (vm_apply s instr)).
      assert (s.(vm_mu) <= (vm_apply s instr).(vm_mu)) as Hstep.
      { apply vm_mu_monotonic_single_step. }
      lia.
    + lia.
Qed.

(** Extended multi-step monotonicity theorems: The µ-accumulator is preserved
    across execution prefixes and compositional execution phases. *)

Theorem run_vm_mu_monotonic_prefix :
  forall k1 k2 trace s,
    k1 <= k2 ->
    (run_vm k1 trace s).(vm_mu) <= (run_vm k2 trace s).(vm_mu).
Proof.
  intros k1. induction k1 as [|k1 IHk1]; intros k2 trace s Hle.
  - simpl. apply run_vm_mu_monotonic.
  - destruct k2 as [|k2].
    + lia.
    + simpl run_vm.
      destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
      * apply (IHk1 k2 trace (vm_apply s instr)). lia.
      * simpl. lia.
Qed.

(** Splitting an execution into two fuel windows cannot make the later window
    cheaper than the earlier one. *)
Theorem run_vm_mu_monotonic_composition :
  forall m n trace s,
    s.(vm_mu) <= (run_vm m trace s).(vm_mu) /\
    (run_vm m trace s).(vm_mu) <= (run_vm (m + n) trace s).(vm_mu).
Proof.
  intros m n trace s.
  split.
  - (* First part: s.(vm_mu) <= (run_vm m trace s).(vm_mu) *)
    apply run_vm_mu_monotonic.
  - (* Second part: (run_vm m trace s).(vm_mu) <= (run_vm (m + n) trace s).(vm_mu) *)
    (* Note: run_vm (m + n) = run_vm n (run_vm m s) by the definition of run_vm *)
    assert (forall k1 k2, k1 <= k1 + k2) as Hle by lia.
    apply (run_vm_mu_monotonic_prefix m (m + n) trace s).
    lia.
Qed.

(** I split the instruction cost into two components here. The only assumption
    is arithmetic: the two projections add back up to [instruction_cost]. That
    lets later files talk about blind search work versus sighted certificate
    validation without changing the ledger theorem. *)

(* INQUISITOR NOTE: abstract section — parameterized theorem.
   Section Variables here are explicit forall premises when the section closes.
   mu_component_split is not a machine-specific assumption; it holds for any
   cost decomposition. All theorems export as explicit forall statements. *)
Section MuDecomposition.

Variable mu_blind_component mu_sighted_component : vm_instruction -> nat.
Variable mu_component_split : forall instr,
  instruction_cost instr =
    mu_blind_component instr + mu_sighted_component instr.

(** If each instruction cost splits into blind plus sighted pieces, then the
    whole ledger sum splits the same way. *)
Lemma ledger_sum_component_decompose :
  forall fuel trace s,
    ledger_sum (ledger_entries fuel trace s) =
      ledger_component_sum mu_blind_component fuel trace s +
      ledger_component_sum mu_sighted_component fuel trace s.
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - reflexivity.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup.
    + simpl.
      rewrite mu_component_split.
      simpl.
      specialize (IH trace (vm_apply s instr)).
      rewrite IH.
      lia.
    + reflexivity.
Qed.

(** The μ balance can be quoted in terms of the two component sums. *)
Theorem bounded_run_mu_decomposition :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) =
      s.(vm_mu) +
      ledger_component_sum mu_blind_component fuel trace s +
      ledger_component_sum mu_sighted_component fuel trace s.
Proof.
  intros fuel trace s.
  destruct (bounded_model_mu_ledger_conservation fuel trace s)
    as [_ Hmu].
  rewrite Hmu.
  rewrite ledger_sum_component_decompose.
  lia.
Qed.

(** The blind component alone is bounded by the total μ increase. *)
Corollary bounded_run_blind_component_le_total :
  forall fuel trace s,
    s.(vm_mu) + ledger_component_sum mu_blind_component fuel trace s <=
    (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  rewrite bounded_run_mu_decomposition.
  remember (ledger_component_sum mu_blind_component fuel trace s) as blind_sum.
  remember (ledger_component_sum mu_sighted_component fuel trace s) as sighted_sum.
  lia.
Qed.

(** The sighted component alone is bounded by the total μ increase. *)
Corollary bounded_run_sighted_component_le_total :
  forall fuel trace s,
    s.(vm_mu) + ledger_component_sum mu_sighted_component fuel trace s <=
    (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  rewrite bounded_run_mu_decomposition.
  remember (ledger_component_sum mu_blind_component fuel trace s) as blind_sum.
  remember (ledger_component_sum mu_sighted_component fuel trace s) as sighted_sum.
  lia.
Qed.

End MuDecomposition.

(** Bridging the prophecy seal and ledger tail.
    This abstract model keeps the hash algebra uninterpreted. It only proves
    the structural fact this file actually needs: the two certificate paths
    agree for a singleton ledger. For longer ledgers, [final_digest ledger]
    reads the tail while [final_digest (rev ledger)] reads the head, so no
    general equality is claimed here. *)

(* INQUISITOR NOTE: abstract interface section — parameterized theorem.
   Hash, combine, default are type/value parameters for abstract hash algebra.
   All theorems export as explicit forall when section closes. *)
Section GestaltIsomorphism.

  Variable Hash : Type.
  Variable combine : Hash -> Hash -> Hash.
  Variable default : Hash.

  Definition final_digest (ledger : list Hash) : Hash :=
    match ledger with
    | [] => default
    | _ => List.last ledger default
    end.

  Definition gestalt_certificate (seal : Hash) (ledger : list Hash) : Hash :=
    combine seal (final_digest ledger).

  (** [computed_isomorphism] takes a different path on purpose: it digests the
      reversed ledger. That means it agrees with [gestalt_certificate] for a
      singleton ledger, not for arbitrary ledgers. *)
  Definition computed_isomorphism (seal : Hash) (ledger : list Hash) : Hash :=
    combine seal (final_digest (rev ledger)).

  (** Equality depends on the fact that [final_digest] returns
      [List.last l default], and [List.last (rev l) default]
      equals [hd default l] for non-empty lists.  For the
      empty case both reduce to [default].  We prove this by
      structural induction on the ledger. *)
  Lemma final_digest_rev :
    forall ledger,
      final_digest (rev ledger) = match ledger with
                                  | [] => default
                                  | h :: _ => h
                                  end.
  Proof.
    intro ledger. unfold final_digest.
    destruct ledger as [| h t].
    - simpl. reflexivity.
    - destruct (rev (h :: t)) eqn:Hrev.
      + (* rev (h :: t) = [] is impossible *)
        apply (f_equal (@List.length _)) in Hrev.
        rewrite rev_length in Hrev. simpl in Hrev. lia.
      + (* rev (h :: t) = h0 :: l *)
        (* rev (h :: t) = rev t ++ [h] definitionally *)
        assert (Happ : rev (h :: t) = rev t ++ [h]) by reflexivity.
        rewrite Hrev in Happ.
        (* Happ : h0 :: l = rev t ++ [h] *)
        rewrite Happ.
        apply List.last_last.
  Qed.

  (** When the ledger has a single canonical entry, the two constructions agree.
      That is the whole theorem. Anything stronger would need a stronger
      digest definition or an explicit ledger-shape assumption. *)
  Lemma gestalt_matches_isomorphism_singleton :
    forall seal entry,
      gestalt_certificate seal [entry] = computed_isomorphism seal [entry].
  Proof.
    intros seal entry.
    unfold gestalt_certificate, computed_isomorphism.
    simpl. unfold final_digest. simpl. reflexivity.
  Qed.

End GestaltIsomorphism.
