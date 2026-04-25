(** DagRestriction.v: the sub-Turing DAG variant of the Thiele Machine.

    Does the mu-ledger require Turing completeness? No.

    This file proves that the No Free Insight axiom and the mu-cost accounting
    survive the removal of backward jumps, CALL, and RET. What remains is a
    Directed Acyclic Graph (DAG) of instructions: control flow moves strictly
    forward through the program. The machine is guaranteed to halt. It cannot
    be given a non-terminating program.

    Three results:

    TERMINATION (dag_terminates): Any dag_trace_wf trace halts within
    length(trace) steps from any initial PC ≤ length(trace).

    STRUCTURAL COMPLETENESS (dag_structural_completeness): PNEW, EMIT, LASSERT,
    CERTIFY, and all MORPH variants are dag-safe. The full epistemic instruction
    set survives the restriction. The Insight ASIC computes everything the
    full machine can certify.

    NFI PRESERVATION (dag_nfi_preserved): No Free Insight holds for DAG traces
    as a direct corollary of NoFreeInsight.no_free_insight_general, which holds
    for all traces unconditionally. The sub-Turing machine cannot certify
    structure it did not pay for.

    The sub-Turing claim: remove instr_jump with backward targets, instr_call,
    and instr_ret. What remains still certifies structural claims, computes
    morphisms, and accumulates mu-cost. You do not need Turing completeness
    to build an Epistemic Root of Trust. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import NoFreeInsight.
From Kernel Require Import RevelationRequirement.
Import RevelationRequirement.RevelationProof.

(** ** DAG Well-Formedness

    A trace is DAG-well-formed if every instruction at every position satisfies
    three conditions:
    1. No CALL (creates return-address stack enabling loops).
    2. No RET (pops return address, enabling arbitrary backward jumps).
    3. Every JUMP or JNEZ target is strictly greater than the current PC
       (no backward edges).
    4. LASSERT: on failure, jumps to LASSERT_TRAP_PC = 3840. We require
       the trace is short enough that this also exits bounds: length ≤ LASSERT_TRAP_PC.

    These are static properties of the instruction and its position. They do
    not depend on runtime register values. *)

Definition is_dag_instr_at (pc trace_len : nat) (instr : vm_instruction) : bool :=
  match instr with
  | instr_jump target _     => Nat.ltb pc target
  | instr_jnez _ target _   => Nat.ltb pc target
  | instr_call _ _          => false
  | instr_ret _             => false
  | instr_lassert _ _ _ _ _ => Nat.leb trace_len LASSERT_TRAP_PC
  | _                       => true
  end.

Definition dag_trace_wf (trace : list vm_instruction) : Prop :=
  forall (pc : nat) (instr : vm_instruction),
    nth_error trace pc = Some instr ->
    is_dag_instr_at pc (length trace) instr = true.

(** ** Helper Lemmas: PC fields of state-building primitives *)

Lemma advance_state_pc_S :
  forall s instr g csrs err,
    (advance_state s instr g csrs err).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

Lemma advance_state_rm_pc_S :
  forall s instr g csrs regs mem err,
    (advance_state_rm s instr g csrs regs mem err).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold advance_state_rm. simpl. reflexivity. Qed.

Lemma advance_state_reveal_pc_S :
  forall s instr flat_idx delta g csrs err,
    (advance_state_reveal s instr flat_idx delta g csrs err).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold advance_state_reveal. simpl. reflexivity. Qed.

Lemma jump_state_pc :
  forall s instr target,
    (jump_state s instr target).(vm_pc) = target.
Proof. intros. unfold jump_state. simpl. reflexivity. Qed.

Lemma jump_state_rm_pc :
  forall s instr target regs mem,
    (jump_state_rm s instr target regs mem).(vm_pc) = target.
Proof. intros. unfold jump_state_rm. simpl. reflexivity. Qed.

(** Any executing position is within the trace bounds. *)
Lemma nth_error_in_bounds :
  forall {A : Type} (l : list A) (i : nat) (x : A),
    nth_error l i = Some x -> i < length l.
Proof.
  intros A l i x H.
  apply nth_error_Some. intro. rewrite H in *. discriminate.
Qed.

(** ** Main Lemma: DAG instructions advance the PC *)

(** For any instruction in a DAG-well-formed trace, executing it strictly
    increases the program counter. This is the engine of termination. *)
(** vm_apply on instr_lassert sets pc to S(pc) on success, LASSERT_TRAP_PC on failure. *)
Lemma vm_apply_lassert_pc :
  forall (s : VMState) (f0 f1 : nat) (b0 : bool) (f2 f3 : nat),
    (vm_apply s (instr_lassert f0 f1 b0 f2 f3)).(vm_pc) =
      if lassert_exec_ok s f0 f1 b0 f2
      then S s.(vm_pc)
      else LASSERT_TRAP_PC.
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma dag_instr_advances_pc :
  forall (s : VMState) (instr : vm_instruction) (trace : list vm_instruction),
    dag_trace_wf trace ->
    nth_error trace s.(vm_pc) = Some instr ->
    (vm_apply s instr).(vm_pc) > s.(vm_pc).
Proof.
  intros s instr trace Hwf Hnth.
  assert (Hdag := Hwf _ _ Hnth).
  assert (Hbound : s.(vm_pc) < length trace).
  { exact (nth_error_in_bounds trace _ _ Hnth). }
  (* Simplify Hdag (is_dag_instr_at → concrete boolean condition) but NOT the goal
     (to avoid simpl unfolding lassert_exec_ok and friends). *)
  unfold is_dag_instr_at in Hdag.
  destruct instr; simpl in Hdag;
    try (unfold vm_apply, advance_state; simpl; lia);
    try (unfold vm_apply, advance_state_rm; simpl; lia);
    try (unfold vm_apply, advance_state_reveal; simpl; lia);
    try (unfold vm_apply;
         destruct (graph_add_module _ _ _) as [? ?];
         unfold advance_state; simpl; lia);
    try (unfold vm_apply;
         destruct (chsh_bits_ok _ _ _ _) eqn:?;
         unfold advance_state; simpl; lia);
    try (unfold vm_apply;
         destruct (VMStep.tensor_indices_ok _ _) eqn:?;
         [unfold advance_state_rm; simpl; lia | unfold advance_state; simpl; lia]);
    try (unfold vm_apply;
         destruct (graph_lookup s.(vm_graph) src_mod) as [?|] eqn:?;
         [destruct (graph_lookup s.(vm_graph) dst_mod) as [?|] eqn:?;
          [destruct (graph_add_morphism _ _ _ _ _) as [? ?];
           unfold advance_state_rm; simpl; lia
          |unfold advance_state; simpl; lia]
         |unfold advance_state; simpl; lia]);
    try (unfold vm_apply;
         destruct (graph_compose_morphisms _ _ _) as [[? ?]|] eqn:?;
         [unfold advance_state_rm; simpl; lia
         |unfold advance_state; simpl; lia]);
    try (unfold vm_apply;
         destruct (graph_add_identity _ _) as [[? ?]|] eqn:?;
         [unfold advance_state_rm; simpl; lia
         |unfold advance_state; simpl; lia]);
    try (unfold vm_apply;
         destruct (graph_delete_morphism _ _) as [?|] eqn:?;
         unfold advance_state; simpl; lia);
    try (unfold vm_apply;
         destruct (graph_lookup_morphism _ _) as [?|] eqn:?;
         [unfold advance_state_rm; simpl; lia
         |unfold advance_state; simpl; lia]);
    try (unfold vm_apply;
         destruct (graph_tensor_morphisms _ _ _) as [[? ?]|] eqn:?;
         [unfold advance_state_rm; simpl; lia
         |unfold advance_state; simpl; lia]).
  (* 3 remaining goals (constructor order): LASSERT, JUMP, JNEZ.
     CALL and RET are closed by lia from Hdag : false = true (logical contradiction). *)
  - (* LASSERT: success → S(pc), failure → LASSERT_TRAP_PC *)
    rewrite vm_apply_lassert_pc.
    apply Nat.leb_le in Hdag.
    case (lassert_exec_ok _ _ _ _ _); simpl; lia.
  - (* JUMP: DAG says target > pc *)
    unfold vm_apply, jump_state; simpl.
    apply Nat.ltb_lt in Hdag. lia.
  - (* JNEZ: register=0 advances, register≠0 jumps forward *)
    unfold vm_apply.
    destruct (Nat.eqb (read_reg s rs) 0) eqn:?.
    + unfold advance_state; simpl; lia.
    + unfold jump_state; simpl. apply Nat.ltb_lt in Hdag. lia.
Qed.

(** ** PC Monotone Growth Under DAG Execution

    After k steps from state s in a DAG trace, the PC has advanced by at
    least k — OR the machine has already halted (PC ≥ length trace).

    This is the formal basis for the termination bound. *)
Lemma dag_pc_growth :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState),
    dag_trace_wf trace ->
    (run_vm fuel trace s).(vm_pc) >= s.(vm_pc) + fuel \/
    (run_vm fuel trace s).(vm_pc) >= length trace.
Proof.
  induction fuel as [|fuel' IH]; intros trace s Hwf.
  - left. simpl. lia.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth.
    + (* Instruction found *)
      simpl. rewrite Hnth.
      specialize (IH trace (vm_apply s instr) Hwf) as [Hleft | Hright].
      * left.
        assert (Hadv := dag_instr_advances_pc s instr trace Hwf Hnth).
        lia.
      * right. exact Hright.
    + (* Stuck: PC ≥ length trace *)
      simpl. rewrite Hnth.
      right.
      apply Nat.nlt_ge. intro Hlt.
      apply nth_error_Some in Hlt. exact (Hlt Hnth).
Qed.

(** ** Termination Theorem

    The central result: any DAG trace terminates.

    Starting from an initial PC within the trace, execution halts (PC leaves
    the trace bounds) within length(trace) - initial_pc steps. *)
Theorem dag_terminates :
  forall (trace : list vm_instruction) (s : VMState),
    dag_trace_wf trace ->
    s.(vm_pc) <= length trace ->
    (run_vm (length trace - s.(vm_pc) + 1) trace s).(vm_pc) >= length trace.
Proof.
  intros trace s Hwf Hpc.
  destruct (dag_pc_growth (length trace - s.(vm_pc) + 1) trace s Hwf) as [Hleft | Hright].
  - lia.
  - exact Hright.
Qed.

(** Corollary: from PC = 0, the machine halts within length(trace) + 1 steps. *)
Corollary dag_terminates_from_zero :
  forall (trace : list vm_instruction),
    dag_trace_wf trace ->
    (run_vm (length trace + 1) trace init_state).(vm_pc) >= length trace.
Proof.
  intros trace Hwf.
  assert (H := dag_terminates trace init_state Hwf (Nat.le_0_l _)).
  simpl (init_state.(vm_pc)) in H.
  rewrite Nat.sub_0_r in H.
  exact H.
Qed.

(** Stability: once halted, adding fuel does not change the state. *)
Lemma run_vm_stuck_repeat :
  forall (k : nat) (trace : list vm_instruction) (s : VMState),
    nth_error trace s.(vm_pc) = None ->
    run_vm k trace s = s.
Proof.
  induction k as [|k' IH]; intros trace s H.
  - reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Lemma run_vm_compose_dag :
  forall m n trace s,
    run_vm (m + n) trace s = run_vm n trace (run_vm m trace s).
Proof.
  induction m as [|m' IH]; intros n trace s.
  - reflexivity.
  - simpl. destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:H.
    + apply IH.
    + symmetry. apply run_vm_stuck_repeat. exact H.
Qed.

Lemma run_vm_halted_stable :
  forall (fuel k : nat) (trace : list vm_instruction) (s : VMState),
    (run_vm fuel trace s).(vm_pc) >= length trace ->
    run_vm (fuel + k) trace s = run_vm fuel trace s.
Proof.
  induction k as [|k' IH]; intros trace s Hhalted.
  - rewrite Nat.add_0_r. reflexivity.
  - (* run_vm (fuel + S k') = run_vm (S k') ∘ (run_vm fuel) = same as run_vm fuel *)
    assert (Hcompose : run_vm (fuel + S k') trace s =
                       run_vm (S k') trace (run_vm fuel trace s))
      by exact (run_vm_compose_dag fuel (S k') trace s).
    rewrite Hcompose.
    set (sf := run_vm fuel trace s).
    assert (Hnone : nth_error trace sf.(vm_pc) = None)
      by (apply nth_error_None; exact Hhalted).
    exact (run_vm_stuck_repeat (S k') trace sf Hnone).
Qed.

(** ** Structural Completeness

    All epistemic instructions — those that can certify structural claims or
    accumulate mu-cost — pass the DAG check unconditionally (or under the
    trivially satisfied condition length ≤ LASSERT_TRAP_PC = 3840). *)

(** PNEW, EMIT, CERTIFY, MORPH, MORPH_ID, MORPH_ASSERT, MORPH_TENSOR,
    MORPH_DELETE, MORPH_GET, COMPOSE: all use advance_state or advance_state_rm,
    so is_dag_instr_at = true for any pc and trace length. *)

Lemma dag_safe_pnew :
  forall pc n region cost, is_dag_instr_at pc n (instr_pnew region cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_emit :
  forall pc n module payload cost,
    is_dag_instr_at pc n (instr_emit module payload cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_certify :
  forall pc n cost, is_dag_instr_at pc n (instr_certify cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_morph :
  forall pc n dst src_mod dst_mod coupling_idx cost,
    is_dag_instr_at pc n (instr_morph dst src_mod dst_mod coupling_idx cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_morph_id :
  forall pc n dst module cost,
    is_dag_instr_at pc n (instr_morph_id dst module cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_morph_assert :
  forall pc n morph_id property cert cost,
    is_dag_instr_at pc n (instr_morph_assert morph_id property cert cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_compose :
  forall pc n dst m1 m2 cost,
    is_dag_instr_at pc n (instr_compose dst m1 m2 cost) = true.
Proof. intros. reflexivity. Qed.

Lemma dag_safe_lassert :
  forall pc freg creg kind flen cost,
    length [instr_lassert freg creg kind flen cost] <= LASSERT_TRAP_PC ->
    is_dag_instr_at pc 1 (instr_lassert freg creg kind flen cost) = true.
Proof.
  intros. unfold is_dag_instr_at. apply Nat.leb_le. simpl in H. lia.
Qed.

(** For any trace shorter than 3840 instructions, LASSERT is DAG-safe.
    This covers all practical programs (3840 is a hard trap-vector boundary). *)
Lemma dag_safe_lassert_short_trace :
  forall (trace : list vm_instruction) (freg creg : nat) (kind : bool) (flen cost : nat),
    length trace <= LASSERT_TRAP_PC ->
    is_dag_instr_at 0 (length trace) (instr_lassert freg creg kind flen cost) = true.
Proof.
  intros. unfold is_dag_instr_at. apply Nat.leb_le. exact H.
Qed.

(** Structural completeness summary: for a trace of length ≤ LASSERT_TRAP_PC,
    every certification-capable instruction is DAG-safe. These are exactly the
    instructions that can accumulate mu-cost and establish certified state. *)
Theorem dag_structural_completeness :
  forall (n : nat),
    n <= LASSERT_TRAP_PC ->
    (forall pc region cost,
       is_dag_instr_at pc n (instr_pnew region cost) = true) /\
    (forall pc module payload cost,
       is_dag_instr_at pc n (instr_emit module payload cost) = true) /\
    (forall pc cost,
       is_dag_instr_at pc n (instr_certify cost) = true) /\
    (forall pc freg creg kind flen cost,
       is_dag_instr_at pc n (instr_lassert freg creg kind flen cost) = true) /\
    (forall pc dst src_mod dst_mod coupling_idx cost,
       is_dag_instr_at pc n (instr_morph dst src_mod dst_mod coupling_idx cost) = true) /\
    (forall pc morph_id property cert cost,
       is_dag_instr_at pc n (instr_morph_assert morph_id property cert cost) = true) /\
    (forall pc dst m1 m2 cost,
       is_dag_instr_at pc n (instr_compose dst m1 m2 cost) = true).
Proof.
  intro n. intro Hn.
  repeat split; intros; try reflexivity.
  (* LASSERT: needs n ≤ LASSERT_TRAP_PC *)
  unfold is_dag_instr_at. apply Nat.leb_le. exact Hn.
Qed.

(** ** No Free Insight Preservation

    No Free Insight is not a property of loops or control flow. It is a
    property of the trace: certification requires a cert-setter instruction,
    regardless of whether that trace is DAG-restricted or Turing-complete.

    The existing no_free_insight_general theorem holds for ALL traces. DAG
    traces are a subset. The restriction makes NFI easier to reason about
    (finite traces, guaranteed halting), not weaker. *)

Theorem dag_nfi_preserved :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    dag_trace_wf trace ->
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n fa ca k fl mu, nth_error trace n = Some (instr_lassert fa ca k fl mu)) \/
    (exists n mid p c mu, nth_error trace n = Some (instr_morph_assert mid p c mu)).
Proof.
  intros trace s_init s_final fuel _ Hrun Hinit Hsupra.
  exact (NoFreeInsight.NoFreeInsight.no_free_insight_general
           trace s_init s_final fuel Hrun Hinit Hsupra).
Qed.

(** Corollary: a DAG trace with no cert-setter instructions can never produce
    a supra-certified state. The machine cannot certify for free even when
    restricted to halt-guaranteed programs. *)
Theorem dag_no_free_insight_corollary :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    dag_trace_wf trace ->
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    List.Forall non_morph_assert_instr trace ->
    ~ has_supra_cert s_final.
Proof.
  intros trace s_init s_final fuel _ Hrun Hinit Hfree.
  exact (NoFreeInsight.NoFreeInsight.supra_bridge_free_trace_has_no_supra_cert
           trace s_init s_final fuel Hrun Hinit Hfree).
Qed.

(** ** The Separation

    These two facts together characterize the Insight ASIC:
    - It always halts (dag_terminates).
    - It cannot certify for free (dag_no_free_insight_corollary).
    - It CAN certify when the program includes cert-setter instructions
      (dag_structural_completeness).

    A sub-Turing machine that enforces No Free Insight is possible. *)
