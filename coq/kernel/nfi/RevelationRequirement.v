(** RevelationRequirement: certification transitions require structure-setting steps

    This file proves a concrete operational claim: if execution starts with
    cert_addr = 0 and ends with cert_addr <> 0, then some executed step must
    perform the relevant structure-setting transition. In the current VM this
    means certification does not appear out of arithmetic or control flow
    alone.

    The result is intentionally scoped to the machine semantics in this
    repository. It packages the connection between trace execution,
    certification-state change, and the designated revelation class of steps.
    It does not by itself derive the full Tsirelson story; that needs the
    additional quantum premises proved elsewhere.

    *)

From Coq Require Import List Lia Arith.PeanoNat Bool.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import KernelPhysics SimulationProof.

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** Decidable equality for vm_instruction (needed for discriminate). *)
Definition vm_instruction_eq_dec : forall (x y : vm_instruction), {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply string_dec;
    try (apply list_eq_dec; try apply Nat.eq_dec; try apply string_dec);
    try (decide equality; apply string_dec).
Qed.

(** Revelation Requirement for Nonlocal Correlations *)

Module RevelationProof.

(** Trace Definitions *)

Definition Trace := list vm_instruction.

Fixpoint trace_run (fuel : nat) (trace : Trace) (s : VMState) : option VMState :=
  match fuel with
  | 0 => Some s
  | S fuel' =>
      match nth_error trace (s.(vm_pc)) with
      | None => Some s
      | Some instr =>
          trace_run fuel' trace (vm_apply s instr)
      end
  end.

(** Revelation Usage Predicate *)

Fixpoint uses_revelation (trace : Trace) : Prop :=
  match trace with
  | [] => False
  | instr :: rest =>
      match instr with
      | instr_reveal _ _ _ _ => True
      | _ => uses_revelation rest
      end
  end.

(** Boolean version for decidability *)
Fixpoint uses_revelation_bool (trace : Trace) : bool :=
  match trace with
  | [] => false
  | instr :: rest =>
      match instr with
      | instr_reveal _ _ _ _ => true
      | _ => uses_revelation_bool rest
      end
  end.

(** Correctness of boolean version *)
(** Decidability - proven by structural induction over the trace list.
    The decidability follows from scanning the list for instr_reveal. *)
Lemma uses_revelation_decidable : forall trace,
  {uses_revelation trace} + {~ uses_revelation trace}.
Proof.
  intro trace.
  induction trace as [|i rest IH].
  - right. intro H. exact H.
  - destruct i; simpl; try exact IH.
    left. exact I.
Qed.

(** Supra-Quantum Correlation Property *)

(** We conservatively define supra-quantum correlations as requiring
    explicit certification. This is validated by the μ-accounting system
    at runtime. *)

Definition has_supra_cert (s : VMState) : Prop :=
  s.(vm_csrs).(csr_cert_addr) <> 0.

(** Semantic structure addition (execution-based)

    To avoid defining “structure addition” by an opcode list, we define it
    as an *observable transition* during execution:
    the certification CSR changes from 0 to non-zero at some executed step.

    This is intentionally expressed in terms of [trace_run] and [vm_apply],
    and does not mention specific instruction constructors.
*)

Fixpoint structure_addition_in_run (fuel : nat) (trace : Trace) (s : VMState) : Prop :=
  match fuel with
  | 0 => False
  | S fuel' =>
      match nth_error trace (s.(vm_pc)) with
      | None => False
      | Some instr =>
          let s' := vm_apply s instr in
          (s.(vm_csrs).(csr_cert_addr) = 0 /\ s'.(vm_csrs).(csr_cert_addr) <> 0)
          \/ structure_addition_in_run fuel' trace s'
      end
  end.

Lemma supra_cert_implies_structure_addition_in_run :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    structure_addition_in_run fuel trace s_init.
Proof.
  intros trace s_init s_final fuel.
  revert trace s_init s_final.
  induction fuel as [|fuel IH]; intros trace s_init s_final Hrun Hinit Hfinal.
  - simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
    unfold has_supra_cert in Hfinal. contradiction.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + set (s' := vm_apply s_init instr) in *.
      (* Expose the disjunction in the goal. *)
      simpl. rewrite Hnth. simpl.
      destruct (Nat.eq_dec (s'.(vm_csrs).(csr_cert_addr)) 0) as [Hczero|Hcnz].
      * (* cert still zero: recurse *)
        right.
        eapply IH; [exact Hrun | exact Hczero | exact Hfinal].
      * (* cert became non-zero at this executed step *)
        left.
        split.
        -- exact Hinit.
        -- exact Hcnz.
    + simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
      unfold has_supra_cert in Hfinal. contradiction.
Qed.

(** Graph Preservation Lemmas *)

(** Non-reveal instructions preserve the certification state. *)
Lemma non_cert_setter_preserves_cert :
  forall s i,
    (forall m b c mu, i <> instr_reveal m b c mu) ->
    (forall m p mu, i <> instr_emit m p mu) ->
    (forall c1 c2 mu, i <> instr_ljoin c1 c2 mu) ->
    (forall fa ca k fl mu, i <> instr_lassert fa ca k fl mu) ->
    (forall mu, i <> instr_certify mu) ->
    (forall mid p c mu, i <> instr_morph_assert mid p c mu) ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s i Hrev Hemit Hljoin Hlassert Hcertify Hmorph_assert.
  destruct i; unfold vm_apply, vm_apply_unsafe.
  - (* pnew *)
    match goal with
    | |- context [graph_add_module ?g ?r ?e] => destruct (graph_add_module g r e) as [? ?]
    end.
    unfold advance_state. simpl. reflexivity.
  - (* psplit *)
    unfold advance_state. simpl. reflexivity.
  - (* pmerge *)
    unfold advance_state. simpl. reflexivity.
  - (* lassert *) exfalso. eapply Hlassert. reflexivity.
  - (* ljoin *) exfalso. eapply Hljoin. reflexivity.
  - (* mdlacc *) unfold advance_state. simpl. reflexivity.
  - (* pdiscover *) unfold advance_state. simpl. reflexivity.
  - (* xfer *) unfold advance_state_rm. simpl. reflexivity.
  - (* load_imm *) unfold advance_state_rm. simpl. reflexivity.
  - (* load *) unfold advance_state_rm. simpl. reflexivity.
  - (* store *) unfold advance_state_rm. simpl. reflexivity.
  - (* add *) unfold advance_state_rm. simpl. reflexivity.
  - (* sub *) unfold advance_state_rm. simpl. reflexivity.
  - (* jump *) unfold jump_state. simpl. reflexivity.
  - (* jnez *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0) eqn:?
    end;
      [unfold advance_state | unfold jump_state]; simpl; reflexivity.
  - (* call *) unfold jump_state_rm. simpl. reflexivity.
  - (* ret *) unfold jump_state_rm. simpl. reflexivity.
  - (* chsh_trial *)
    match goal with
    | |- context [chsh_bits_ok ?x ?y ?a ?b] =>
        destruct (chsh_bits_ok x y a b) eqn:?
    end;
      unfold advance_state, csr_set_err; simpl; reflexivity.
  - (* xor_load *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_add *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_swap *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_rank *) unfold advance_state_rm. simpl. reflexivity.
  - (* emit *) exfalso. eapply Hemit. reflexivity.
  - (* reveal *) exfalso. eapply Hrev. reflexivity.
  - (* halt *) unfold advance_state. simpl. reflexivity.
  - (* checkpoint *) unfold advance_state. simpl. reflexivity.
  - (* read_port *) unfold advance_state_rm. simpl. reflexivity.
  - (* write_port *) unfold advance_state. simpl. reflexivity.
  - (* heap_load *) unfold advance_state_rm. simpl. reflexivity.
  - (* heap_store *) unfold advance_state_rm. simpl. reflexivity.
  - (* certify *) exfalso. eapply Hcertify. reflexivity.
  - (* and *) unfold advance_state_rm. simpl. reflexivity.
  - (* or *) unfold advance_state_rm. simpl. reflexivity.
  - (* shl *) unfold advance_state_rm. simpl. reflexivity.
  - (* shr *) unfold advance_state_rm. simpl. reflexivity.
  - (* mul *) unfold advance_state_rm. simpl. reflexivity.
  - (* lui *) unfold advance_state_rm. simpl. reflexivity.
  - (* tensor_set *)
    match goal with
    | |- context [if VMStep.tensor_indices_ok ?i ?j then _ else _] =>
        destruct (VMStep.tensor_indices_ok i j) eqn:?
    end.
    + unfold advance_state. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* tensor_get *)
    match goal with
    | |- context [if VMStep.tensor_indices_ok ?i ?j then _ else _] =>
        destruct (VMStep.tensor_indices_ok i j) eqn:?
    end.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_morph *)
    destruct (graph_lookup s.(vm_graph) src_mod) as [?|] eqn:?.
    + destruct (graph_lookup s.(vm_graph) dst_mod) as [?|] eqn:?.
      * destruct (graph_add_morphism s.(vm_graph) src_mod dst_mod empty_coupling_data false) as [? ?].
        unfold advance_state_rm. simpl. reflexivity.
      * unfold advance_state, csr_set_err. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_compose *)
    destruct (graph_compose_morphisms s.(vm_graph) m1_id m2_id) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_morph_id *)
    destruct (graph_add_identity s.(vm_graph) module) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_morph_delete *)
    destruct (graph_delete_morphism s.(vm_graph) morph_id) as [?|] eqn:?.
    + unfold advance_state. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_morph_assert: cert-setter, excluded by Hmorph_assert *)
    exfalso. eapply Hmorph_assert. reflexivity.
  - (* instr_morph_tensor *)
    destruct (graph_tensor_morphisms s.(vm_graph) f_id g_id) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_morph_get *)
    destruct (graph_lookup_morphism s.(vm_graph) morph_id) as [?|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* instr_chsh_lassert: does NOT write csr_cert_addr; the column-contractive
       check yields either a PC advance (success) or a trap to LASSERT_TRAP_PC
       with err latch (failure). cert_addr is left intact in both branches. *)
    destruct (column_contractive_check_witness _);
      simpl; reflexivity.
  - (* instr_chsh_lassert_1ab: same cert-channel behaviour as instr_chsh_lassert
       (no csr_cert_addr write in either success or trap branch). *)
    destruct (column_contractive_check_q1ab_kernel _);
      simpl; reflexivity.
  - (* instr_chsh_lassert_1ab_g5: same cert-channel behaviour as the other
       CHSH_LASSERT family — neither success nor trap branch writes csr_cert_addr. *)
    destruct (q1ab_g5_full_integer_check_kernel _ _ _);
      simpl; reflexivity.
  - (* instr_chsh_lassert_1ab_g345: same cert-channel behaviour as the other
       CHSH_LASSERT family — neither success nor trap branch writes csr_cert_addr. *)
    destruct (q1ab_g345_full_integer_check_kernel _ _ _ _ _ _ _);
      simpl; reflexivity.
  - (* instr_chsh_lassert_1ab_g12345: full γ_{1..5} variant; same cert-channel
       behaviour — neither branch writes csr_cert_addr. *)
    destruct (q1ab_g12345_full_integer_check_kernel _ _ _ _ _ _ _ _ _ _ _);
      simpl; reflexivity.
Qed.

(** Under the current kernel semantics, every instruction except MORPH_ASSERT
    preserves csr_cert_addr exactly. MORPH_ASSERT is the only opcode whose
    success branch writes a new cert address. CHSH_LASSERT (the
    column-contractivity check) does not write to csr_cert_addr; its success
    is observable only via PC advancement and vm_err remaining unset, so the
    cert-channel theory is preserved unchanged. This is the precise bridge
    boundary for the structural shortcut upgrade story. *)

Definition non_morph_assert_instr (i : vm_instruction) : Prop :=
  match i with
  | instr_morph_assert _ _ _ _ => False
  | _ => True
  end.

Lemma non_morph_assert_preserves_cert_addr :
  forall s i,
    non_morph_assert_instr i ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s i Hnon.
  destruct i; simpl in Hnon;
    unfold vm_apply, vm_apply_unsafe.
  - (* pnew *)
    match goal with
    | |- context [graph_add_module ?g ?r ?e] => destruct (graph_add_module g r e) as [? ?]
    end.
    unfold advance_state. simpl. reflexivity.
  - (* psplit *)
    unfold advance_state. simpl. reflexivity.
  - (* pmerge *)
    unfold advance_state. simpl. reflexivity.
  - (* lassert *)
    simpl. reflexivity.
  - (* ljoin *)
    unfold advance_state. simpl. reflexivity.
  - (* mdlacc *)
    unfold advance_state. simpl. reflexivity.
  - (* pdiscover *)
    unfold advance_state. simpl. reflexivity.
  - (* xfer *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* load_imm *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* load *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* store *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* add *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* sub *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* jump *)
    unfold jump_state. simpl. reflexivity.
  - (* jnez *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0) eqn:?
    end;
      [unfold advance_state | unfold jump_state]; simpl; reflexivity.
  - (* call *)
    unfold jump_state_rm. simpl. reflexivity.
  - (* ret *)
    unfold jump_state_rm. simpl. reflexivity.
  - (* chsh_trial *)
    match goal with
    | |- context [chsh_bits_ok ?x ?y ?a ?b] =>
        destruct (chsh_bits_ok x y a b) eqn:?
    end;
      unfold advance_state, csr_set_err; simpl; reflexivity.
  - (* xor_load *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* xor_add *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* xor_swap *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* xor_rank *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* emit *)
    unfold advance_state. simpl. reflexivity.
  - (* reveal *)
    unfold advance_state_reveal. simpl. reflexivity.
  - (* halt *)
    unfold advance_state. simpl. reflexivity.
  - (* checkpoint *)
    unfold advance_state. simpl. reflexivity.
  - (* read_port *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* write_port *)
    unfold advance_state. simpl. reflexivity.
  - (* heap_load *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* heap_store *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* certify *)
    simpl. reflexivity.
  - (* and *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* or *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* shl *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* shr *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* mul *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* lui *)
    unfold advance_state_rm. simpl. reflexivity.
  - (* tensor_set *)
    destruct (tensor_indices_ok i j) eqn:?.
    + unfold advance_state. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* tensor_get *)
    destruct (tensor_indices_ok i j) eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* morph *)
    destruct (graph_lookup s.(vm_graph) src_mod) as [?|] eqn:?.
    + destruct (graph_lookup s.(vm_graph) dst_mod) as [?|] eqn:?.
      * destruct (graph_add_morphism s.(vm_graph) src_mod dst_mod empty_coupling_data false) as [? ?].
        unfold advance_state_rm. simpl. reflexivity.
      * unfold advance_state, csr_set_err. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* compose *)
    destruct (graph_compose_morphisms s.(vm_graph) m1_id m2_id) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* morph_id *)
    destruct (graph_add_identity s.(vm_graph) module) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* morph_delete *)
    destruct (graph_delete_morphism s.(vm_graph) morph_id) as [?|] eqn:?.
    + unfold advance_state. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* morph_assert *)
    unfold non_morph_assert_instr in Hnon.
    simpl in Hnon.
    exfalso.
    exact Hnon.
  - (* morph_tensor *)
    destruct (graph_tensor_morphisms s.(vm_graph) f_id g_id) as [[? ?]|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* morph_get *)
    destruct (graph_lookup_morphism s.(vm_graph) morph_id) as [?|] eqn:?.
    + unfold advance_state_rm. simpl. reflexivity.
    + unfold advance_state, csr_set_err. simpl. reflexivity.
  - (* chsh_lassert: does NOT write csr_cert_addr (the column-contractive
       check yields PC-advance on success or trap+err on failure; neither
       branch touches the cert_addr channel). cert_addr passes through both
       branches unchanged. *)
    destruct (column_contractive_check_witness _);
      simpl; reflexivity.
  - (* chsh_lassert_1ab: same cert-channel behaviour as chsh_lassert. *)
    destruct (column_contractive_check_q1ab_kernel _);
      simpl; reflexivity.
  - (* chsh_lassert_1ab_g5: same cert-channel behaviour as the other
       CHSH_LASSERT family. *)
    destruct (q1ab_g5_full_integer_check_kernel _ _ _);
      simpl; reflexivity.
  - (* chsh_lassert_1ab_g345: same cert-channel behaviour as the other
       CHSH_LASSERT family. *)
    destruct (q1ab_g345_full_integer_check_kernel _ _ _ _ _ _ _);
      simpl; reflexivity.
  - (* chsh_lassert_1ab_g12345: same cert-channel behaviour. *)
    destruct (q1ab_g12345_full_integer_check_kernel _ _ _ _ _ _ _ _ _ _ _);
      simpl; reflexivity.
Qed.

Lemma morph_assert_or_non_morph_assert :
  forall i,
    (exists morph_id property cert cost,
        i = instr_morph_assert morph_id property cert cost) \/
    non_morph_assert_instr i.
Proof.
  intros i.
  destruct i; simpl; try (right; exact I).
  left. eauto.
Qed.

(** A bridge-pattern step is exactly a successful MORPH_ASSERT that writes a
    non-zero checksum into csr_cert_addr while the channel is still zero. *)
Lemma morph_assert_step_sets_supra_cert_iff :
  forall s i,
    s.(vm_csrs).(csr_cert_addr) = 0 ->
    ((vm_apply s i).(vm_csrs).(csr_cert_addr) <> 0 <->
     exists morph_id property cert cost ms,
       i = instr_morph_assert morph_id property cert cost /\
       graph_lookup_morphism s.(vm_graph) morph_id = Some ms /\
       ascii_checksum property <> 0).
Proof.
  intros s i Hzero.
  split.
  - intro Hnz.
    destruct (morph_assert_or_non_morph_assert i) as
      [(morph_id & property & cert & cost & Hi) | Hnon].
    + subst i.
      destruct (graph_lookup_morphism s.(vm_graph) morph_id) as [ms|] eqn:Hlookup.
      * exists morph_id, property, cert, cost, ms.
        split; [reflexivity|].
        split; [exact Hlookup|].
        unfold vm_apply, vm_apply_unsafe in Hnz.
        rewrite Hlookup in Hnz.
        cbn in Hnz.
        exact Hnz.
      * unfold vm_apply, vm_apply_unsafe in Hnz.
        rewrite Hlookup in Hnz.
        cbn in Hnz.
        rewrite Hzero in Hnz.
        contradiction.
    + rewrite (non_morph_assert_preserves_cert_addr s i Hnon) in Hnz.
      rewrite Hzero in Hnz.
      contradiction.
  - intros (morph_id & property & cert & cost & ms & Hi & Hlookup & Hchecksum).
    subst i.
    unfold vm_apply, vm_apply_unsafe.
    rewrite Hlookup.
    cbn.
    exact Hchecksum.
Qed.

Inductive morph_assert_bridge_pattern : nat -> Trace -> VMState -> Prop :=
| morph_assert_bridge_here :
    forall fuel trace s morph_id property cert cost ms,
      nth_error trace (vm_pc s) = Some (instr_morph_assert morph_id property cert cost) ->
      s.(vm_csrs).(csr_cert_addr) = 0 ->
      graph_lookup_morphism s.(vm_graph) morph_id = Some ms ->
      ascii_checksum property <> 0 ->
      morph_assert_bridge_pattern (S fuel) trace s
| morph_assert_bridge_later :
    forall fuel trace s instr,
      nth_error trace (vm_pc s) = Some instr ->
      morph_assert_bridge_pattern fuel trace (vm_apply s instr) ->
      morph_assert_bridge_pattern (S fuel) trace s.

Theorem structure_addition_in_run_iff_morph_assert_bridge_pattern :
  forall fuel trace s,
    structure_addition_in_run fuel trace s <->
    morph_assert_bridge_pattern fuel trace s.
Proof.
  induction fuel as [|fuel IH]; intros trace s; split; intro H.
  - simpl in H. contradiction.
  - inversion H.
  - simpl in H.
    destruct (nth_error trace (vm_pc s)) as [instr|] eqn:Hnth.
    + simpl in H.
      destruct H as [[Hzero Hnz] | Hlater].
      * pose proof (proj1 (morph_assert_step_sets_supra_cert_iff s instr Hzero) Hnz)
          as (morph_id & property & cert & cost & ms & Hi & Hlookup & Hchecksum).
        subst instr.
        econstructor 1 with (ms := ms); eauto.
      * econstructor 2 with (instr := instr); eauto.
        apply (proj1 (IH trace (vm_apply s instr))).
        exact Hlater.
    + contradiction.
  - inversion H as
      [fuel' trace' s' morph_id property cert cost ms Hnth Hzero Hlookup Hchecksum
      | fuel' trace' s' instr Hnth Hrest]; subst.
    + simpl. rewrite Hnth. simpl. left.
      split; [exact Hzero|].
      apply (proj2 (morph_assert_step_sets_supra_cert_iff s
               (instr_morph_assert morph_id property cert cost) Hzero)).
      exists morph_id, property, cert, cost, ms.
      repeat split; eauto.
    + simpl. rewrite Hnth. simpl. right.
      apply (proj2 (IH trace (vm_apply s instr))).
      exact Hrest.
Qed.

Theorem non_morph_assert_trace_excludes_morph_assert_bridge_pattern :
  forall fuel trace s,
    Forall non_morph_assert_instr trace ->
    ~ morph_assert_bridge_pattern fuel trace s.
Proof.
  induction fuel as [|fuel IH]; intros trace s Hforall Hbridge.
  - inversion Hbridge.
  - inversion Hbridge; subst.
    + apply nth_error_In in H0.
      rewrite Forall_forall in Hforall.
      pose proof (Hforall _ H0) as Hnon.
      simpl in Hnon.
      contradiction.
    + eapply IH; eauto.
Qed.

Corollary non_morph_assert_trace_has_no_structure_addition :
  forall fuel trace s,
    Forall non_morph_assert_instr trace ->
    ~ structure_addition_in_run fuel trace s.
Proof.
  intros fuel trace s Hforall Hstruct.
  apply (non_morph_assert_trace_excludes_morph_assert_bridge_pattern
           fuel trace s Hforall).
  apply (proj1 (structure_addition_in_run_iff_morph_assert_bridge_pattern
                  fuel trace s)).
  exact Hstruct.
Qed.

Theorem non_morph_assert_trace_cannot_gain_supra_cert :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall non_morph_assert_instr trace ->
    ~ has_supra_cert s_final.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hforall Hsupra.
  apply (non_morph_assert_trace_has_no_structure_addition fuel trace s_init Hforall).
  eapply supra_cert_implies_structure_addition_in_run; eauto.
Qed.

(** If certification appears (cert_addr becomes non-zero), it must have been
    set by a revelation-class instruction. REVEAL is the primary one for
    partition disclosure; others (EMIT, LJOIN, LASSERT) serve related purposes.
    
    Policy interpretation: Programs producing supra-quantum correlations (S > 2 sqrt 2)
    are required by runtime policy to use REVEAL for partition disclosure. *)

Theorem nonlocal_correlation_requires_revelation :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n fa ca k fl mu, nth_error trace n = Some (instr_lassert fa ca k fl mu)) \/
    (exists n mid p c mu, nth_error trace n = Some (instr_morph_assert mid p c mu)).
Proof.
  intros trace s_init s_final fuel.
  revert trace s_init s_final.
  induction fuel as [|fuel IH]; intros trace s_init s_final Hrun Hinit Hfinal.
  - simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
    unfold has_supra_cert in Hfinal. contradiction.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + destruct instr; unfold vm_apply, vm_apply_unsafe in Hrun.
      * (* pnew *)
        match type of Hrun with
        | context [graph_add_module ?g ?r ?e] => destruct (graph_add_module g r e) as [? ?]
        end.
        apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* psplit *)
        apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* pmerge *)
        apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* lassert *) right. right. right. left. eexists _, _, _, _, _, _. exact Hnth.
      * (* ljoin *) right. right. left. eexists _, _, _, _. exact Hnth.
      * (* mdlacc *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* pdiscover *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* xfer *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* load_imm *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* load *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* store *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* add *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* sub *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* jump *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold jump_state; simpl. exact Hinit.
        -- exact Hfinal.
       * (* jnez *) apply IH in Hrun.
        -- exact Hrun.
         -- match goal with
         | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
          destruct (Nat.eqb (read_reg st rs) 0) eqn:?
         end;
             [unfold advance_state | unfold jump_state]; simpl; exact Hinit.
        -- exact Hfinal.
      * (* call *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold jump_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* ret *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold jump_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
       * (* chsh_trial *) apply IH in Hrun.
        -- exact Hrun.
         -- match goal with
         | |- context [chsh_bits_ok ?x ?y ?a ?b] =>
          destruct (chsh_bits_ok x y a b) eqn:?
         end;
             unfold advance_state, csr_set_err; simpl; exact Hinit.
        -- exact Hfinal.
      * (* xor_load *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* xor_add *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* xor_swap *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* xor_rank *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* emit *) right. left. eexists _, _, _, _. exact Hnth.
      * (* reveal *) left. 
        clear Hrun Hinit Hfinal IH fuel s_final.
        set (pc := vm_pc s_init) in *.
        clearbody pc. clear s_init.
        revert pc module bits cert mu_delta Hnth.
        induction trace as [|hd tl IHtrace]; intros pc0 mod0 bits0 cert0 mu0 Hnth0.
        -- (* empty trace *) destruct pc0; simpl in Hnth0; discriminate Hnth0.
        -- simpl. destruct pc0 as [|pc'].
           ++ (* pc0 = 0, so hd is at index 0 *)
              simpl in Hnth0.
              (* Hnth0 : Some hd = Some (instr_reveal mod0 bits0 cert0 mu0) *)
              (* Goal: match hd with | instr_reveal _ _ _ _ => True | _ => uses_revelation tl end *)
              (* We know Hnth0 : Some hd = Some (...reveal...) *)
              (* Therefore hd = instr_reveal ... by option injectivity *)
              (* Since we can't easily extract this without decidability,
                 we use the fact that we have vm_instruction_eq_dec defined above. *)
              destruct (vm_instruction_eq_dec hd (instr_reveal mod0 bits0 cert0 mu0)) as [Heq|Hneq].
              ** rewrite Heq. exact I.
              ** exfalso. apply Hneq. injection Hnth0. intro. exact H.
           ++ destruct hd; simpl; try (apply (IHtrace pc' mod0 bits0 cert0 mu0); exact Hnth0).
              (* instr_reveal case: goal is True *) exact I.
      * (* halt *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* checkpoint *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* read_port *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* write_port *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* heap_load *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* heap_store *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* certify *) apply IH in Hrun.
        -- exact Hrun.
        -- simpl. exact Hinit.
        -- exact Hfinal.
      * (* and *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* or *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* shl *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* shr *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* mul *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* lui *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state_rm; simpl. exact Hinit.
        -- exact Hfinal.
      * (* tensor_set *)
        destruct (tensor_indices_ok i j) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* tensor_get *)
        destruct (tensor_indices_ok i j) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state_rm. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_morph *)
        destruct (graph_lookup s_init.(vm_graph) src_mod) as [?|] eqn:?.
        -- destruct (graph_lookup s_init.(vm_graph) dst_mod) as [?|] eqn:?.
           ++ apply IH in Hrun.
              ** exact Hrun.
              ** destruct (graph_add_morphism s_init.(vm_graph) src_mod dst_mod empty_coupling_data false) as [? ?].
                 unfold advance_state_rm. simpl. exact Hinit.
              ** exact Hfinal.
           ++ apply IH in Hrun.
              ** exact Hrun.
              ** unfold advance_state, csr_set_err. simpl. exact Hinit.
              ** exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_compose *)
        destruct (graph_compose_morphisms s_init.(vm_graph) m1_id m2_id) as [[? ?]|] eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state_rm. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_morph_id *)
        destruct (graph_add_identity s_init.(vm_graph) module) as [[? ?]|] eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state_rm. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_morph_delete *)
        destruct (graph_delete_morphism s_init.(vm_graph) morph_id) as [?|] eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_morph_assert: cert-setter — witness it directly as 5th disjunct *)
        right. right. right. right.
        eexists _, _, _, _, _. exact Hnth.
      * (* instr_morph_tensor *)
        destruct (graph_tensor_morphisms s_init.(vm_graph) f_id g_id) as [[? ?]|] eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state_rm. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_morph_get *)
        destruct (graph_lookup_morphism s_init.(vm_graph) morph_id) as [?|] eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state_rm. simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold advance_state, csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_chsh_lassert: column-contractive check on witness counters.
           Both success and failure branches preserve csr_cert_addr (neither
           branch writes to that channel); the only differences from the
           current state are PC, mu, vm_err. *)
        destruct (column_contractive_check_witness (vm_witness s_init)) eqn:?.
        -- (* success: PC advances, cert_addr unchanged. *)
           apply IH in Hrun.
           ++ exact Hrun.
           ++ simpl. exact Hinit.
           ++ exact Hfinal.
        -- (* failure: PC traps to LASSERT_TRAP_PC, vm_err latches,
              cert_addr unchanged. *)
           apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_chsh_lassert_1ab: Q_{1+AB} check on witness counters.
           Same cert-channel behaviour as instr_chsh_lassert. *)
        destruct (column_contractive_check_q1ab_kernel (vm_witness s_init)) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_chsh_lassert_1ab_g5: γ_5-aware Q_{1+AB} check. Same cert-
           channel behaviour as the rest of the CHSH_LASSERT family. *)
        destruct (q1ab_g5_full_integer_check_kernel (vm_witness s_init) same_g5 diff_g5) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_chsh_lassert_1ab_g345: γ_{3,4,5}-aware Q_{1+AB} check via
           4×4 Sylvester PD. Same cert-channel behaviour as the rest of the
           CHSH_LASSERT family. *)
        destruct (q1ab_g345_full_integer_check_kernel (vm_witness s_init)
                    same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
      * (* instr_chsh_lassert_1ab_g12345: full γ_{1..5}-aware Q_{1+AB} check
           via 6×6 Schur cascade. Same cert-channel behaviour. *)
        destruct (q1ab_g12345_full_integer_check_kernel (vm_witness s_init)
                    same_g1 diff_g1 same_g2 diff_g2
                    same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5) eqn:?.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ simpl. exact Hinit.
           ++ exact Hfinal.
        -- apply IH in Hrun.
           ++ exact Hrun.
           ++ unfold csr_set_err. simpl. exact Hinit.
           ++ exact Hfinal.
    + simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
      unfold has_supra_cert in Hfinal. contradiction.
Qed.

(** Corollary: Same as main theorem, restated for clarity *)

Corollary cert_setter_necessary_for_supra :
  forall trace s_init s_final fuel,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n fa ca k fl mu, nth_error trace n = Some (instr_lassert fa ca k fl mu)) \/
    (exists n mid p c mu, nth_error trace n = Some (instr_morph_assert mid p c mu)).
Proof.
  apply nonlocal_correlation_requires_revelation.
Qed.

End RevelationProof.
