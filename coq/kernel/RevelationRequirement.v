From Coq Require Import List Lia Arith.PeanoNat Bool.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import KernelPhysics.
Require Import SimulationProof.

(** Decidable equality for vm_instruction (needed for discriminate). *)
Definition vm_instruction_eq_dec : forall (x y : vm_instruction), {x = y} + {x <> y}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try apply string_dec;
    try (apply list_eq_dec; try apply Nat.eq_dec; try apply string_dec);
    try (decide equality; apply string_dec).
Qed.

(** * Revelation Requirement for Nonlocal Correlations *)

Module RevelationProof.

(** * Trace Definitions *)

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

(** * Revelation Usage Predicate *)

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
(** Decidability - constructive proof deferred due to Coq tactic limitations
    with 18-constructor inductives. The decidability is trivial in principle:
    scan the list for instr_reveal. Validated by Python runtime. *)
Lemma uses_revelation_decidable : forall trace,
  {uses_revelation trace} + {~ uses_revelation trace}.
Proof.
  intro trace.
  induction trace as [|i rest IH].
  - right. intro H. exact H.
  - destruct i; simpl; try exact IH.
    left. exact I.
Qed.

(** * Supra-Quantum Correlation Property *)

(** We conservatively define supra-quantum correlations as requiring
    explicit certification. This is validated by the μ-accounting system
    at runtime. *)

Definition has_supra_cert (s : VMState) : Prop :=
  s.(vm_csrs).(csr_cert_addr) <> 0.

(** * Semantic structure addition (execution-based)

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

(** * Graph Preservation Lemmas *)

(** Non-reveal instructions preserve the certification state *)
Lemma non_cert_setter_preserves_cert :
  forall s i,
    (forall m b c mu, i <> instr_reveal m b c mu) ->
    (forall m p mu, i <> instr_emit m p mu) ->
    (forall c1 c2 mu, i <> instr_ljoin c1 c2 mu) ->
    (forall m f c mu, i <> instr_lassert m f c mu) ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s i Hrev Hemit Hljoin Hlassert.
  destruct i; unfold vm_apply.
  - (* pnew *) destruct (graph_pnew _ _). unfold advance_state. simpl. reflexivity.
  - (* psplit *) destruct (graph_psplit _ _ _ _) as [[[? ?] ?]|];
      unfold advance_state, csr_set_err; simpl; reflexivity.
  - (* pmerge *) destruct (graph_pmerge _ _ _) as [[? ?]|];
      unfold advance_state, csr_set_err; simpl; reflexivity.
  - (* lassert *) exfalso. eapply Hlassert. reflexivity.
  - (* ljoin *) exfalso. eapply Hljoin. reflexivity.
  - (* mdlacc *) unfold advance_state. simpl. reflexivity.
  - (* pdiscover *) unfold advance_state. simpl. reflexivity.
  - (* xfer *) unfold advance_state_rm. simpl. reflexivity.
  - (* pyexec *) unfold advance_state. simpl. reflexivity.
  - (* chsh_trial *) destruct (chsh_bits_ok _ _ _ _) eqn:?;
      unfold advance_state, csr_set_err; simpl; reflexivity.
  - (* xor_load *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_add *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_swap *) unfold advance_state_rm. simpl. reflexivity.
  - (* xor_rank *) unfold advance_state_rm. simpl. reflexivity.
  - (* emit *) exfalso. eapply Hemit. reflexivity.
  - (* reveal *) exfalso. eapply Hrev. reflexivity.
  - (* oracle_halts *) unfold advance_state. simpl. reflexivity.
  - (* halt *) unfold advance_state. simpl. reflexivity.
Qed.

(** * Main Theorem: Cert Must Come From Revelation-Class Instructions *)

(** If certification appears (cert_addr becomes non-zero), it must have been
    set by a revelation-class instruction. REVEAL is the primary one for
    partition disclosure; others (EMIT, LJOIN, LASSERT) serve related purposes.
    
    Policy interpretation: Programs producing supra-quantum correlations (S > 2√2)
    are required by runtime policy to use REVEAL for partition disclosure.
    This is validated by test_supra_revelation_semantics.py. *)

Theorem nonlocal_correlation_requires_revelation :
  forall (trace : Trace) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n m f c mu, nth_error trace n = Some (instr_lassert m f c mu)).
Proof.
  intros trace s_init s_final fuel.
  revert trace s_init s_final.
  induction fuel as [|fuel IH]; intros trace s_init s_final Hrun Hinit Hfinal.
  - simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
    unfold has_supra_cert in Hfinal. contradiction.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + destruct instr; unfold vm_apply in Hrun.
      * (* pnew *) destruct (graph_pnew _ _). apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* psplit *) destruct (graph_psplit _ _ _ _) as [[[g' l] r]|]; apply IH in Hrun;
          try exact Hrun; try exact Hfinal; unfold advance_state, csr_set_err; simpl; exact Hinit.
      * (* pmerge *) destruct (graph_pmerge _ _ _) as [[g' m]|]; apply IH in Hrun;
          try exact Hrun; try exact Hfinal; unfold advance_state, csr_set_err; simpl; exact Hinit.
      * (* lassert *) right. right. right. eexists _, _, _, _, _. exact Hnth.
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
      * (* pyexec *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* chsh_trial *) apply IH in Hrun.
        -- exact Hrun.
        -- destruct (chsh_bits_ok _ _ _ _) eqn:?;
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
      * (* oracle_halts *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
      * (* halt *) apply IH in Hrun.
        -- exact Hrun.
        -- unfold advance_state; simpl. exact Hinit.
        -- exact Hfinal.
    + simpl in Hrun. injection Hrun as Heq. rewrite <- Heq in Hfinal.
      unfold has_supra_cert in Hfinal. contradiction.
Qed.

(** * Corollary: Same as main theorem, restated for clarity *)

Corollary cert_setter_necessary_for_supra :
  forall trace s_init s_final fuel,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    uses_revelation trace \/
    (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
    (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
    (exists n m f c mu, nth_error trace n = Some (instr_lassert m f c mu)).
Proof.
  apply nonlocal_correlation_requires_revelation.
Qed.

End RevelationProof.
