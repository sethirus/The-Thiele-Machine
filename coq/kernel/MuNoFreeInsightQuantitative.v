From Coq Require Import List Lia Arith.PeanoNat Bool.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import MuLedgerConservation.
Require Import RevelationRequirement.

Module MuNoFreeInsightQuantitative.

Import VMStep.VMStep.
Import RevelationProof.

(** * Phase I: Quantitative μ lower bound for supra-certification

    The kernel already proves the structural statement:
      supra-certification (csr_cert_addr ≠ 0) cannot happen “for free”.

    This file adds a quantitative strengthening *inside the deterministic kernel*:
      If supra-certification happens, then there exists a cert-setting step along
      the execution, and the final μ is at least the initial μ plus that step’s
      declared cost.
*)

Definition is_cert_setterb (i : vm_instruction) : bool :=
  match i with
  | instr_reveal _ _ _ _ => true
  | instr_emit _ _ _ => true
  | instr_ljoin _ _ _ => true
  | instr_lassert _ _ _ _ => true
  | _ => false
  end.

Definition is_cert_setter (i : vm_instruction) : Prop := is_cert_setterb i = true.

(** [vm_exec_mu_monotone]: formal specification. *)
Lemma vm_exec_mu_monotone :
  forall fuel trace s0 sf,
    vm_exec fuel trace s0 sf ->
    s0.(vm_mu) <= sf.(vm_mu).
Proof.
  intros fuel trace s0 sf Hexec.
  induction Hexec.
  - lia.
  - (* s -> s' is one step, then s' -> s'' by IH *)
    eapply Nat.le_trans with (m := s'.(vm_mu)).
    + rewrite (vm_step_mu _ _ _ H0). lia.
    + exact IHHexec.
Qed.

(** ------------------------------------------------------------------------- *)
(** Trace-run version (total functional semantics)

    The certification pipeline in the kernel layer is phrased in terms of
    [RevelationProof.trace_run]. To avoid mismatches between relations and
    functions (and to handle early-stop when [nth_error] returns [None]), we
    also provide the quantitative bound directly over [trace_run].
*)

Lemma trace_run_mu_monotone :
  forall fuel trace s0 s1,
    trace_run fuel trace s0 = Some s1 ->
    s0.(vm_mu) <= s1.(vm_mu).
Proof.
  induction fuel as [|fuel IH]; intros trace s0 s1 Hrun.
  - simpl in Hrun. inversion Hrun; subst. lia.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s0)) as [instr|] eqn:Hnth.
    + eapply Nat.le_trans with (m := (vm_apply s0 instr).(vm_mu)).
      * rewrite (vm_apply_mu s0 instr). lia.
      * eapply IH. exact Hrun.
    + inversion Hrun; subst. lia.
Qed.

(** [cert_preserved_if_not_cert_setterb]: formal specification. *)
Lemma cert_preserved_if_not_cert_setterb :
  forall s instr,
    is_cert_setterb instr = false ->
    (vm_apply s instr).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s instr Hnot.
  apply (non_cert_setter_preserves_cert s instr).
  all: destruct instr; simpl in Hnot; try discriminate; intros; discriminate.
Qed.

(** [supra_cert_implies_mu_lower_bound_trace_run]: formal specification. *)
Theorem supra_cert_implies_mu_lower_bound_trace_run :
  forall fuel trace s_init s_final,
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    has_supra_cert s_final ->
    exists instr,
      is_cert_setter instr /\
      s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr.
Proof.
  induction fuel as [|fuel IH]; intros trace s_init s_final Hrun Hinit Hsupra.
  - simpl in Hrun. inversion Hrun; subst.
    unfold has_supra_cert in Hsupra. rewrite Hinit in Hsupra. contradiction.
  - simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + destruct (is_cert_setterb instr) eqn:Hsetterb.
      * exists instr.
        split.
        -- unfold is_cert_setter. exact Hsetterb.
        -- (* μ increases by at least this step's cost, then stays monotone *)
           pose proof (trace_run_mu_monotone fuel trace (vm_apply s_init instr) s_final Hrun) as Hmu_tail.
           rewrite (vm_apply_mu s_init instr) in Hmu_tail.
           lia.
      * (* not a cert-setter: cert addr preserved, continue *)
        assert (Hinit' : (vm_apply s_init instr).(vm_csrs).(csr_cert_addr) = 0%nat).
        { rewrite (cert_preserved_if_not_cert_setterb s_init instr Hsetterb). exact Hinit. }
        specialize (IH trace (vm_apply s_init instr) s_final Hrun Hinit' Hsupra).
        destruct IH as [instr' [Hsetter Hmu]].
        exists instr'.
        split; [exact Hsetter|].
        (* prefix μ monotonicity from s_init to (vm_apply s_init instr) *)
        assert (Hmu_prefix : s_init.(vm_mu) <= (vm_apply s_init instr).(vm_mu)).
        { rewrite (vm_apply_mu s_init instr). lia. }
        lia.
    + inversion Hrun; subst.
      unfold has_supra_cert in Hsupra. rewrite Hinit in Hsupra. contradiction.
Qed.

(** [step_preserves_cert_if_not_cert_setter]: formal specification. *)
Lemma step_preserves_cert_if_not_cert_setter :
  forall s instr s',
    vm_step s instr s' ->
    is_cert_setterb instr = false ->
    s'.(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s instr s' Hstep Hnot.
  rewrite <- (vm_step_vm_apply _ _ _ Hstep).
  apply (non_cert_setter_preserves_cert s instr).
  all: destruct instr; simpl in Hnot; try discriminate; intros; discriminate.
Qed.

(** [supra_cert_has_cert_setter_step]: formal specification. *)
Theorem supra_cert_has_cert_setter_step :
  forall fuel trace s_init s_final,
    vm_exec fuel trace s_init s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    exists fuel1 fuel2 s_mid instr s_mid',
      fuel = fuel1 + S fuel2 /\
      vm_exec fuel1 trace s_init s_mid /\
      nth_error trace s_mid.(vm_pc) = Some instr /\
      vm_step s_mid instr s_mid' /\
      is_cert_setter instr /\
      vm_exec fuel2 trace s_mid' s_final.
Proof.
  intros fuel trace s_init s_final Hexec.
  revert Hexec.
  (* Stronger induction: carry the “cert is still 0 so far” hypothesis. *)
  intros Hexec Hinit Hsupra.
  induction Hexec.
  - unfold has_supra_cert in Hsupra. rewrite Hinit in Hsupra. contradiction.
  - destruct (is_cert_setterb instr) eqn:Hsetterb.
    + (* cert-setter at this step *)
      exists 0%nat, fuel, s, instr, s'.
      split.
      * simpl. reflexivity.
      * split.
        -- exact (vm_exec_zero trace s).
        -- split.
          ++ exact H.
          ++ split.
            ** exact H0.
            ** split.
              --- unfold is_cert_setter. exact Hsetterb.
              --- exact Hexec.
    + (* not a cert-setter: cert_addr preserved, recurse *)
      assert (Hcert_pres : s'.(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr)).
      { eapply step_preserves_cert_if_not_cert_setter; eauto. }
      assert (Hinit' : s'.(vm_csrs).(csr_cert_addr) = 0).
      { rewrite Hcert_pres. exact Hinit. }
      specialize (IHHexec Hinit' Hsupra).
      destruct IHHexec as [fuel1 [fuel2 [s_mid [instr_mid [s_mid' [Hfuel [Hpre [Hnth [Hstep [Hsetter Hpost]]]]]]]]]].
      exists (S fuel1), fuel2, s_mid, instr_mid, s_mid'.
      split.
      * lia.
      * split.
        -- eapply vm_exec_step; eauto.
        -- split.
          ++ exact Hnth.
          ++ split.
            ** exact Hstep.
            ** split.
              --- exact Hsetter.
              --- exact Hpost.
Qed.

(** [supra_cert_implies_mu_lower_bound]: formal specification. *)
Corollary supra_cert_implies_mu_lower_bound :
  forall fuel trace s_init s_final,
    vm_exec fuel trace s_init s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert s_final ->
    exists instr,
      is_cert_setter instr /\
      s_final.(vm_mu) >= s_init.(vm_mu) + instruction_cost instr.
Proof.
  intros fuel trace s_init s_final Hexec Hinit Hsupra.
  pose proof (supra_cert_has_cert_setter_step fuel trace s_init s_final Hexec Hinit Hsupra)
    as [fuel1 [fuel2 [s_mid [instr [s_mid' [Hfuel [Hpre [Hnth [Hstep [Hsetter Hpost]]]]]]]]]].
  exists instr.
  split.
  - exact Hsetter.
  - pose proof (vm_exec_mu_monotone _ _ _ _ Hpre) as Hmu_pre.
    pose proof (vm_step_mu _ _ _ Hstep) as Hmu_step.
    pose proof (vm_exec_mu_monotone _ _ _ _ Hpost) as Hmu_post.
    rewrite Hmu_step in Hmu_post.
    lia.
Qed.

End MuNoFreeInsightQuantitative.
