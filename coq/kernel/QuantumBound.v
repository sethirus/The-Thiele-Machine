(** =========================================================================
    QuantumBound: Quantum-admissible traces preserve zero cert_addr
    =========================================================================

    WHY THIS FILE EXISTS:
    The Thiele Machine distinguishes classical (mu=0) from quantum (mu>0)
    regimes. This file proves the foundational boundary theorem:
    quantum-admissible traces -- those that avoid cert-setting instructions
    (REVEAL, EMIT, LJOIN, LASSERT, CERTIFY) -- cannot achieve
    supra-certification (csr_cert_addr <> 0).

    THE KEY THEOREM:
    quantum_admissible_implies_no_supra_cert: for any trace that is
    quantum_admissible, if the initial cert_addr is 0 then the final
    cert_addr remains 0 regardless of fuel. The proof proceeds by
    showing every non-cert-setter instruction preserves cert_addr
    (vm_apply_preserves_cert_addr), then applying induction on fuel.

    SUPPORTING LEMMAS (all proven):
    - csr_set_err_preserves_cert_addr
    - csr_set_status_preserves_cert_addr
    - advance_state_cert_addr / advance_state_rm_cert_addr
    - vm_apply_preserves_cert_addr
    - quantum_admissible_all_not_cert_setters

    FALSIFICATION:
    Find a quantum_admissible trace (no REVEAL/EMIT/LJOIN/LASSERT/CERTIFY)
    that sets csr_cert_addr to a non-zero value. This would directly
    contradict quantum_admissible_implies_no_supra_cert.
    ========================================================================= *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** All theorems in this file are fully proved (zero Admitted).
    See quantum_admissible_implies_no_supra_cert for the main result. *)

(** =========================================================================
    CERTIFICATION INTERFACE DEFINITIONS
    =========================================================================

    These definitions provide the interface that Certification.v requires.
    They bridge the quantum admissibility predicates to the main
    certification machinery.

    ========================================================================= *)

From Coq Require Import List Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import RevelationRequirement SimulationProof.

Import RevelationProof.

(** A trace is "quantum admissible" if it contains no cert-setting instructions.

    Cert-setting instructions are those that modify the certification address:
    - REVEAL: sets cert_addr to non-zero value
    - EMIT: sets cert_addr to non-zero value
    - LJOIN: sets cert_addr to non-zero value
    - LASSERT: sets cert_addr to non-zero value

    This predicate defines the "quantum boundary" - traces that stay within
    quantum correlations (CHSH ≤ 2√2) don't need certification operations. *)

Definition quantum_admissible (trace : list vm_instruction) : Prop :=
  forall instr, In instr trace ->
    match instr with
    | instr_reveal _ _ _ _ => False
    | instr_emit _ _ _ => False
    | instr_ljoin _ _ _ => False
    | instr_lassert _ _ _ _ _ => False
    | instr_certify _ => False
    | instr_morph_assert _ _ _ _ => False
    | instr_and _ _ _ _ => True
    | instr_or _ _ _ _ => True
    | instr_shl _ _ _ _ => True
    | instr_shr _ _ _ _ => True
    | instr_mul _ _ _ _ => True
    | instr_lui _ _ _ => True
    | _ => True
    end.

(** ** Certification Address Tracking *)

(** CSR helper for cert_addr *)
Definition has_supra_cert (s : VMState) : Prop :=
  s.(vm_csrs).(csr_cert_addr) <> 0%nat.

(** ** Helper Lemmas for Certification Preservation *)

(** A single instruction is NOT a cert-setter *)
Definition is_not_cert_setter (instr : vm_instruction) : Prop :=
  match instr with
  | instr_reveal _ _ _ _ => False
  | instr_emit _ _ _ => False
  | instr_ljoin _ _ _ => False
  | instr_lassert _ _ _ _ _ => False
  | instr_certify _ => False
  | instr_morph_assert _ _ _ _ => False
  | instr_and _ _ _ _ => True
  | instr_or _ _ _ _ => True
  | instr_shl _ _ _ _ => True
  | instr_shr _ _ _ _ => True
  | instr_mul _ _ _ _ => True
  | instr_lui _ _ _ => True
  | _ => True
  end.

(** csr_set_err preserves cert_addr *)
Lemma csr_set_err_preserves_cert_addr : forall csrs err,
  (csr_set_err csrs err).(csr_cert_addr) = csrs.(csr_cert_addr).
Proof.
  intros csrs err. unfold csr_set_err. simpl. reflexivity.
Qed.

(** csr_set_status preserves cert_addr *)
Lemma csr_set_status_preserves_cert_addr : forall csrs status,
  (csr_set_status csrs status).(csr_cert_addr) = csrs.(csr_cert_addr).
Proof.
  intros csrs status. unfold csr_set_status. simpl. reflexivity.
Qed.

(** advance_state with unchanged csrs preserves cert_addr *)
Lemma advance_state_cert_addr : forall s instr graph csrs err,
  (advance_state s instr graph csrs err).(vm_csrs).(csr_cert_addr) = 
  csrs.(csr_cert_addr).
Proof.
  intros. unfold advance_state. simpl. reflexivity.
Qed.

(** advance_state_rm with unchanged csrs preserves cert_addr *)
Lemma advance_state_rm_cert_addr : forall s instr graph csrs regs mem err,
  (advance_state_rm s instr graph csrs regs mem err).(vm_csrs).(csr_cert_addr) = 
  csrs.(csr_cert_addr).
Proof.
  intros. unfold advance_state_rm. simpl. reflexivity.
Qed.

(** If an instruction is not a cert-setter, vm_apply preserves cert_addr *)
Lemma vm_apply_preserves_cert_addr : forall s instr,
  is_not_cert_setter instr ->
  (vm_apply s instr).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s instr Hnot.
  destruct instr; simpl in *; try contradiction;
    (* Instructions that use advance_state with s.(vm_csrs) or error variants *)
    repeat match goal with
           | |- context[match ?x with _ => _ end] => destruct x; simpl
           | |- (advance_state _ _ _ ?csrs _).(vm_csrs).(csr_cert_addr) = _ =>
               rewrite advance_state_cert_addr
           | |- (advance_state_rm _ _ _ ?csrs _ _ _).(vm_csrs).(csr_cert_addr) = _ =>
               rewrite advance_state_rm_cert_addr
           end;
    (* Now we have csrs either s.(vm_csrs) or csr_set_err/csr_set_status *)
    try reflexivity;
    try (rewrite csr_set_err_preserves_cert_addr; reflexivity).
Qed.

(** quantum_admissible means all instructions are not cert-setters *)
Lemma quantum_admissible_all_not_cert_setters : forall trace instr,
  quantum_admissible trace ->
  In instr trace ->
  is_not_cert_setter instr.
Proof.
  intros trace instr Hqa Hin.
  unfold quantum_admissible in Hqa.
  specialize (Hqa instr Hin).
  destruct instr; simpl in *; auto.
Qed.

(** ** Main Theorem: Quantum admissible traces preserve cert_addr = 0 *)

Lemma quantum_admissible_implies_no_supra_cert :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    quantum_admissible trace ->
    trace_run fuel trace s_init = Some s_final ->
    ~ has_supra_cert s_final.
Proof.
  intros trace s_init s_final fuel Hinit Hqa Hrun.
  unfold has_supra_cert.
  (* Prove by induction on fuel that cert_addr is preserved *)
  revert s_init s_final Hinit Hrun.
  induction fuel as [|fuel' IH]; intros s_init s_final Hinit Hrun.
  - (* fuel = 0: s_final = s_init *)
    simpl in Hrun. inversion Hrun. subst. lia.
  - (* fuel = S fuel' *)
    simpl in Hrun.
    destruct (nth_error trace (vm_pc s_init)) as [instr|] eqn:Hnth.
    + (* There is an instruction *)
      (* The instruction is in the trace, so it's not a cert-setter *)
      assert (Hin: In instr trace).
      { apply nth_error_In with (vm_pc s_init). exact Hnth. }
      assert (Hnot: is_not_cert_setter instr).
      { apply quantum_admissible_all_not_cert_setters with trace; auto. }
      (* vm_apply preserves cert_addr *)
      assert (Hpres: (vm_apply s_init instr).(vm_csrs).(csr_cert_addr) = 
                     s_init.(vm_csrs).(csr_cert_addr)).
      { apply vm_apply_preserves_cert_addr. exact Hnot. }
      (* Apply IH *)
      apply IH with (vm_apply s_init instr).
      * rewrite Hpres. exact Hinit.
      * exact Hrun.
    + (* No instruction at PC: returns s_init unchanged *)
      inversion Hrun. subst. lia.
Qed.

(** =========================================================================
    END CERTIFICATION INTERFACE DEFINITIONS
    ========================================================================= *)
