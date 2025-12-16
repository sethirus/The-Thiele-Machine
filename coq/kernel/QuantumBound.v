From Coq Require Import List Lia Arith.PeanoNat Bool.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import RevelationRequirement.

Import RevelationProof.

(** * Quantum Bound (Kernel-Level)

    This module provides a kernel-level *operational* guarantee:

      If a trace contains no cert-setting instructions (REVEAL/EMIT/LJOIN/LASSERT),
      then executing it cannot set the certification CSR.

    A full distributional CHSH/Tsirelson theorem requires a probabilistic
    measurement semantics (receipts/statistics). That development is carried in
    the ThieleMachine-level Bell files (boxes, CHSH checks), not in the
    deterministic kernel step semantics.
*)

Module QuantumBound.

(** * Quantum-Admissible Traces *)

(** A trace is quantum-admissible if it contains no cert-setting instructions. *)
Fixpoint quantum_admissible (trace : list vm_instruction) : Prop :=
  match trace with
  | [] => True
  | i :: rest =>
      (forall m b c mu, i <> instr_reveal m b c mu) /\
      (forall m p mu, i <> instr_emit m p mu) /\
      (forall c1 c2 mu, i <> instr_ljoin c1 c2 mu) /\
      (forall m f c mu, i <> instr_lassert m f c mu) /\
      quantum_admissible rest
  end.

Lemma quantum_admissible_nil : quantum_admissible [].
Proof. simpl. exact I. Qed.

Lemma quantum_admissible_cons : forall i trace,
  quantum_admissible (i :: trace) <->
  ((forall m b c mu, i <> instr_reveal m b c mu) /\
   (forall m p mu, i <> instr_emit m p mu) /\
   (forall c1 c2 mu, i <> instr_ljoin c1 c2 mu) /\
   (forall m f c mu, i <> instr_lassert m f c mu) /\
   quantum_admissible trace).
Proof. intro i. intro trace. simpl. split; intro H; exact H. Qed.

(** * Structural helper lemmas *)

(** Helper: quantum-admissible traces preserve local structure *)
Lemma quantum_admissible_preserves_structure :
  forall i trace,
    quantum_admissible (i :: trace) ->
    (forall m b c mu, i <> instr_reveal m b c mu) /\
    quantum_admissible trace.
Proof.
  intros i trace H.
  apply quantum_admissible_cons in H.
  destruct H as [Hr [He [Hj [Hl Hrest]]]].
  split; auto.
Qed.

(** * The Quantum Bound Theorem *)

(** This file currently establishes the *operational* (kernel-level) bound:
    traces with no cert-setting instructions cannot set the certification CSR.

    A full *distributional* CHSH/Tsirelson theorem requires a probabilistic
    measurement semantics (induced distribution, receipts/statistics, etc.).
    That development lives in the ThieleMachine-level Bell files rather than
    the deterministic kernel semantics.
*)

(** * The Connection to Revelation *)

(** THEOREM: Quantum-admissible traces cannot produce supra-classical correlations.
    
    This is the KEY theorem connecting revelation to quantum bounds.
    However, it requires:
    1. A semantic model connecting traces to probability distributions
    2. A proof that partition graphs without revelation yield LHV factorization
    3. The convex hull analysis in lhv_chsh_bound
    
    We prove a weaker version using the RevelationRequirement infrastructure.
*)

(** ** Bridge lemma: Connect two formulations of cert-setter existence *)

Lemma uses_revelation_to_existential : forall trace,
  uses_revelation trace ->
  exists n m b c mu, nth_error trace n = Some (instr_reveal m b c mu).
Proof.
  intro trace. induction trace as [|i rest IH]; intro H.
  - (* Empty trace: uses_revelation [] = False *)
    simpl in H. contradiction.
  - (* Non-empty trace *)
    simpl in H. destruct i as
      [ region mu_pnew
      | m_ps left_ps right_ps mu_ps
      | m1_pm m2_pm mu_pm
      | m_la f_la cert_la mu_la
      | c1_lj c2_lj mu_lj
      | m_mdl mu_mdl
      | m_pd ev_pd mu_pd
      | dst_xf src_xf mu_xf
      | payload_py mu_py
      | dst_xl addr_xl mu_xl
      | dst_xa src_xa mu_xa
      | a_xs b_xs mu_xs
      | dst_xr src_xr mu_xr
      | m_em p_em mu_em
      | m_rev bits_rev cert_rev mu_rev
      | p_oh mu_oh
      | mu_halt
      ].
    all: try (apply IH in H; destruct H as [n [m [b [c [mu Hn]]]]];
             exists (S n), m, b, c, mu; simpl; exact Hn).
    (* instr_reveal case: found it at position 0 *)
    exists 0, m_rev, bits_rev, cert_rev, mu_rev. simpl. reflexivity.
Qed.

Lemma cert_setter_forms_equiv : forall trace,
  (uses_revelation trace \/
   (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
   (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
   (exists n m f c mu, nth_error trace n = Some (instr_lassert m f c mu)))
  <->
  (exists n instr, nth_error trace n = Some instr /\
    ((exists m b c mu, instr = instr_reveal m b c mu) \/
     (exists m p mu, instr = instr_emit m p mu) \/
     (exists c1 c2 mu, instr = instr_ljoin c1 c2 mu) \/
     (exists m f c mu, instr = instr_lassert m f c mu))).
Proof.
  intros trace. split; intros H.
  - (* Forward direction *)
    destruct H as [Hrev|[Hemit|[Hljoin|Hlassert]]].
    + (* uses_revelation *)
      apply uses_revelation_to_existential in Hrev.
      destruct Hrev as [n [m [b [c [mu Hn]]]]].
      exists n, (instr_reveal m b c mu). split.
      * exact Hn.
      * left. exists m, b, c, mu. reflexivity.
    + (* emit *)
      destruct Hemit as [n [m [p [mu Hn]]]].
      exists n, (instr_emit m p mu). split.
      * exact Hn.
      * right. left. exists m, p, mu. reflexivity.
    + (* ljoin *)
      destruct Hljoin as [n [c1 [c2 [mu Hn]]]].
      exists n, (instr_ljoin c1 c2 mu). split.
      * exact Hn.
      * right. right. left. exists c1, c2, mu. reflexivity.
    + (* lassert *)
      destruct Hlassert as [n [m [f [c [mu Hn]]]]].
      exists n, (instr_lassert m f c mu). split.
      * exact Hn.
      * right. right. right. exists m, f, c, mu. reflexivity.
  - (* Backward direction *)
    destruct H as [n [instr [Hnth Hforms]]].
    destruct Hforms as [Hrev|[Hemit|[Hljoin|Hlassert]]].
    + (* reveal *)
      left. destruct Hrev as [m [b [c [mu Heq]]]]. subst instr.
      (* Show uses_revelation trace by induction *)
      revert n Hnth. induction trace as [|i rest IHt]; intros n Hn.
      * destruct n; discriminate Hn.
      * destruct n as [|n'].
        -- (* n = 0: first instruction is REVEAL *)
           simpl in Hn. injection Hn as Heq. subst i.
           simpl. exact I.
        -- (* n = S n': REVEAL is somewhere in tail *)
           simpl in Hn. simpl.
           destruct i as
             [ region mu_pnew  | m_ps left_ps right_ps mu_ps | m1_pm m2_pm mu_pm
             | m_la f_la cert_la mu_la | c1_lj c2_lj mu_lj | m_mdl mu_mdl
             | m_pd ev_pd mu_pd | dst_xf src_xf mu_xf | payload_py mu_py
             | dst_xl addr_xl mu_xl | dst_xa src_xa mu_xa | a_xs b_xs mu_xs
             | dst_xr src_xr mu_xr | m_em p_em mu_em | m_rev bits_rev cert_rev mu_rev
             | p_oh mu_oh | mu_halt ].
           ++ (* instr_pnew *) apply (IHt n'). exact Hn.
           ++ (* instr_psplit *) apply (IHt n'). exact Hn.
           ++ (* instr_pmerge *) apply (IHt n'). exact Hn.
           ++ (* instr_lassert *) apply (IHt n'). exact Hn.
           ++ (* instr_ljoin *) apply (IHt n'). exact Hn.
           ++ (* instr_mdlacc *) apply (IHt n'). exact Hn.
           ++ (* instr_pdiscover *) apply (IHt n'). exact Hn.
           ++ (* instr_xfer *) apply (IHt n'). exact Hn.
           ++ (* instr_pyexec *) apply (IHt n'). exact Hn.
           ++ (* instr_xor_load *) apply (IHt n'). exact Hn.
           ++ (* instr_xor_add *) apply (IHt n'). exact Hn.
           ++ (* instr_xor_swap *) apply (IHt n'). exact Hn.
           ++ (* instr_xor_rank *) apply (IHt n'). exact Hn.
           ++ (* instr_emit *) apply (IHt n'). exact Hn.
           ++ (* instr_reveal: trivial True *) exact I.
           ++ (* instr_oracle_halts *) apply (IHt n'). exact Hn.
           ++ (* instr_halt *) apply (IHt n'). exact Hn.
    + (* emit *)
      right. left. destruct Hemit as [m [p [mu Heq]]]. subst instr.
      exists n, m, p, mu. exact Hnth.
    + (* ljoin *)
      right. right. left. destruct Hljoin as [c1 [c2 [mu Heq]]]. subst instr.
      exists n, c1, c2, mu. exact Hnth.
    + (* lassert *)
      right. right. right. destruct Hlassert as [m [f [c [mu Heq]]]]. subst instr.
      exists n, m, f, c, mu. exact Hnth.
Qed.

(** ** Main result: quantum-admissible traces cannot produce supra-certification *)

(** If no cert-setter appears, then no supra-cert can be established *)
Theorem quantum_admissible_implies_no_supra_cert :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    quantum_admissible trace ->
    ~ has_supra_cert s_final.
Proof.
  intros trace s_init s_final fuel Hrun Hinit Hadm Hfinal.
  
  (* By RevelationRequirement theorem: supra_cert → cert-setter exists *)
  assert (Hcert_raw: uses_revelation trace \/
   (exists n m p mu, nth_error trace n = Some (instr_emit m p mu)) \/
   (exists n c1 c2 mu, nth_error trace n = Some (instr_ljoin c1 c2 mu)) \/
   (exists n m f c mu, nth_error trace n = Some (instr_lassert m f c mu))).
  { apply (RevelationProof.cert_setter_necessary_for_supra trace s_init s_final fuel); auto. }
  
  (* Convert to unified form *)
  apply cert_setter_forms_equiv in Hcert_raw.
  destruct Hcert_raw as [n [instr [Hnth Hcert]]].
  
  (* But quantum_admissible says no cert-setter exists - contradiction *)
  destruct Hcert as [[m [b [c [mu Heq]]]] | [[m [p [mu Heq]]] | [[c1 [c2 [mu Heq]]] | [m [f [c [mu Heq]]]]]]];
    subst instr.
  
  - (* REVEAL case *)
    (* Extract that trace at position n is REVEAL *)
    (* Show this contradicts quantum_admissible *)
    clear Hrun Hinit Hfinal s_init s_final fuel.
    revert n m b c mu Hnth.
    induction trace as [|i rest IH]; intros n m_id bits_val cert_val mu_val Hnth.
    + destruct n; discriminate Hnth.
    + destruct n as [|n'].
      * simpl in Hnth. injection Hnth as Heq. subst i.
        apply quantum_admissible_preserves_structure in Hadm.
        destruct Hadm as [Hcontra _].
        exfalso. apply (Hcontra m_id bits_val cert_val mu_val). reflexivity.
      * simpl in Hnth.
        apply quantum_admissible_preserves_structure in Hadm.
        destruct Hadm as [_ Hrest].
        apply (IH Hrest n' m_id bits_val cert_val mu_val Hnth).
  
  - (* EMIT case - similar argument *)
    clear Hrun Hinit Hfinal s_init s_final fuel.
    revert n m p mu Hnth.
    induction trace as [|i rest IH]; intros n m_id payload_val mu_val Hnth.
    + destruct n; discriminate Hnth.
    + destruct n as [|n'].
      * simpl in Hnth. injection Hnth as Heq. subst i.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [Hcontra _]].
        exfalso. apply (Hcontra m_id payload_val mu_val). reflexivity.
      * simpl in Hnth.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [_ [_ [_ Hrest]]]].
        apply (IH Hrest n' m_id payload_val mu_val Hnth).
  
  - (* LJOIN case *)
    clear Hrun Hinit Hfinal s_init s_final fuel.
    revert n c1 c2 mu Hnth.
    induction trace as [|i rest IH]; intros n cert1_val cert2_val mu_val Hnth.
    + destruct n; discriminate Hnth.
    + destruct n as [|n'].
      * simpl in Hnth. injection Hnth as Heq. subst i.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [_ [Hcontra _]]].
        exfalso. apply (Hcontra cert1_val cert2_val mu_val). reflexivity.
      * simpl in Hnth.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [_ [_ [_ Hrest]]]].
        apply (IH Hrest n' cert1_val cert2_val mu_val Hnth).
  
  - (* LASSERT case *)
    clear Hrun Hinit Hfinal s_init s_final fuel.
    revert n m f c mu Hnth.
    induction trace as [|i rest IH]; intros n m_id formula_val cert_val mu_val Hnth.
    + destruct n; discriminate Hnth.
    + destruct n as [|n'].
      * simpl in Hnth. injection Hnth as Heq. subst i.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [_ [_ [Hcontra _]]]].
        exfalso. apply (Hcontra m_id formula_val cert_val mu_val). reflexivity.
      * simpl in Hnth.
        apply quantum_admissible_cons in Hadm.
        destruct Hadm as [_ [_ [_ [_ Hrest]]]].
        apply (IH Hrest n' m_id formula_val cert_val mu_val Hnth).
Qed.
End QuantumBound.

