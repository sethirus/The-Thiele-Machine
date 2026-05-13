(** UniversalShortcutLifting: from "trace fires supra-cert" to
    [SoundStructuralShortcut] inhabitation, generically.

    [StructuralAdvantageCertifiedShortcut.v] exhibits [factored_n1_shortcut].
    [SimpleMorphShortcut.v] exhibits [simple_morph_shortcut]. Both are
    concrete inhabitants tied to one specific trace each.

    This file lifts the recipe to a generic theorem. Any trace that fires
    the supra-cert channel from a clean initial state, without latching
    [vm_err], yields a [SoundStructuralShortcut] for that trace. The
    construction is uniform: prior = {init, final}, posterior = {final},
    observation function distinguishes states by whether [csr_cert_addr]
    is nonzero, decision tree is the two-leaf branch.

    The hypotheses are intentionally minimal: clean initial state, no
    error at the end, the supra-cert channel actually fired, and at
    least one cert-setter instruction executed in the trace. The
    last condition is a structural reflection of "the supra-cert
    channel could only have fired via a successful cert-setter" and is
    needed to discharge the decision-tree depth condition.

    What this closes: the §20 open piece called the "open translation
    theorem" asks whether every informal structural shortcut packages
    as a [SoundStructuralShortcut]. This file proves the lifting for
    the cert-setter family of informal shortcuts: any successful trace
    that lifts a state from clean to supra-certified, with no error,
    is in that class. *)

From Coq Require Import List Arith.PeanoNat Lia Bool String.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import SimulationProof.
From Kernel Require Import NoFreeInsight InformationGainToStrengthening MuShannonBridge.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import StructuralAdvantageObservedShortcut.

Import RevelationProof.

(** Running the VM on an empty trace returns the state unchanged. This
    lets us derive [trace <> []] from the assumption that the trace
    fired the supra-cert channel from a clean initial state. *)
Lemma run_vm_nil_id :
  forall (fuel : nat) (s : VMState), run_vm fuel [] s = s.
Proof.
  intros fuel s.
  destruct fuel as [| fuel']; simpl.
  - reflexivity.
  - destruct (vm_pc s); reflexivity.
Qed.

(** Generic cert-addr observation function: a state's observation is the
    trace iff its cert channel has been activated, else the empty list.
    This is the canonical observation function that makes
    "uncertified" and "supra-certified" distinguishable. *)
Definition cert_addr_obs_fn (trace : list vm_instruction)
    (s : VMState) : list vm_instruction :=
  match s.(vm_csrs).(csr_cert_addr) with
  | 0 => []
  | _ => trace
  end.

(** Generic constant representative function. The
    [PosteriorRepresentativeReduction] predicate uses
    [observation_equiv] via this representative; a constant function
    makes every prior state equivalent to every posterior state under
    it, which is the trivial-but-sufficient witness for the
    existential. The actual narrowing content lives in the
    observation function above. *)
Definition trivial_repr_obs_fn (_ : VMState) : list vm_instruction :=
  [instr_halt 0].

(** The universal lifting theorem.

    Five hypotheses, every one a directly checkable property of the
    trace and its initial state:
    1. [s_init] is clean (no cert addr set yet).
    2. The trace's final state has supra-cert activated.
    3. The trace's final state has no error.
    4. The trace executed at least one cert-setter instruction.

    Conclusion: a closed [SoundStructuralShortcut] for this trace
    exists. The construction is uniform across all traces satisfying
    the hypotheses. *)
Theorem any_supra_cert_run_yields_shortcut :
  forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    has_supra_cert (run_vm fuel trace s_init) ->
    (run_vm fuel trace s_init).(vm_err) = false ->
    MuShannonBridge.cert_setter_executions fuel trace s_init >= 1 ->
    SoundStructuralShortcut fuel trace s_init.
Proof.
  intros fuel trace s_init Hclean Hsupra Hnoerr Hcert_count.
  set (final := run_vm fuel trace s_init) in *.
  (* s_init <> final, derived from Hclean and Hsupra. *)
  assert (Hneq : s_init <> final).
  { intro Heq.
    unfold has_supra_cert in Hsupra.
    rewrite <- Heq in Hsupra.
    rewrite Hclean in Hsupra.
    apply Hsupra. reflexivity. }
  (* trace <> [], derived from the fact that an empty trace would leave
     s_init unchanged, contradicting has_supra_cert from a clean start. *)
  assert (Htnz : trace <> []).
  { intro Htnull. subst trace.
    unfold final in Hsupra.
    rewrite run_vm_nil_id in Hsupra.
    unfold has_supra_cert in Hsupra.
    rewrite Hclean in Hsupra.
    apply Hsupra. reflexivity. }
  apply sound_shortcut_from_components with
    (decoder := fun receipts => receipts)
    (obs_fn := cert_addr_obs_fn trace)
    (repr_obs_fn := trivial_repr_obs_fn)
    (obs_eqb := receipt_list_eqb)
    (omega_prior := [s_init; final])
    (omega_posterior := [final])
    (tree := MuShannonBridge.dt_branch MuShannonBridge.dt_leaf MuShannonBridge.dt_leaf).
  - (* H1: obs_eqb_spec *)
    exact receipt_list_eqb_spec.
  - (* H2: is_strict_subset [final] [s_init; final] *)
    split.
    + intros s Hin. simpl in Hin. destruct Hin as [<- | []]. simpl. auto.
    + exists s_init. split.
      * simpl. auto.
      * simpl. intro Hin.
        destruct Hin as [Heq | []]. symmetry in Heq. apply Hneq. exact Heq.
  - (* H3: distinguishing_witness *)
    exists s_init. split.
    + simpl. auto.
    + split.
      * simpl. intro Hin.
        destruct Hin as [Heq | []]. symmetry in Heq. apply Hneq. exact Heq.
      * intros s' Hin'. simpl in Hin'.
        destruct Hin' as [<- | []].
        unfold cert_addr_obs_fn.
        rewrite Hclean.
        unfold has_supra_cert in Hsupra.
        destruct (final.(vm_csrs).(csr_cert_addr)) eqn:E.
        ** exfalso. apply Hsupra. reflexivity.
        ** intro Heq. apply Htnz. symmetry. exact Heq.
  - (* H4: s_init.(vm_csrs).(csr_cert_addr) = 0 *)
    exact Hclean.
  - (* H5: Certified ... *)
    unfold NoFreeInsight.Certified.
    unfold NoFreeInsight.CertifiedWithSupra.
    split.
    + (* CertifiedObs *)
      unfold NoFreeInsight.CertifiedObs.
      split.
      * exact Hnoerr.
      * unfold InformationGainToStrengthening.omega_predicate.
        eapply (InformationGainToStrengthening.existsb_In_true
                  receipt_list_eqb receipt_list_eqb_spec).
        ** simpl. auto.
        ** unfold cert_addr_obs_fn.
           fold final.
           unfold has_supra_cert in Hsupra.
           destruct (final.(vm_csrs).(csr_cert_addr)) eqn:E.
           *** exfalso. apply Hsupra. reflexivity.
           *** reflexivity.
    + fold final. exact Hsupra.
  - (* H6: decision_tree_realized_by_trace *)
    unfold MuShannonBridge.decision_tree_realized_by_trace.
    simpl. (* depth = 1 + max 0 0 = 1 *)
    exact Hcert_count.
  - (* H7: feasible_size [final] > 0 *)
    simpl. lia.
  - (* H8: PosteriorRepresentativeReduction *)
    unfold MuShannonBridge.PosteriorRepresentativeReduction.
    exists (fun _ => [s_init; final]).
    split.
    + intros s_prior Hin_prior.
      exists final. split.
      * simpl. auto.
      * split.
        ** exact Hin_prior.
        ** unfold MuShannonBridge.observation_equiv,
                  trivial_repr_obs_fn.
           reflexivity.
    + split.
      * simpl. lia.
      * intros s_post Hin_post.
        simpl in Hin_post.
        destruct Hin_post as [<- | []].
        simpl. lia.
Qed.

(** As a downstream sanity result, the lifted shortcut also lands in
    the abstract representation theorem. The conclusion exhibits a
    strictly stronger posterior predicate, a structure-addition
    event, and the [log2_up] narrowing bound on $\mu$, for any trace
    satisfying the lifting hypotheses. *)
Theorem any_supra_cert_run_lands_in_representation :
  forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState)
         (Hclean : s_init.(vm_csrs).(csr_cert_addr) = 0)
         (Hsupra : has_supra_cert (run_vm fuel trace s_init))
         (Hnoerr : (run_vm fuel trace s_init).(vm_err) = false)
         (Hcert_count : MuShannonBridge.cert_setter_executions fuel trace s_init >= 1),
    let shortcut := any_supra_cert_run_yields_shortcut
                      fuel trace s_init Hclean Hsupra Hnoerr Hcert_count in
    let P_prior :=
      InformationGainToStrengthening.omega_predicate
        (shortcut_obs_eqb _ _ _ shortcut)
        (shortcut_omega_prior _ _ _ shortcut)
        (shortcut_obs_fn _ _ _ shortcut) in
    let P_posterior :=
      InformationGainToStrengthening.omega_predicate
        (shortcut_obs_eqb _ _ _ shortcut)
        (shortcut_omega_posterior _ _ _ shortcut)
        (shortcut_obs_fn _ _ _ shortcut) in
    NoFreeInsight.strictly_stronger P_posterior P_prior /\
    NoFreeInsight.has_structure_addition fuel trace s_init /\
    Nat.log2_up
      (MuShannonBridge.feasible_size
        (shortcut_omega_prior _ _ _ shortcut)) -
    Nat.log2_up
      (MuShannonBridge.feasible_size
        (shortcut_omega_posterior _ _ _ shortcut)) <=
      (run_vm fuel trace s_init).(vm_mu) - s_init.(vm_mu).
Proof.
  intros fuel trace s_init Hclean Hsupra Hnoerr Hcert_count.
  apply (every_sound_structural_shortcut_lands_here fuel trace s_init).
Qed.
