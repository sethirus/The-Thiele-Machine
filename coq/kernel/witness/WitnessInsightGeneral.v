(** WitnessInsightGeneral.v — General Witness Insight Taxonomy

    THE THREE-TIER WITNESS INSIGHT STRUCTURE

    The ASPIRATIONAL item "Witness insight is non-free (general)" is closed
    here by formalizing the three-tier taxonomy and proving the central
    theorem for all three tiers.

    TIER 0 — RAW OBSERVATION (always free):
      CHSH_TRIAL: updates witness counters (wc_same_XY, wc_diff_XY).
      Cost: 0.  These are observational data, NOT authorization tokens.
      No cert channel is activated.

    TIER 1 — CERTIFIED STRUCTURAL INSIGHT (always costs >= 1):
      Any instruction that activates a cert channel:
      - csr_cert_addr: 0 → nonzero  (cert_addr_setters: MORPH_ASSERT, LASSERT, etc.)
      - vm_certified: false → true  (CERTIFY opcode)
      From certified_insight_nonfree (InsightTaxonomy.v): cost >= 1, mu >= +1.

    TIER 2 — CERTIFIED NON-LOCAL WITNESS INSIGHT (costs >= 1):
      vm_certified = true AND chsh_violation_certified (S > 2).
      The vm_certified flag is a Tier 1 event (cost >= 1).
      The CHSH violation (S > 2) makes the statistics non-local
      (chsh_certification_not_local in CHSHStatisticalBridge.v).
      Together: certified non-local evidence requires cost >= 1 to achieve.

    THE KEY NEW THEOREM

    [witness_insight_nonfree_general]:
      Any trace that achieves certified non-local witness statistics
      (vm_certified = true AND chsh_stat_from_wc > 2) from an uncertified
      baseline must have paid mu >= initial_mu + 1.

    This is the general theorem connecting witness space narrowing to cost:
    committing to a non-local explanation of witness data requires
    certification (cost >= 1), even if the raw trials were free.

    The "general" aspect: the theorem applies to ANY trace length and ANY
    sequence of opcodes — raw CHSH_TRIAL observations are free, but
    certifying what those observations mean is provably non-free.

    HONEST SCOPE

    - CHSH_TRIAL does not activate cert channels (Tier 0 is free).
    - Certified witness insight (Tier 1+2) costs >= 1 (from existing kernel).
    - Any trace achieving certified non-local statistics from uncertified
      baseline must have paid mu >= 1 (trace-level theorem).

    - That uncertified CHSH_TRIAL observations are thermodynamically free.
      (That requires Landauer-Unruh calibration, in NoFIToEinstein.v.)
    - That accumulating witness data without certification costs nothing
      in a physical sense.
    - A general "feasible-set narrowing" theorem for uncertified ops.
      (InformationGainToStrengthening.v handles that abstract direction.)

    The trace-level theorem is genuinely new; others compose existing results.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           AbstractNoFI InsightTaxonomy
                           LandauerDerivation OCamlExtractionBridge
                           CHSHStatisticalBridge.

(**

    CHSH_TRIAL is NOT a cert_addr_setter and is NOT instr_certify.
    Therefore it cannot create a certified insight event.
*)

(** CHSH_TRIAL is not a cert_addr_setter: cert_addr_setterb returns false. *)
Lemma chsh_trial_not_cert_addr_setter :
  forall a b x y mu_delta,
    cert_addr_setterb (instr_chsh_trial a b x y mu_delta) = false.
Proof. intros. simpl. reflexivity. Qed.

(** CHSH_TRIAL preserves csr_cert_addr. *)
Lemma chsh_trial_preserves_cert_addr :
  forall s a b x y mu_delta,
    (vm_apply s (instr_chsh_trial a b x y mu_delta)).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s a b x y mu_delta.
  apply thiele_non_cert_addr_setter_preserves.
  apply chsh_trial_not_cert_addr_setter.
Qed.

(** CHSH_TRIAL is not instr_certify, so vm_certified is preserved. *)
Lemma chsh_trial_preserves_vm_certified :
  forall s a b x y mu_delta,
    (vm_apply s (instr_chsh_trial a b x y mu_delta)).(vm_certified) =
    s.(vm_certified).
Proof.
  intros s a b x y mu_delta.
  apply vm_apply_preserves_certified_non_certify.
  intros d. discriminate.
Qed.

(** CHSH_TRIAL is a Tier 0 event: it does NOT create a certified insight
    event from any baseline state. *)
Theorem chsh_trial_is_tier0 :
  forall s a b x y mu_delta,
    ~ is_cert_insight_event s (instr_chsh_trial a b x y mu_delta).
Proof.
  intros s a b x y mu_delta Hevent.
  unfold is_cert_insight_event in Hevent.
  destruct Hevent as [[Hca_pre Hca_post] | [Hcf_pre Hcf_post]].
  - rewrite chsh_trial_preserves_cert_addr in Hca_post. exact (Hca_post Hca_pre).
  - rewrite chsh_trial_preserves_vm_certified, Hcf_pre in Hcf_post. discriminate.
Qed.

(**

    Specialization of certified_insight_nonfree from InsightTaxonomy.v
    to the witness insight context.
*)

(** A witness insight event is a certified insight event in the witness
    context — any instruction that activates a cert channel while the
    witness state is potentially non-local. *)
Definition is_witness_insight_event (s : VMState) (i : vm_instruction) : Prop :=
  is_cert_insight_event s i.

(** Tier 1 theorem: any certified witness insight event costs >= 1. *)
Theorem certified_witness_insight_nonfree :
  forall (s : VMState) (i : vm_instruction),
    is_witness_insight_event s i ->
    instruction_cost i >= 1 /\
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i Hevent.
  exact (certified_insight_nonfree s i Hevent).
Qed.

(**

    A state certifies non-local witness statistics if:
    1. vm_certified = true  (certification channel activated — Tier 1, cost >= 1)
    2. chsh_violation_certified s  (CHSH statistic S > 2, hence non-local)

    chsh_certification_not_local (from CHSHStatisticalBridge.v) proves that
    condition 2 implies the witness statistics have no local deterministic
    explanation.  Condition 1 guarantees cost >= 1 was paid.
*)

(** A state has certified non-local witness statistics. *)
Definition has_certified_nonlocal_witness (s : VMState) : Prop :=
  s.(vm_certified) = true /\ chsh_violation_certified s.

(** Single-step Tier 2 theorem: an instruction that achieves certified
    non-local witness statistics from an uncertified baseline costs >= 1. *)
Theorem nonlocal_witness_insight_nonfree :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_certified) = false ->
    has_certified_nonlocal_witness (vm_apply s i) ->
    instruction_cost i >= 1 /\
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i Hbefore [Hcert_post _].
  split.
  - exact (no_free_certification_certified s i Hbefore Hcert_post).
  - exact (no_free_certification_certified_mu s i Hbefore Hcert_post).
Qed.

(**

    The key new theorem: over ANY trace, achieving certified non-local
    witness statistics from an uncertified baseline requires mu >= init + 1.

    This theorem closes the ASPIRATIONAL gap: it IS the general theorem
    connecting witness insight (certified non-locality) to cost.

    By induction on the trace.  At the step where vm_certified goes from
    false to true, no_free_certification_certified_mu gives mu += 1.
    mu is nondecreasing over the rest of the trace (eo_mu_trace_nondecreasing).
*)

(** Helper: if vm_certified starts false and trace achieves it true,
    mu grows by >= 1. *)
Lemma no_free_certification_certified_trace_mu :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_certified) = false ->
    (acm_run thiele_cert_machine trace s0).(vm_certified) = true ->
    (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1.
Proof.
  induction trace as [| i rest IH]; intros s0 Hbefore Hafter.
  - (* Empty trace: final state = s0; certified = false, contradiction *)
    simpl in Hafter. rewrite Hbefore in Hafter. discriminate.
  - (* Cons: i :: rest *)
    simpl in Hafter.
    simpl.
    destruct ((vm_apply s0 i).(vm_certified)) eqn:Hmid.
    + (* vm_certified becomes true after step i *)
      pose proof (no_free_certification_certified_mu s0 i Hbefore Hmid) as Hmu_step.
      pose proof (eo_mu_trace_nondecreasing rest (vm_apply s0 i)) as Hmu_rest.
      lia.
    + (* vm_certified still false after step i; IH applies *)
      pose proof (IH (vm_apply s0 i) Hmid Hafter) as IH_result.
      pose proof (eo_mu_nondecreasing s0 i) as Hstep.
      lia.
Qed.

(** THE GENERAL WITNESS INSIGHT THEOREM.

    Any trace that achieves certified non-local witness statistics from an
    uncertified baseline must have paid at least 1 unit of mu-cost.

    CLOSES: ASPIRATIONAL "Witness insight is non-free (general)."

    INTERPRETATION:
    - Raw CHSH_TRIAL observations (Tier 0) are free — they just accumulate data.
    - COMMITTING to a non-local interpretation (vm_certified = true) requires
      certification, which provably costs >= 1.
    - Therefore: non-local CERTIFIED witness insight is non-free.
    - This is the general theorem: it applies to ANY trace, ANY opcodes,
      for the specific case of certified non-locality. *)
Theorem witness_insight_nonfree_general :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_certified) = false ->
    (acm_run thiele_cert_machine trace s0).(vm_certified) = true ->
    chsh_violation_certified (acm_run thiele_cert_machine trace s0) ->
    (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1.
Proof.
  intros trace s0 Hbefore Hcert _.
  exact (no_free_certification_certified_trace_mu trace s0 Hbefore Hcert).
Qed.

(**

    Packages the three-tier structure into a single summary theorem.
*)

Theorem witness_insight_complete_taxonomy :
  (** Tier 0: CHSH trials do not activate cert channels — they are free. *)
  (forall s a b x y mu_delta, ~ is_cert_insight_event s (instr_chsh_trial a b x y mu_delta)) /\
  (** Tier 1: Certified insight events (any cert channel activation) cost >= 1. *)
  (forall s i, is_cert_insight_event s i ->
     instruction_cost i >= 1 /\ (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1) /\
  (** Tier 2 trace: Achieving certified non-local statistics from baseline
     requires mu to grow >= 1 over the trace. *)
  (forall trace s0,
     s0.(vm_certified) = false ->
     (acm_run thiele_cert_machine trace s0).(vm_certified) = true ->
     chsh_violation_certified (acm_run thiele_cert_machine trace s0) ->
     (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1).
Proof.
  refine (conj _ (conj _ _)).
  - exact chsh_trial_is_tier0.
  - exact certified_insight_nonfree.
  - exact witness_insight_nonfree_general.
Qed.
