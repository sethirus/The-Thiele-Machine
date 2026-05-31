(** A2Payoff: the equal-trust substitution-test payoff theorem.

    This file packages the commitment-accounting results into one theorem the
    monograph can cite.

    The theorem says, in one place:

    1. Trusted erasure accounting and trusted A2 accounting differ: erasure can
       certify at zero cost when no erasure occurs; A2 cannot.
    2. For any trusted local-predicate pricing law, the quantitative trace
       floor "cost >= number of certification commitments" holds iff the
       priced predicate contains the cert-flip predicate.
    3. The batch/n-way version holds iff the priced predicate contains A2.
    4. If the law also refuses to overcharge beyond certification commitments,
       then it is exactly unit-priced A2.
    5. In contrapositive form, every non-A2 substitute fails exact
       non-overcharging commitment pricing.
    6. In richer decomposed cost models, the commitment component is exact iff
       the charged predicate is A2; the real VM's [instruction_cost] decomposes
       into background cost plus the [vm_certified] commitment count.

    This is the current answer to the substitution test: substitutes work only
    by containing A2; exact non-overcharging substitutes are A2.
*)

From Kernel Require Import CommitmentVsErasure.
From Kernel Require Import CommitmentPredicateAdequacy.
From Kernel Require Import CommitmentCostDecomposition.

Definition commitment_vs_erasure_payoff : Prop :=
  (exists (TE : TrustedErasureAccountingSystem)
          (trace : list (tea_instr TE))
          (s0 : tea_state TE),
      tea_cert TE s0 = false /\
      tea_cert TE (tea_run TE trace s0) = true /\
      tea_total_cost TE trace = 0 /\
      tea_any_erasure TE trace s0 = false)
  /\
  (forall (CS : UniversalCertificationCost.CertificationSystem)
          (trace : list (UniversalCertificationCost.cs_instr CS))
          (s0 : UniversalCertificationCost.cs_state CS),
      UniversalCertificationCost.cs_cert CS s0 = false ->
      UniversalCertificationCost.cs_cert CS
        (UniversalCertificationCost.cs_run CS trace s0) = true ->
      UniversalCertificationCost.cs_total_cost CS trace >= 1).

Theorem a2_equal_trust_substitution_payoff :
  commitment_vs_erasure_payoff /\
  (forall LPS : LocalPredicatePricedSystem,
      quantitative_certification_floor LPS <->
      local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      batch_certification_floor LPS <->
      local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      (quantitative_certification_floor LPS /\
       no_overcharge_for_commitments LPS)
      <->
      (local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) /\
       exact_unit_pricing LPS)) /\
  (forall LPS : LocalPredicatePricedSystem,
      ~ local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) ->
      ~ (quantitative_certification_floor LPS /\
         no_overcharge_for_commitments LPS)) /\
  (forall DCS : DecomposedCommitmentSystem,
      (forall trace s0,
          dcs_total_cost DCS trace s0 =
          dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0)
      <->
      dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS)) /\
  (forall DCS : DecomposedCommitmentSystem,
      ~ dcs_local_predicate_same DCS (dcs_cert_flip_local DCS) (dcs_charge DCS) ->
      ~ (forall trace s0,
            dcs_total_cost DCS trace s0 =
            dcs_total_base DCS trace s0 + dcs_cert_flip_count DCS trace s0)) /\
  (forall trace s0,
      dcs_total_cost vm_certified_decomposed_system trace s0 =
      dcs_total_base vm_certified_decomposed_system trace s0
      + dcs_cert_flip_count vm_certified_decomposed_system trace s0).
Proof.
  split.
  - exact commitment_cost_not_reducible_to_erasure_cost.
  - split.
    + intro LPS. apply quantitative_floor_iff_a2_predicate_subsumed.
    + split.
      * intro LPS. apply batch_certification_floor_iff_a2_predicate_subsumed.
      * split.
        -- intro LPS. apply exact_commitment_pricing_characterization.
        -- split.
           ++ intro LPS. apply substitution_test_rejects_non_a2_exact_substitute.
           ++ split.
              ** intro DCS. apply dcs_exact_total_cost_formula_iff.
              ** split.
                 --- intro DCS.
                     apply dcs_substitution_test_rejects_non_a2_exact_component.
                 --- apply vm_instruction_cost_exactly_background_plus_cert_commitments.
Qed.

Print Assumptions a2_equal_trust_substitution_payoff.
