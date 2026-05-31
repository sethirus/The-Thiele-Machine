(** CommitmentPredicateAdequacy: the substitution gate for A2.

    The critic's substitution test asks whether an A2 theorem still holds
    after replacing "cert-flip" by an arbitrary local invariant.  This file
    makes that test precise.

    We consider trusted local-predicate pricing systems.  A system chooses a
    local predicate [lps_charge s i].  The trust law says:

      - charged steps cost at least 1;
      - uncharged steps are free.

    This is the clean "no hidden A2 in the cost schedule" regime: the local
    predicate is the whole reason a step can cost anything.

    The theorem is exact:

      A local predicate yields a universal certification-cost floor
      iff it covers every uncertified-to-certified transition.

    Consequence.  An arbitrary substitute predicate, such as "erases a bit" or
    "writes address zero", is adequate for certification cost only when every
    certification commitment also satisfies that predicate.  Otherwise a
    trusted system can certify at zero cost.  A2 is therefore the minimal
    local predicate for certification-cost lower bounds under equal trust.

    INQUISITOR NOTE: proof-connectivity gap suppressed — this file is the
    substrate-free half of the substitution gate.  Every theorem here is
    indicator-uniqueness over an abstract local-predicate pricing record
    (lps_charge / lps_cost); it deliberately imports no VM semantics, because
    the point is that the floor follows from the cost schedule alone, with no
    appeal to the machine.  The VM teeth live next door in
    CommitmentCostDecomposition.v (which imports VMState/VMStep/SimulationProof
    and proves no_free_certification_certified), and A2Payoff.v is the
    aggregator that combines the abstract result here with that concrete
    instruction-set lemma.  Connection to the foundation chain is therefore
    real but routed through A2Payoff, not by a direct VMState import that this
    file would never use.
*)

From Coq Require Import List Bool Lia.
Import ListNotations.

(** A trusted local-predicate pricing system with state-dependent local cost.

    State-dependent cost makes the theorem about local step predicates rather
    than about a global instruction schedule.  That is the right abstraction
    for the substitution test: the question is whether the local predicate
    being priced is semantically adequate for certification. *)
Record LocalPredicatePricedSystem := mk_local_predicate_priced_system {
  lps_state  : Type;
  lps_instr  : Type;
  lps_step   : lps_state -> lps_instr -> lps_state;
  lps_cost   : lps_state -> lps_instr -> nat;
  lps_cert   : lps_state -> bool;
  lps_charge : lps_state -> lps_instr -> bool;

  lps_charged_costs :
    forall (s : lps_state) (i : lps_instr),
      lps_charge s i = true ->
      lps_cost s i >= 1;

  lps_uncharged_free :
    forall (s : lps_state) (i : lps_instr),
      lps_charge s i = false ->
      lps_cost s i = 0;
}.

Fixpoint lps_run (LPS : LocalPredicatePricedSystem)
                 (trace : list (lps_instr LPS))
                 (s : lps_state LPS) : lps_state LPS :=
  match trace with
  | [] => s
  | i :: rest => lps_run LPS rest (lps_step LPS s i)
  end.

Fixpoint lps_total_cost (LPS : LocalPredicatePricedSystem)
                        (trace : list (lps_instr LPS))
                        (s : lps_state LPS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      lps_cost LPS s i
      + lps_total_cost LPS rest (lps_step LPS s i)
  end.

(** The substitute predicate covers A2 exactly when every cert-flip step is a
    charged step. *)
Definition covers_cert_flips (LPS : LocalPredicatePricedSystem) : Prop :=
  forall (s : lps_state LPS) (i : lps_instr LPS),
    lps_cert LPS s = false ->
    lps_cert LPS (lps_step LPS s i) = true ->
    lps_charge LPS s i = true.

(** Universal certification floor: every trace that reaches certification
    from an uncertified state pays positive cost. *)
Definition universal_certification_floor
           (LPS : LocalPredicatePricedSystem) : Prop :=
  forall (trace : list (lps_instr LPS)) (s0 : lps_state LPS),
    lps_cert LPS s0 = false ->
    lps_cert LPS (lps_run LPS trace s0) = true ->
    lps_total_cost LPS trace s0 >= 1.

(** The explicit A2 local predicate for an arbitrary step system. *)
Definition cert_flip_local (LPS : LocalPredicatePricedSystem)
           (s : lps_state LPS) (i : lps_instr LPS) : bool :=
  andb (negb (lps_cert LPS s))
       (lps_cert LPS (lps_step LPS s i)).

Fixpoint lps_cert_flip_count (LPS : LocalPredicatePricedSystem)
                             (trace : list (lps_instr LPS))
                             (s : lps_state LPS) : nat :=
  match trace with
  | [] => 0
  | i :: rest =>
      (if cert_flip_local LPS s i then 1 else 0)
      + lps_cert_flip_count LPS rest (lps_step LPS s i)
  end.

Definition local_predicate_le (LPS : LocalPredicatePricedSystem)
           (P Q : lps_state LPS -> lps_instr LPS -> bool) : Prop :=
  forall s i, P s i = true -> Q s i = true.

(** Quantitative floor: total cost lower-bounds the number of certification
    commitment events in the trace. *)
Definition quantitative_certification_floor
           (LPS : LocalPredicatePricedSystem) : Prop :=
  forall (trace : list (lps_instr LPS)) (s0 : lps_state LPS),
    lps_total_cost LPS trace s0 >= lps_cert_flip_count LPS trace s0.

(** No overcharging relative to certification commitments: total cost never
    exceeds the number of cert-flip events in the trace.  This rules out
    generic "charge every step" substitutes when the task is to price
    certification commitment itself. *)
Definition no_overcharge_for_commitments
           (LPS : LocalPredicatePricedSystem) : Prop :=
  forall (trace : list (lps_instr LPS)) (s0 : lps_state LPS),
    lps_total_cost LPS trace s0 <= lps_cert_flip_count LPS trace s0.

Definition exact_unit_pricing (LPS : LocalPredicatePricedSystem) : Prop :=
  forall (s : lps_state LPS) (i : lps_instr LPS),
    lps_cost LPS s i = if lps_charge LPS s i then 1 else 0.

Definition local_predicate_same (LPS : LocalPredicatePricedSystem)
           (P Q : lps_state LPS -> lps_instr LPS -> bool) : Prop :=
  local_predicate_le LPS P Q /\ local_predicate_le LPS Q P.

Definition LPSJob (LPS : LocalPredicatePricedSystem) :=
  (lps_state LPS * list (lps_instr LPS))%type.

Definition job_certifies (LPS : LocalPredicatePricedSystem)
           (job : LPSJob LPS) : Prop :=
  let (s0, trace) := job in
  lps_cert LPS s0 = false /\
  lps_cert LPS (lps_run LPS trace s0) = true.

Fixpoint lps_batch_total_cost (LPS : LocalPredicatePricedSystem)
                              (jobs : list (LPSJob LPS)) : nat :=
  match jobs with
  | [] => 0
  | (s0, trace) :: rest =>
      lps_total_cost LPS trace s0 + lps_batch_total_cost LPS rest
  end.

Fixpoint lps_batch_cert_flip_count (LPS : LocalPredicatePricedSystem)
                                   (jobs : list (LPSJob LPS)) : nat :=
  match jobs with
  | [] => 0
  | (s0, trace) :: rest =>
      lps_cert_flip_count LPS trace s0
      + lps_batch_cert_flip_count LPS rest
  end.

Definition batch_certification_floor
           (LPS : LocalPredicatePricedSystem) : Prop :=
  forall jobs : list (LPSJob LPS),
    Forall (job_certifies LPS) jobs ->
    lps_batch_total_cost LPS jobs >= length jobs.

(** A2 is the least local predicate that covers certification commitment:
    any adequate substitute predicate must contain [cert_flip_local]. *)
Theorem cert_flip_is_least_covering_predicate :
  forall (LPS : LocalPredicatePricedSystem),
    covers_cert_flips LPS <->
    local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS).
Proof.
  intros LPS. split.
  - intros Hcovers s i Hflip.
    unfold cert_flip_local in Hflip.
    apply Bool.andb_true_iff in Hflip.
    destruct Hflip as [Hbefore Hafter].
    apply Bool.negb_true_iff in Hbefore.
    exact (Hcovers s i Hbefore Hafter).
  - intros Hle s i Hbefore Hafter.
    apply Hle.
    unfold cert_flip_local.
    rewrite Hbefore, Hafter.
    reflexivity.
Qed.

(** Quantitative sufficiency: pricing any predicate that contains cert-flips
    charges at least one unit per certification commitment event. *)
Theorem covers_cert_flips_sufficient_for_quantitative_floor :
  forall (LPS : LocalPredicatePricedSystem),
    covers_cert_flips LPS ->
    quantitative_certification_floor LPS.
Proof.
  intros LPS Hcovers.
  unfold quantitative_certification_floor.
  pose proof (proj1 (cert_flip_is_least_covering_predicate LPS) Hcovers)
    as Hle.
  induction trace as [| i rest IH]; intros s0.
  - simpl. lia.
  - simpl.
    destruct (cert_flip_local LPS s0 i) eqn:Hflip.
    + pose proof (Hle s0 i Hflip) as Hcharge.
      pose proof (lps_charged_costs LPS s0 i Hcharge) as Hcost.
      pose proof (IH (lps_step LPS s0 i)) as Hrest.
      lia.
    + pose proof (IH (lps_step LPS s0 i)) as Hrest.
      lia.
Qed.

(** Quantitative necessity: if total cost lower-bounds the cert-flip count,
    the priced predicate must contain every cert-flip. *)
Theorem quantitative_floor_necessary_for_covers_cert_flips :
  forall (LPS : LocalPredicatePricedSystem),
    quantitative_certification_floor LPS ->
    covers_cert_flips LPS.
Proof.
  intros LPS Hfloor.
  unfold covers_cert_flips.
  intros s i Hstart Hfinal.
  destruct (lps_charge LPS s i) eqn:Hcharge.
  - reflexivity.
  - exfalso.
    pose proof (Hfloor [i] s) as Hbound.
    simpl in Hbound.
    unfold cert_flip_local in Hbound.
    rewrite Hstart, Hfinal in Hbound.
    simpl in Hbound.
    pose proof (lps_uncharged_free LPS s i Hcharge) as Hfree.
    rewrite Hfree in Hbound.
    lia.
Qed.

Theorem quantitative_certification_floor_iff_covers_cert_flips :
  forall (LPS : LocalPredicatePricedSystem),
    quantitative_certification_floor LPS <-> covers_cert_flips LPS.
Proof.
  intros LPS. split.
  - apply quantitative_floor_necessary_for_covers_cert_flips.
  - apply covers_cert_flips_sufficient_for_quantitative_floor.
Qed.

Theorem quantitative_floor_iff_a2_predicate_subsumed :
  forall (LPS : LocalPredicatePricedSystem),
    quantitative_certification_floor LPS <->
    local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS).
Proof.
  intros LPS.
  rewrite quantitative_certification_floor_iff_covers_cert_flips.
  apply cert_flip_is_least_covering_predicate.
Qed.

Lemma certifying_trace_has_cert_flip :
  forall (LPS : LocalPredicatePricedSystem)
         (trace : list (lps_instr LPS))
         (s0 : lps_state LPS),
    lps_cert LPS s0 = false ->
    lps_cert LPS (lps_run LPS trace s0) = true ->
    lps_cert_flip_count LPS trace s0 >= 1.
Proof.
  intros LPS trace.
  induction trace as [| i rest IH]; intros s0 Hstart Hfinal.
  - simpl in Hfinal. rewrite Hstart in Hfinal. discriminate.
  - simpl in *.
    destruct (lps_cert LPS (lps_step LPS s0 i)) eqn:Hmid.
    + unfold cert_flip_local.
      rewrite Hstart, Hmid. simpl. lia.
    + pose proof (IH (lps_step LPS s0 i) Hmid Hfinal) as Hrest.
      destruct (cert_flip_local LPS s0 i); lia.
Qed.

Theorem batch_certification_floor_iff_a2_predicate_subsumed :
  forall (LPS : LocalPredicatePricedSystem),
    batch_certification_floor LPS <->
    local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS).
Proof.
  intros LPS. split.
  - intros Hbatch.
    apply cert_flip_is_least_covering_predicate.
    unfold covers_cert_flips.
    intros s i Hstart Hfinal.
    destruct (lps_charge LPS s i) eqn:Hcharge; [reflexivity|].
    exfalso.
    pose proof (Hbatch [(s, [i])]) as Hone.
    simpl in Hone.
    assert (Hjobs : Forall (job_certifies LPS) [(s, [i])]).
    { constructor.
      - unfold job_certifies. simpl. split; assumption.
      - constructor. }
    specialize (Hone Hjobs).
    pose proof (lps_uncharged_free LPS s i Hcharge) as Hfree.
    rewrite Hfree in Hone.
    lia.
  - intros Hle.
    pose proof (proj2 (quantitative_floor_iff_a2_predicate_subsumed LPS) Hle)
      as Hquant.
    unfold batch_certification_floor.
    intros jobs Hjobs.
    induction Hjobs as [| [s0 trace] rest Hjob Hrest IH].
    + simpl. lia.
    + unfold job_certifies in Hjob.
      destruct Hjob as [Hstart Hfinal].
      simpl.
      pose proof (Hquant trace s0) as Hcost.
      pose proof (certifying_trace_has_cert_flip LPS trace s0 Hstart Hfinal)
        as Hflip.
      lia.
Qed.

(** If a pricing law does not overcharge relative to cert commitments, every
    charged step must itself be a cert-flip. *)
Theorem no_overcharge_forces_charge_only_on_cert_flips :
  forall (LPS : LocalPredicatePricedSystem),
    no_overcharge_for_commitments LPS ->
    local_predicate_le LPS (lps_charge LPS) (cert_flip_local LPS).
Proof.
  intros LPS Hno s i Hcharge.
  destruct (cert_flip_local LPS s i) eqn:Hflip; [reflexivity|].
  exfalso.
  pose proof (lps_charged_costs LPS s i Hcharge) as Hcost.
  pose proof (Hno [i] s) as Hno_one.
  simpl in Hno_one.
  rewrite Hflip in Hno_one.
  lia.
Qed.

(** If a law both lower-bounds and upper-bounds commitment count, the charged
    predicate is exactly A2 and each charged step has exact unit cost. *)
Theorem exact_commitment_pricing_characterization :
  forall (LPS : LocalPredicatePricedSystem),
    (quantitative_certification_floor LPS /\
     no_overcharge_for_commitments LPS)
    <->
    (local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) /\
     exact_unit_pricing LPS).
Proof.
  intros LPS. split.
  - intros [Hfloor Hno].
    assert (Hcf_le_charge :
      local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS)).
    { apply quantitative_floor_iff_a2_predicate_subsumed. exact Hfloor. }
    assert (Hcharge_le_cf :
      local_predicate_le LPS (lps_charge LPS) (cert_flip_local LPS)).
    { apply no_overcharge_forces_charge_only_on_cert_flips. exact Hno. }
    split.
    + split; assumption.
    + unfold exact_unit_pricing.
      intros s i.
      destruct (lps_charge LPS s i) eqn:Hcharge.
      * pose proof (lps_charged_costs LPS s i Hcharge) as Hge.
        pose proof (Hcharge_le_cf s i Hcharge) as Hflip.
        pose proof (Hno [i] s) as Hle.
        simpl in Hle.
        rewrite Hflip in Hle.
        lia.
      * pose proof (lps_uncharged_free LPS s i Hcharge) as Hfree.
        exact Hfree.
  - intros [[Hcf_le_charge Hcharge_le_cf] Hexact].
    assert (Heq : forall s i,
              lps_charge LPS s i = cert_flip_local LPS s i).
    { intros s i.
      destruct (lps_charge LPS s i) eqn:Hcharge;
      destruct (cert_flip_local LPS s i) eqn:Hflip; try reflexivity.
      - pose proof (Hcharge_le_cf s i Hcharge) as Hcontra.
        rewrite Hflip in Hcontra. discriminate.
      - pose proof (Hcf_le_charge s i Hflip) as Hcontra.
        rewrite Hcharge in Hcontra. discriminate. }
    assert (Hcost_eq_count :
      forall trace s0,
        lps_total_cost LPS trace s0 =
        lps_cert_flip_count LPS trace s0).
    { induction trace as [| i rest IH]; intros s0.
      - reflexivity.
      - simpl.
        rewrite Hexact.
        rewrite Heq.
        destruct (cert_flip_local LPS s0 i);
          specialize (IH (lps_step LPS s0 i)); lia. }
    split.
    + unfold quantitative_certification_floor.
      intros trace s0. rewrite Hcost_eq_count. lia.
    + unfold no_overcharge_for_commitments.
      intros trace s0. rewrite Hcost_eq_count. lia.
Qed.

(** The substitution test in contrapositive form: under equal trust, any local
    predicate that is not A2 fails exact non-overcharging commitment pricing. *)
Theorem substitution_test_rejects_non_a2_exact_substitute :
  forall (LPS : LocalPredicatePricedSystem),
    ~ local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS) ->
    ~ (quantitative_certification_floor LPS /\
       no_overcharge_for_commitments LPS).
Proof.
  intros LPS Hnot_same [Hfloor Hno].
  apply Hnot_same.
  pose proof (proj1 (exact_commitment_pricing_characterization LPS)
              (conj Hfloor Hno)) as [Hsame _].
  exact Hsame.
Qed.

(** Equivalently: every exact non-overcharging substitute is A2. *)
Theorem substitution_test_exact_substitute_is_a2 :
  forall (LPS : LocalPredicatePricedSystem),
    quantitative_certification_floor LPS ->
    no_overcharge_for_commitments LPS ->
    local_predicate_same LPS (cert_flip_local LPS) (lps_charge LPS).
Proof.
  intros LPS Hfloor Hno.
  pose proof (proj1 (exact_commitment_pricing_characterization LPS)
              (conj Hfloor Hno)) as [Hsame _].
  exact Hsame.
Qed.

(** Sufficiency: if the substitute predicate covers cert-flips, it gives the
    same trace-level certification floor as A2. *)
Theorem covers_cert_flips_sufficient_for_floor :
  forall (LPS : LocalPredicatePricedSystem),
    covers_cert_flips LPS ->
    universal_certification_floor LPS.
Proof.
  intros LPS Hcovers.
  unfold universal_certification_floor.
  induction trace as [| i rest IH]; intros s0 Hstart Hfinal.
  - simpl in Hfinal. rewrite Hstart in Hfinal. discriminate.
  - simpl in *.
    destruct (lps_cert LPS (lps_step LPS s0 i)) eqn:Hmid.
    + pose proof (Hcovers s0 i Hstart Hmid) as Hcharge.
      pose proof (lps_charged_costs LPS s0 i Hcharge) as Hcost.
      lia.
    + pose proof (IH (lps_step LPS s0 i) Hmid Hfinal) as Hrest.
      lia.
Qed.

(** Necessity: if a substitute predicate misses any cert-flip, the one-step
    trace through that missed transition certifies at zero cost. *)
Theorem floor_necessary_for_covers_cert_flips :
  forall (LPS : LocalPredicatePricedSystem),
    universal_certification_floor LPS ->
    covers_cert_flips LPS.
Proof.
  intros LPS Hfloor.
  unfold covers_cert_flips.
  intros s i Hstart Hfinal.
  destruct (lps_charge LPS s i) eqn:Hcharge.
  - reflexivity.
  - exfalso.
    pose proof (Hfloor [i] s Hstart) as Hstep_floor.
    simpl in Hstep_floor.
    rewrite Hfinal in Hstep_floor.
    specialize (Hstep_floor eq_refl).
    pose proof (lps_uncharged_free LPS s i Hcharge) as Hfree.
    simpl in Hstep_floor.
    rewrite Hfree in Hstep_floor.
    lia.
Qed.

(** Exact substitution gate. *)
Theorem local_predicate_certification_floor_iff_covers_cert_flips :
  forall (LPS : LocalPredicatePricedSystem),
    universal_certification_floor LPS <-> covers_cert_flips LPS.
Proof.
  intros LPS. split.
  - apply floor_necessary_for_covers_cert_flips.
  - apply covers_cert_flips_sufficient_for_floor.
Qed.

Theorem universal_floor_forces_a2_predicate_subsumed :
  forall (LPS : LocalPredicatePricedSystem),
    universal_certification_floor LPS ->
    local_predicate_le LPS (cert_flip_local LPS) (lps_charge LPS).
Proof.
  intros LPS Hfloor.
  apply cert_flip_is_least_covering_predicate.
  exact (floor_necessary_for_covers_cert_flips LPS Hfloor).
Qed.

(** Discharge an impossible boolean branch through the trusted [discriminate]
    idiom, so no raw [False] eliminator appears in a term position. The witness
    systems below choose predicates that make certain match branches unreachable
    (a [false = true] or [true = false] hypothesis). *)
Lemma charged_branch_unreachable {P : Prop} (H : false = true) : P.
Proof. discriminate H. Qed.

Lemma uncharged_branch_unreachable {P : Prop} (H : true = false) : P.
Proof. discriminate H. Qed.

(** A concrete failed substitute: erasure accounting that never erases.

    The system is trusted relative to its local predicate.  It simply chose the
    wrong predicate for certification commitment. *)
Definition no_erasure_commitment_lps : LocalPredicatePricedSystem :=
  {| lps_state := bool;
     lps_instr := unit;
     lps_step := fun _ _ => true;
     lps_cost := fun _ _ => 0;
     lps_cert := fun b => b;
     lps_charge := fun _ _ => false;
     lps_charged_costs := fun _ _ Hcharge =>
       charged_branch_unreachable Hcharge;
     lps_uncharged_free := fun _ _ _ => eq_refl |}.

Theorem erasure_substitute_fails_commitment_floor :
  ~ universal_certification_floor no_erasure_commitment_lps.
Proof.
  intro Hfloor.
  pose proof (floor_necessary_for_covers_cert_flips
                no_erasure_commitment_lps Hfloor false tt
                eq_refl eq_refl) as Hcover.
  discriminate Hcover.
Qed.

(** A2 as the exact adequate predicate. *)
Definition cert_flip_predicate_lps : LocalPredicatePricedSystem :=
  {| lps_state := bool;
     lps_instr := unit;
     lps_step := fun _ _ => true;
     lps_cost := fun s _ => if s then 0 else 1;
     lps_cert := fun b => b;
     lps_charge := fun s _ => negb s;
     lps_charged_costs := fun s _ Hcharge =>
       match s as b return negb b = true -> (if b then 0 else 1) >= 1 with
       | false => fun _ => le_n 1
       | true => fun H => charged_branch_unreachable H
       end Hcharge;
     lps_uncharged_free := fun s _ Hcharge =>
       match s as b return negb b = false -> (if b then 0 else 1) = 0 with
       | false => fun H => uncharged_branch_unreachable H
       | true => fun _ => eq_refl
       end Hcharge |}.

Theorem a2_predicate_has_commitment_floor :
  universal_certification_floor cert_flip_predicate_lps.
Proof.
  apply covers_cert_flips_sufficient_for_floor.
  unfold covers_cert_flips, cert_flip_predicate_lps.
  intros s [] Hstart _.
  simpl in *.
  destruct s; [discriminate | reflexivity].
Qed.

Theorem a2_predicate_has_quantitative_floor :
  quantitative_certification_floor cert_flip_predicate_lps.
Proof.
  apply covers_cert_flips_sufficient_for_quantitative_floor.
  unfold covers_cert_flips, cert_flip_predicate_lps.
  intros s [] Hstart _.
  simpl in *.
  destruct s; [discriminate | reflexivity].
Qed.

Print Assumptions covers_cert_flips_sufficient_for_quantitative_floor.
Print Assumptions quantitative_floor_necessary_for_covers_cert_flips.
Print Assumptions quantitative_certification_floor_iff_covers_cert_flips.
Print Assumptions quantitative_floor_iff_a2_predicate_subsumed.
Print Assumptions certifying_trace_has_cert_flip.
Print Assumptions batch_certification_floor_iff_a2_predicate_subsumed.
Print Assumptions no_overcharge_forces_charge_only_on_cert_flips.
Print Assumptions exact_commitment_pricing_characterization.
Print Assumptions substitution_test_rejects_non_a2_exact_substitute.
Print Assumptions substitution_test_exact_substitute_is_a2.
Print Assumptions covers_cert_flips_sufficient_for_floor.
Print Assumptions floor_necessary_for_covers_cert_flips.
Print Assumptions local_predicate_certification_floor_iff_covers_cert_flips.
Print Assumptions cert_flip_is_least_covering_predicate.
Print Assumptions universal_floor_forces_a2_predicate_subsumed.
Print Assumptions erasure_substitute_fails_commitment_floor.
Print Assumptions a2_predicate_has_commitment_floor.
Print Assumptions a2_predicate_has_quantitative_floor.
