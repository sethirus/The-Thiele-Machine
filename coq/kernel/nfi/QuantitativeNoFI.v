(** QuantitativeNoFI.v
    AXIOM 5: QUANTITATIVE NO FREE INSIGHT

    FROM 1 TO K
    UniversalCertificationCost.v proves:
        total_cost ≥ 1    (for any substrate satisfying A2)

    This file proves:
        total_cost ≥ K    where K = qcs_threshold

    K is the MINIMUM WITNESS needed to certify.  When K > 1, this says
    certifying something of complexity K costs K, every time. No way around it.
    This is the formal content of "insight requires cost proportional to
    what is learned."

    THE FIVE AXIOMS (fields of QuantitativeCertificationSystem and
    QuantitativeCertificationSystem_full)
    A2  (inherited, cs_cert_costs): cert transition costs ≥ 1
    A3. qcs_cost_bounds_witness:
          qcs_witness s + cs_cost i ≥ qcs_witness (cs_step s i)
          "Each instruction's cost bounds how much witness it can generate"
    A4. qcsf_witness_nondecreasing:
          qcs_witness s ≤ qcs_witness (cs_step s i)
          (NOT derivable from A3.  A3 bounds growth from above
           (w + cost ≥ w'); A4 bounds change from below (w ≤ w'):
           opposite directions.  Counterexample (w,cost,w') = (1,0,0)
           satisfies A3 with cost ≥ 0 yet violates A4.  Stated as its
           own field; idle for the ≥K floor, which uses only A3/A5/A6.)
    A5. qcs_cert_threshold_witness:
          cs_cert s = true → qcs_witness s ≥ qcs_threshold
          "Certification requires having accumulated ≥ K evidence"
    A6. Initial witness:
          qcs_witness s₀ = 0   (stated as theorem hypothesis)

    THE CENTRAL LEMMA (telescoping)
    qcs_witness s0 + cs_total_cost trace ≥ qcs_witness (cs_run trace s0)

    Proof: at each step, cost ≥ Δwitness.  Summing over the trace:
           total_cost ≥ total_Δwitness = final_witness - initial_witness.
    With initial_witness = 0: total_cost ≥ final_witness.
    With certified_requires_witness: final_witness ≥ K.
    Therefore: total_cost ≥ K.

    THE INFORMATION-THEORETIC READING
    qcs_witness measures HOW MUCH the state has learned.
    qcs_threshold is HOW MUCH it needs to have learned to certify.
    qcs_cost_bounds_witness says: learning costs.

    When K = 1: same as UniversalCertificationCost.v (A2 alone).
    When K = n: you need n units of evidence, each costing ≥ 1.
    When K = H(X): you need Shannon-entropy(X) evidence to certify X.
    When K = K(x): you need Kolmogorov-complexity(x) to certify x.

    The last two require connecting qcs_witness to an information measure;
    no theorem here makes that connection.

    A3/A4/A5 are requirements on the system, discharged per instantiation.
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost.

(**

    Extends CertificationSystem with:
      - qcs_witness   : state → nat  (the evidence accumulator)
      - qcs_threshold : nat          (minimum witness for certification)
      - A3: cost bounds witness growth
      - A5: certification requires threshold witness

    A4 (nondecreasing) does NOT follow from A3.  A3 gives w + cost ≥ w'
    (an upper bound on growth); A4 wants w ≤ w' (a lower bound on change);
    opposite directions, see (w,cost,w') = (1,0,0).  It is therefore
    axiomatized as its own field on QuantitativeCertificationSystem_full
    (see the analysis at that record below), and is idle in any case: the
    ≥K floor uses only A3, A5, A6.
*)

Record QuantitativeCertificationSystem := mk_qcs {
  (** Underlying CertificationSystem: inherits A2 (cs_cert_costs). *)
  qcs_base       : CertificationSystem;

  (** The witness function: how much evidence has been accumulated. *)
  qcs_witness    : cs_state qcs_base -> nat;

  (** The certification threshold: minimum witness needed for certification. *)
  qcs_threshold  : nat;

  (** A3: The cost of an instruction bounds the witness it can generate.

      Formally: witness_before + cost ≥ witness_after.

      This is the key quantitative axiom.  In nat arithmetic (no negatives),
      this says: the increase in witness (if any) is at most the cost paid.

      This is a model-level witness-growth bound. It does not identify the
      witness with physical information or the cost with work; those readings
      require a separate calibration.
  *)
  qcs_cost_bounds_witness :
    forall (s : cs_state qcs_base) (i : cs_instr qcs_base),
      qcs_witness s + cs_cost qcs_base i >= qcs_witness (cs_step qcs_base s i);

  (** A5: Certification requires having accumulated ≥ threshold evidence.

      Formally: cs_cert s = true → qcs_witness s ≥ qcs_threshold.

      This connects the binary cert indicator to the quantitative witness.
      When qcs_threshold = 1, this says "cert requires any nonzero evidence."
      When qcs_threshold = N, this says "cert requires N units of evidence."

      This is the stated threshold contract between the Boolean certification
      predicate and the witness. Its physical or semantic interpretation is
      outside this record.
  *)
  qcs_cert_threshold_witness :
    forall (s : cs_state qcs_base),
      cs_cert qcs_base s = true ->
      qcs_witness s >= qcs_threshold;
}.

(**

    A4 (witness nondecreasing) does NOT follow from A3.

    A3 says witness_before + cost ≥ witness_after, and cost ≥ 0 since
    cost : _ → nat. Together these do NOT give witness_after ≥ witness_before.
    Counterexample: witness_before = 1, cost = 0, witness_after = 0
    satisfies A3 (1 + 0 ≥ 0) with cost ≥ 0, yet witness_after < witness_before.
    The two inequalities bound opposite directions.

    Adding cs_cert_costs (A2), which gives a LOWER BOUND on cost when
    cert transitions, does not give nondecreasing either.

    A4 is therefore a separate field. It says that evidence cannot be
    "unlearned" (knowledge is persistent).
*)

(** A4 as a field: knowledge is monotone. *)
Record QuantitativeCertificationSystem_full := mk_qcs_full {
  (** The quantitative base (A2, A3, A5 included). *)
  qcsf_qcs       : QuantitativeCertificationSystem;

  (** A4: Witness is nondecreasing. Evidence once accumulated stays.

      Formally: qcs_witness s ≤ qcs_witness (cs_step qcs_base s i).

      This optional field says that the supplied witness value is monotone under
      every step. It is a formal persistence condition, not a general claim
      about memory, information, or physical erasure.

      (This can fail in systems with noise / forgetting; those would
       not satisfy NoFI in the strong quantitative sense.)
  *)
  qcsf_witness_nondecreasing :
    forall (s  : cs_state (qcs_base qcsf_qcs))
           (i  : cs_instr (qcs_base qcsf_qcs)),
      qcs_witness qcsf_qcs s <=
      qcs_witness qcsf_qcs (cs_step (qcs_base qcsf_qcs) s i);
}.

(**

    LEMMA (qcs_telescoping):
    For any QCS satisfying A3 (cost bounds witness growth),
    over any trace, the initial witness plus total cost bounds the
    final witness.

    Formally:
      qcs_witness s0 + cs_total_cost trace ≥ qcs_witness (cs_run trace s0)

    PROOF: Induction on the trace.
    - Base: qcs_witness s0 + 0 = qcs_witness s0 ≥ qcs_witness s0. ✓
    - Step: trace = i :: rest.
        By A3: qcs_witness s0 + cs_cost i ≥ qcs_witness (cs_step s0 i).
        By IH: qcs_witness (cs_step s0 i) + cs_total_cost rest
               ≥ qcs_witness (cs_run rest (cs_step s0 i)).
        Combining:
          qcs_witness s0 + cs_cost i + cs_total_cost rest
          ≥ qcs_witness (cs_step s0 i) + cs_total_cost rest
          ≥ qcs_witness (cs_run rest (cs_step s0 i))
          = qcs_witness (cs_run (i::rest) s0). ✓
*)

Lemma qcs_telescoping :
  forall (QCS : QuantitativeCertificationSystem)
         (trace : list (cs_instr (qcs_base QCS)))
         (s0 : cs_state (qcs_base QCS)),
    qcs_witness QCS s0 + cs_total_cost (qcs_base QCS) trace >=
    qcs_witness QCS (cs_run (qcs_base QCS) trace s0).
Proof.
  intros QCS.
  induction trace as [| i rest IH]; intros s0.
  - (* Base: empty trace. run returns s0. *)
    simpl. lia.
  - (* Step: trace = i :: rest. *)
    simpl.
    (* A3: qcs_witness s0 + cs_cost i ≥ qcs_witness (cs_step s0 i) *)
    pose proof (qcs_cost_bounds_witness QCS s0 i) as HA3.
    (* IH: qcs_witness (cs_step s0 i) + cs_total_cost rest ≥ qcs_witness (cs_run rest (cs_step s0 i)) *)
    specialize (IH (cs_step (qcs_base QCS) s0 i)).
    lia.
Qed.

(**

    THEOREM (universal_nfi_quantitative):

    For any QuantitativeCertificationSystem QCS satisfying A2, A3, A5,
    starting from witness = 0 and reaching certification:

        total_cost ≥ qcs_threshold

    PROOF:
    1. By qcs_telescoping (A3):
         0 + total_cost ≥ witness_final
    2. By A5 (qcs_cert_threshold_witness):
         witness_final ≥ qcs_threshold
    3. Therefore: total_cost ≥ qcs_threshold.
*)

Theorem universal_nfi_quantitative :
  forall (QCS : QuantitativeCertificationSystem)
         (trace : list (cs_instr (qcs_base QCS)))
         (s0 : cs_state (qcs_base QCS)),
    (** A6: initial witness = 0 *)
    qcs_witness QCS s0 = 0 ->
    (** Final state is certified *)
    cs_cert (qcs_base QCS) (cs_run (qcs_base QCS) trace s0) = true ->
    (** Conclusion: total cost ≥ threshold *)
    cs_total_cost (qcs_base QCS) trace >= qcs_threshold QCS.
Proof.
  intros QCS trace s0 Hinit Hcert.
  (* Step 1: total_cost ≥ witness_final (by telescoping, with initial = 0) *)
  pose proof (qcs_telescoping QCS trace s0) as Htele.
  rewrite Hinit in Htele.
  simpl in Htele.
  (* Step 2: witness_final ≥ threshold (by A5) *)
  pose proof (qcs_cert_threshold_witness QCS
                (cs_run (qcs_base QCS) trace s0)
                Hcert) as Hthresh.
  (* Combine *)
  lia.
Qed.

(** Witness lower bound: from a zero witness, any trace costs at least the
    final witness, whether or not the run certifies. *)
Theorem universal_nfi_quantitative_witness :
  forall (QCS : QuantitativeCertificationSystem)
         (trace : list (cs_instr (qcs_base QCS)))
         (s0 : cs_state (qcs_base QCS)),
    qcs_witness QCS s0 = 0 ->
    cs_total_cost (qcs_base QCS) trace >=
      qcs_witness QCS (cs_run (qcs_base QCS) trace s0).
Proof.
  intros QCS trace s0 Hinit.
  pose proof (qcs_telescoping QCS trace s0) as Htele.
  rewrite Hinit in Htele. simpl in Htele.
  exact Htele.
Qed.

(** What this file does not do. It states the threshold floor for any
    system that supplies A3 and A5; it does not connect the witness to an
    information measure. With the witness a Shannon entropy the floor would
    read cost >= H(X), and with it a Kolmogorov complexity cost >= K(x); no
    theorem here makes either connection. *)
