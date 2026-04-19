(** QuantitativeNoFI.v
    AXIOM 5: QUANTITATIVE NO FREE INSIGHT

    THE GAP BEING CLOSED
    UniversalCertificationCost.v proved:
        total_cost ≥ 1    (for any substrate satisfying A2)

    This file pushes to:
        total_cost ≥ K    where K = cs_cert_threshold

    K is the MINIMUM WITNESS needed to certify.  When K > 1, this says
    you cannot certify something of complexity K without spending K cost.
    This is the formal content of "insight requires cost proportional to
    what is learned."

    THE FIVE AXIOMS
    A2  (inherited): cert transition costs ≥ 1
    A3. cs_witness_cost_step:
          cs_witness s + cs_cost i ≥ cs_witness (cs_step s i)
          "Each instruction's cost bounds how much witness it can generate"
    A4. cs_witness_nondecreasing:
          cs_witness s ≤ cs_witness (cs_step s i)
          (Derivable from A3 when cs_cost ≥ 0, but stated separately
           for clarity and to match the intuition)
    A5. cs_certified_requires_witness:
          cs_cert s = true → cs_witness s ≥ cs_cert_threshold
          "Certification requires having accumulated ≥ K evidence"
    A6. cs_witness_initial:
          cs_witness s₀ = 0   (stated as theorem hypothesis)

    THE CENTRAL LEMMA (telescoping)
    cs_witness s0 + cs_total_cost trace ≥ cs_witness (cs_run trace s0)

    Proof: at each step, cost ≥ Δwitness.  Summing over the trace:
           total_cost ≥ total_Δwitness = final_witness - initial_witness.
    With initial_witness = 0: total_cost ≥ final_witness.
    With certified_requires_witness: final_witness ≥ K.
    Therefore: total_cost ≥ K.

    THE INFORMATION-THEORETIC READING
    cs_witness measures HOW MUCH the state has learned.
    cs_cert_threshold is HOW MUCH it needs to have learned to certify.
    cs_witness_cost_step says: learning costs.

    When K = 1: same as UniversalCertificationCost.v (A2 alone).
    When K = n: you need n units of evidence, each costing ≥ 1.
    When K = H(X): you need Shannon-entropy(X) evidence to certify X.
    When K = K(x): you need Kolmogorov-complexity(x) to certify x.

    The last two require connecting cs_witness to an information measure.
    That is the open problem.

    A3/A4/A5 are requirements on the system, discharged per instantiation.
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           AbstractNoFI UniversalCertificationCost
                           MuLedgerConservation.

(**

    Extends CertificationSystem with:
      - cs_witness       : state → nat  (the evidence accumulator)
      - cs_cert_threshold : nat          (minimum witness for certification)
      - A3: cost bounds witness growth
      - A5: certification requires threshold witness

    A4 (nondecreasing) follows from A3 when cs_cost ≥ 0 (which is always
    true since cs_cost : _ → nat).  We derive it rather than axiomatize it.
*)

Record QuantitativeCertificationSystem := mk_qcs {
  (** Underlying CertificationSystem — inherits A2 (cs_cert_costs). *)
  qcs_base       : CertificationSystem;

  (** The witness function: how much evidence has been accumulated. *)
  qcs_witness    : cs_state qcs_base -> nat;

  (** The certification threshold: minimum witness needed for certification. *)
  qcs_threshold  : nat;

  (** A3: The cost of an instruction bounds the witness it can generate.

      Formally: witness_before + cost ≥ witness_after.

      This is the key quantitative axiom.  In nat arithmetic (no negatives),
      this says: the increase in witness (if any) is at most the cost paid.

      Physical reading: you cannot learn more than you pay for.
      Information-theoretic reading: Δinformation ≤ Δwork.
  *)
  qcs_cost_bounds_witness :
    forall (s : cs_state qcs_base) (i : cs_instr qcs_base),
      qcs_witness s + cs_cost qcs_base i >= qcs_witness (cs_step qcs_base s i);

  (** A5: Certification requires having accumulated ≥ threshold evidence.

      Formally: cs_cert s = true → qcs_witness s ≥ qcs_threshold.

      This connects the binary cert indicator to the quantitative witness.
      When qcs_threshold = 1, this says "cert requires any nonzero evidence."
      When qcs_threshold = N, this says "cert requires N units of evidence."

      Physical reading: you cannot certify something of complexity N without
      having accumulated N units of evidence.
  *)
  qcs_cert_threshold_witness :
    forall (s : cs_state qcs_base),
      cs_cert qcs_base s = true ->
      qcs_witness s >= qcs_threshold;
}.

(**

    A4 (witness nondecreasing) follows from A3:
    cost ≥ 0 (since cost : _ → nat) and A3 gives:
    witness_before + cost ≥ witness_after ≥ witness_before.
    The last inequality is NOT from A3 directly — it's what we want to prove.

    Actually: A3 says witness_before + cost ≥ witness_after.
    This does NOT immediately give witness_after ≥ witness_before.
    We need an additional argument.

    However: if we also assume cs_cert_costs (A2), which gives a LOWER BOUND
    on cost when cert transitions, we don't get nondecreasing for free.

    DECISION: Add A4 as a separate axiom.  It is mild and natural — it says
    that evidence cannot be "unlearned" (knowledge is persistent).
*)

(** A4 as a field — knowledge is monotone. *)
Record QuantitativeCertificationSystem_full := mk_qcs_full {
  (** The quantitative base (A2, A3, A5 included). *)
  qcsf_qcs       : QuantitativeCertificationSystem;

  (** A4: Witness is nondecreasing — evidence once accumulated stays.

      Formally: qcs_witness s ≤ qcs_witness (cs_step qcs_base s i).

      Physical reading: you cannot "unlearn" something.
      Information-theoretic reading: information is not spontaneously lost.

      (This can fail in systems with noise / forgetting — those would
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

(** Stronger statement: also gives the explicit witness lower bound. *)
Theorem universal_nfi_quantitative_witness :
  forall (QCS : QuantitativeCertificationSystem)
         (trace : list (cs_instr (qcs_base QCS)))
         (s0 : cs_state (qcs_base QCS)),
    qcs_witness QCS s0 = 0 ->
    cs_cert (qcs_base QCS) (cs_run (qcs_base QCS) trace s0) = true ->
    cs_total_cost (qcs_base QCS) trace >=
      qcs_witness QCS (cs_run (qcs_base QCS) trace s0).
Proof.
  intros QCS trace s0 Hinit Hcert.
  pose proof (qcs_telescoping QCS trace s0) as Htele.
  rewrite Hinit in Htele. simpl in Htele.
  exact Htele.
Qed.

(**

    The simplest Thiele instantiation: cs_witness = vm_mu, threshold = 1.

    A3: vm_mu s + instruction_cost i ≥ vm_mu (vm_apply s i)
        This is an EQUALITY by vm_apply_mu.  So A3 holds trivially.

    A5: cs_cert (vm_apply s i) = true → vm_mu(vm_apply s i) ≥ 1.
        This follows from certification_requires_positive_mu.

    WHAT THIS GIVES: total_cost ≥ 1.
    Same as UniversalCertificationCost.v — not yet more powerful.

    WHY IT MATTERS: This proves the framework is instantiable.
    The interesting work is lifting threshold from 1 to a content-dependent K.
*)

(** A3 for Thiele (cert_addr channel, witness = vm_mu):
    vm_mu s + instruction_cost i ≥ vm_mu (vm_apply s i)
    (equality, since vm_apply_mu gives exact equality) *)
Lemma thiele_cost_bounds_witness_mu :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_mu) + instruction_cost i >= (vm_apply s i).(vm_mu).
Proof.
  intros s i.
  rewrite vm_apply_mu. lia.
Qed.

(** A5 for Thiele (cert_addr channel):
    thiele_cert_bool s = true → vm_mu s ≥ 1.

    PROOF: thiele_cert_bool s = true means csr_cert_addr ≠ 0.
    This channel can only be reached through cert-addr-setters, each costing ≥ 1.
    But we need this as a STATIC property of the state, not a trace property.

    SUBTLETY: In Coq, a VMState could be constructed directly with
    csr_cert_addr ≠ 0 AND vm_mu = 0.  The static property doesn't hold
    for arbitrary states — it holds for states REACHABLE from initial state.

    RESOLUTION: Weaken to threshold = 0 for the general static form,
    and use the trace-level theorem for the interesting case.
    OR: use a different witness function that is always ≥ 1 when certified,
    by construction.

    We choose the second approach: define the witness as
      witness_cert_addr s := if thiele_cert_bool s then 1 else 0
    This trivially satisfies A5 with threshold = 1.
*)

Definition thiele_witness_cert_addr (s : VMState) : nat :=
  if thiele_cert_bool s then 1 else 0.

(** A3 for thiele_witness_cert_addr:
    thiele_witness_cert_addr s + instruction_cost i
    ≥ thiele_witness_cert_addr (vm_apply s i).

    Case split: if the transition sets cert (cert_addr 0 → nonzero), cost ≥ 1.
    If cert stays the same (false→false or true→true), witness unchanged, trivial.
*)
Lemma thiele_cert_addr_cost_bounds_witness :
  forall (s : VMState) (i : vm_instruction),
    thiele_witness_cert_addr s + instruction_cost i >=
    thiele_witness_cert_addr (vm_apply s i).
Proof.
  intros s i.
  unfold thiele_witness_cert_addr.
  destruct (thiele_cert_bool s) eqn:Hs;
  destruct (thiele_cert_bool (vm_apply s i)) eqn:Hsi;
  simpl.
  - lia.
  - lia.
  - (* cert was false, now true — cost ≥ 1 *)
    pose proof (thiele_cert_bool_zero_iff s) as [Hzero _].
    pose proof (thiele_cert_bool_nonzero_iff (vm_apply s i)) as [Hnonzero _].
    pose proof (no_free_certification s i (Hzero Hs) (Hnonzero Hsi)).
    lia.
  - lia.
Qed.

(** A5 for thiele_witness_cert_addr:
    thiele_cert_bool s = true → thiele_witness_cert_addr s ≥ 1.
    Trivially true by definition. *)
Lemma thiele_cert_addr_threshold_witness :
  forall (s : VMState),
    cs_cert thiele_cert_addr_system s = true ->
    thiele_witness_cert_addr s >= 1.
Proof.
  intros s Hcert.
  unfold thiele_witness_cert_addr. simpl in Hcert. rewrite Hcert. simpl. lia.
Qed.

(** The Thiele VM as a QuantitativeCertificationSystem (threshold = 1). *)
Definition thiele_qcs_cert_addr : QuantitativeCertificationSystem :=
  {|
    qcs_base      := thiele_cert_addr_system;
    qcs_witness   := thiele_witness_cert_addr;
    qcs_threshold := 1;
    qcs_cost_bounds_witness      := thiele_cert_addr_cost_bounds_witness;
    qcs_cert_threshold_witness   := thiele_cert_addr_threshold_witness;
  |}.

(** Quantitative NoFI for Thiele VM (cert_addr channel), threshold = 1. *)
Theorem thiele_quantitative_nfi_cert_addr :
  forall (trace : list vm_instruction) (s0 : VMState),
    thiele_witness_cert_addr s0 = 0 ->
    thiele_cert_bool (cs_run (qcs_base thiele_qcs_cert_addr) trace s0) = true ->
    cs_total_cost (qcs_base thiele_qcs_cert_addr) trace >= 1.
Proof.
  intros trace s0 Hinit Hcert.
  exact (universal_nfi_quantitative thiele_qcs_cert_addr trace s0 Hinit Hcert).
Qed.

(**

    THE CURRENT STATE:
    With threshold = 1, this is equivalent to UniversalCertificationCost.v.
    The quantitative theorem gives total_cost ≥ 1.

    WHAT AXIOM 5 PROPER REQUIRES:
    A witness function W : VMState → nat such that:

      (A) W(s) measures the INFORMATION CONTENT of the certificate in s.
          Not merely "is there a certificate" (binary) but "how complex
          is the certificate?"

      (B) W satisfies A3 with threshold K > 1.
          Then: total_cost ≥ K = complexity of certificate.

      (C) K depends on WHAT is being certified, not just the fact that
          something is certified.  This connects to Kolmogorov complexity,
          Shannon entropy, or circuit lower bounds.

    THE CANDIDATE WITNESS FUNCTIONS (to be developed):

    W1. Certificate payload bits:
          W(s) := concrete bit length of the certificate payload reachable from
          csr_cert_addr in s's formula store.
          Meaning: larger certificate payloads cost more.
          K = payload_bit_length(cert_content).
          Problem: requires formalizing the formula store lookup.

    W2. CHSH witness count:
          W(s) := total CHSH trials accumulated in vm_witness counters.
          Meaning: more quantum evidence requires more trials.
          K = N_CHSH_trials needed to distinguish quantum from classical.
          Connection: Tsirelson bound violation requires ≥ N trials.

    W3. Partition graph complexity:
          W(s) := some measure of vm_graph complexity (e.g., |modules| + |morphisms|).
          Meaning: certifying a complex partition structure costs more.
          K = complexity of the partition structure being certified.

    W4. Shannon entropy of the cert content:
          W(s) := H(cert_distribution) (in some discrete approximation).
          K = H(X) for the random variable X being certified.
          Connection: Shannon's theorem on data compression.

    W5. Kolmogorov complexity (non-computable, but formalizable as an oracle):
          W(s) := K(cert_content).
          K = K(x) for the string x being certified.
          Connection: Chaitin's incompleteness theorem.
          Requires: an oracle for K, which must be axiomatized.

    DEVELOPMENT STATUS:
    1. DONE (this file): quantitative framework + trivial threshold = 1.
    2. DONE: W2 (CHSH witness count) — proven as chsh_trial_count_lower_bound
       below. Certifying a CHSH violation requires ≥ N_min CHSH trials.
    3. OPEN: W1 (cert payload bits) — connect cert cost to cert size.
    4. OPEN: W4 (Shannon) — formal connection to information theory.
    5. OPEN: W5 (Kolmogorov) — requires oracle axiom.

    WHAT WOULD MAKE THIS EPOCH-SHIFTING:
    W5 with a concrete, falsifiable connection between K(cert) and
    physical cost.  That would make "No Free Insight" a precise formal
    analog of the Landauer bound for cognition.

    above as W1-W5.
*)

(**

    The Thiele VM tracks CHSH trial counts in vm_witness (WitnessCounts, 8
    fields: wc_same_00, wc_diff_00, ..., wc_same_11, wc_diff_11).

    This section builds a SEPARATE CertificationSystem for the CHSH channel:
      - cost function:  chsh_trial_cost (counts valid CHSH_TRIAL executions)
      - cert predicate: chsh_cert (at least one valid trial has been run)
      - witness:        witness_total s.(vm_witness) (total trial count)
      - threshold:      1 (first non-trivial iteration)
 chsh_trial_cost is NOT instruction_cost (mu-cost).  The two cost
    notions are orthogonal.  A single CHSH_TRIAL can have mu_delta = 0 but
    still counts as 1 CHSH trial.  Using instruction_cost for A3 would fail.

    RESULT: total CHSH_TRIAL count ≥ 1 to transition from uncertified to
    certified (i.e., at least one valid trial has been run).

    NEXT ITERATION: Lift threshold from 1 to N_min for Tsirelson violation
    detection, by proving A5 with threshold = N_min.

*)

(** The CHSH cost function: counts valid CHSH_TRIAL executions.
    Cost = 1 if the instruction is a CHSH_TRIAL with valid bits.
    Cost = 0 for everything else (including invalid-bit CHSH_TRIALs). *)
Definition chsh_trial_cost (i : vm_instruction) : nat :=
  match i with
  | instr_chsh_trial x y a b _ =>
      if chsh_bits_ok x y a b then 1 else 0
  | _ => 0
  end.

(** Total CHSH witness count: sum of all 8 WitnessCounts buckets.
    Delegates to witness_total from VMState.v. *)
Definition chsh_total_witness (s : VMState) : nat :=
  witness_total s.(vm_witness).

(**
    HELPER LEMMA 1: record_trial increments witness_total by exactly 1.
    Proof: case split on (x,y) ∈ {(0,0),(0,S),(S,0),(S,S)} and Nat.eqb a b.
    Each case increments exactly one bucket of witness_total. *)
Lemma record_trial_total :
  forall (wc : WitnessCounts) (x y a b : nat),
    witness_total (record_trial wc x y a b) = witness_total wc + 1.
Proof.
  intros wc x y a b.
  unfold record_trial, witness_total.
  destruct x as [|x']; destruct y as [|y'];
  destruct (Nat.eqb a b); simpl; lia.
Qed.

(**
    HELPER LEMMA 2: vm_apply changes vm_witness ONLY for instr_chsh_trial
    with valid bits (chsh_bits_ok = true).  All other instructions
    (including CHSH_TRIAL with invalid bits) preserve vm_witness exactly.

    Proof uses the same tactic pattern as vm_apply_certified in PrimeAxiom.v:
    destruct + repeat-match-destruct handles all opaque conditionals. *)
Lemma vm_apply_witness :
  forall (s : VMState) (i : vm_instruction),
    (vm_apply s i).(vm_witness) =
    match i with
    | instr_chsh_trial x y a b _ =>
        if chsh_bits_ok x y a b then record_trial s.(vm_witness) x y a b
        else s.(vm_witness)
    | _ => s.(vm_witness)
    end.
Proof.
  intros s i.
  destruct i; simpl;
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  end;
  simpl; unfold advance_state, advance_state_reveal,
    advance_state_rm, jump_state, jump_state_rm; simpl;
  reflexivity.
Qed.

(**
    A3 PROOF: CHSH trial cost bounds witness growth.  ZERO ADMITTED.

    For valid CHSH_TRIAL: chsh_trial_cost = 1, witness grows by 1 (equality).
    For invalid CHSH_TRIAL: chsh_trial_cost = 0, witness unchanged (equality).
    For all other instructions: chsh_trial_cost = 0, witness unchanged.
*)
Lemma chsh_a3_obligation :
  forall (s : VMState) (i : vm_instruction),
    chsh_total_witness s + chsh_trial_cost i >=
    chsh_total_witness (vm_apply s i).
Proof.
  intros s i.
  unfold chsh_total_witness.
  rewrite (vm_apply_witness s i).
  destruct i; simpl; try lia.
  (* instr_chsh_trial: case split on validity of bits *)
  destruct (chsh_bits_ok x y a b) eqn:Hbits; simpl.
  - (* valid bits: trial_cost = 1, witness grows by 1 *)
    rewrite record_trial_total. lia.
  - (* invalid bits: trial_cost = 0, witness unchanged *)
    lia.
Qed.

(**
    THE CHSH CERTIFICATION SYSTEM

    Cert predicate: at least one valid CHSH trial has been recorded.
    (witness_total s.(vm_witness) ≥ 1, equivalently 0 < witness_total ...)
    Cost function: chsh_trial_cost (counts valid CHSH_TRIAL executions).
    Step function: vm_apply (same underlying VM).

    A2 PROOF: The only way to go from cert=false (no trials) to cert=true
    (≥1 trial) in one step is via instr_chsh_trial with valid bits.
    That instruction has chsh_trial_cost = 1 ≥ 1.
*)

(** CHSH cert predicate: true iff at least one valid CHSH trial has run. *)
Definition chsh_cert (s : VMState) : bool :=
  Nat.ltb 0 (witness_total s.(vm_witness)).

(** A2 for the CHSH system: cert transition requires a valid CHSH_TRIAL. *)
Lemma chsh_a2 :
  forall (s : VMState) (i : vm_instruction),
    chsh_cert s = false ->
    chsh_cert (vm_apply s i) = true ->
    chsh_trial_cost i >= 1.
Proof.
  intros s i Hbefore Hafter.
  unfold chsh_cert in *.
  pose proof (vm_apply_witness s i) as Hw.
  rewrite Hw in Hafter.
  destruct i; simpl in *;
  (* Non-CHSH: vm_witness unchanged, so Hafter = Hbefore — contradiction *)
  try (rewrite Hbefore in Hafter; discriminate).
  (* instr_chsh_trial: case split on bit validity *)
  destruct (chsh_bits_ok x y a b) eqn:Hbits; simpl in *.
  - (* valid bits: simpl already reduced chsh_trial_cost to 1 *)
    lia.
  - (* invalid bits: witness unchanged — contradiction *)
    rewrite Hbefore in Hafter. discriminate.
Qed.

(** The CHSH CertificationSystem. *)
Definition chsh_cert_system : CertificationSystem :=
  {|
    cs_state     := VMState;
    cs_instr     := vm_instruction;
    cs_step      := vm_apply;
    cs_cost      := chsh_trial_cost;
    cs_cert      := chsh_cert;
    cs_cert_costs := chsh_a2;
  |}.

(** A5 for CHSH QCS (threshold = 1): if cert = true, witness ≥ 1. *)
Lemma chsh_a5 :
  forall (s : VMState),
    cs_cert chsh_cert_system s = true ->
    witness_total s.(vm_witness) >= 1.
Proof.
  intros s Hcert.
  simpl in Hcert. unfold chsh_cert in Hcert.
  apply Nat.ltb_lt in Hcert. lia.
Qed.

(** The CHSH QuantitativeCertificationSystem (threshold = 1).
    A3 discharged by chsh_a3_obligation (zero Admitted).
    A5 discharged by chsh_a5.

    WHAT THIS GIVES:
    Any trace from zero CHSH trials to ≥1 CHSH trial contains at least
    one valid CHSH_TRIAL instruction.  Total CHSH_TRIAL count ≥ 1.

    NEXT ITERATION — W2 proper:
    Lift threshold to N_min (trials needed for Tsirelson violation detection).
    Requires: A5 for N_min: witness_total ≥ N_min → violation certifiable.
    Connection to Tsirelson bound via CHSHExtraction.v / CHSH.v. *)
Definition chsh_qcs : QuantitativeCertificationSystem :=
  {|
    qcs_base                   := chsh_cert_system;
    qcs_witness                := (fun s => witness_total s.(vm_witness));
    qcs_threshold              := 1;
    qcs_cost_bounds_witness    := chsh_a3_obligation;
    qcs_cert_threshold_witness := chsh_a5;
  |}.

(** Quantitative NoFI for CHSH channel: any trace achieving cert
    from zero trials requires executing ≥1 valid CHSH_TRIAL.
    Zero Admitted. *)
Theorem chsh_quantitative_nfi :
  forall (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0 ->
    chsh_cert (cs_run chsh_cert_system trace s0) = true ->
    cs_total_cost chsh_cert_system trace >= 1.
Proof.
  intros trace s0 Hinit Hcert.
  apply (universal_nfi_quantitative chsh_qcs trace s0).
  - simpl. exact Hinit.
  - exact Hcert.
Qed.

(**

    The threshold=1 CHSH QCS proves: one trial requires one instruction.
    But the interesting bound is: N trials require N instructions.

    This section parameterizes the CHSH cert predicate by N, giving a family
    of QCS instances:

        chsh_cert_n N s := (N <=? witness_total s.(vm_witness))

    A2_n: cert-false → cert-true in one step requires a valid CHSH_TRIAL.
    A5_n: cert = true → witness_total ≥ N (trivially, by Nat.leb_le).
    A3: unchanged — same chsh_a3_obligation works for all N.

    THEOREM (chsh_trial_count_lower_bound):
    Starting from zero trials, accumulating N valid CHSH trials requires
    executing AT LEAST N valid CHSH_TRIAL instructions.

    CONTENT: The VM cannot fabricate trial counts by any other means.
    No other instruction changes vm_witness.  Every trial is authentic.
    This is formal proof of trial authenticity for arbitrary N.

*)

(** CHSH cert predicate parameterized by N: true when ≥N trials recorded. *)
Definition chsh_cert_n (n : nat) (s : VMState) : bool :=
  Nat.leb n (witness_total s.(vm_witness)).

(** A2 for threshold N: transition from cert=false to cert=true
    requires a valid CHSH_TRIAL (cost = 1).

    PROOF: cert=false means witness_total < N.
    cert=true after means witness_total ≥ N.
    Since vm_witness only changes via valid CHSH_TRIAL (by vm_apply_witness),
    and record_trial grows witness_total by exactly 1, the step must be a
    valid CHSH_TRIAL, which has chsh_trial_cost = 1 ≥ 1. *)
Lemma chsh_a2_n :
  forall (n : nat) (s : VMState) (i : vm_instruction),
    chsh_cert_n n s = false ->
    chsh_cert_n n (vm_apply s i) = true ->
    chsh_trial_cost i >= 1.
Proof.
  intros n s i Hbefore Hafter.
  unfold chsh_cert_n in *.
  rewrite (vm_apply_witness s i) in Hafter.
  destruct i; simpl in *;
  try (rewrite Hbefore in Hafter; discriminate).
  destruct (chsh_bits_ok x y a b) eqn:Hbits; simpl in *.
  - lia.
  - rewrite Hbefore in Hafter. discriminate.
Qed.

(** A5 for threshold N: cert = true → witness_total ≥ N. Trivial. *)
Lemma chsh_a5_n :
  forall (n : nat) (s : VMState),
    chsh_cert_n n s = true ->
    witness_total s.(vm_witness) >= n.
Proof.
  intros n s Hcert.
  unfold chsh_cert_n in Hcert.
  apply Nat.leb_le in Hcert. lia.
Qed.

(** CHSH CertificationSystem with threshold N. *)
Definition chsh_cert_system_n (n : nat) : CertificationSystem :=
  {|
    cs_state     := VMState;
    cs_instr     := vm_instruction;
    cs_step      := vm_apply;
    cs_cost      := chsh_trial_cost;
    cs_cert      := chsh_cert_n n;
    cs_cert_costs := chsh_a2_n n;
  |}.

(** A3 for chsh_cert_system_n: same obligation as before — cost bounds
    witness growth regardless of threshold.  Shared across all N. *)
Lemma chsh_a3_n :
  forall (n : nat) (s : VMState) (i : vm_instruction),
    witness_total s.(vm_witness) + cs_cost (chsh_cert_system_n n) i >=
    witness_total (cs_step (chsh_cert_system_n n) s i).(vm_witness).
Proof.
  intros n s i. simpl.
  exact (chsh_a3_obligation s i).
Qed.

(** CHSH QuantitativeCertificationSystem with threshold N. *)
Definition chsh_qcs_n (n : nat) : QuantitativeCertificationSystem :=
  {|
    qcs_base                   := chsh_cert_system_n n;
    qcs_witness                := (fun s => witness_total s.(vm_witness));
    qcs_threshold              := n;
    qcs_cost_bounds_witness    := chsh_a3_n n;
    qcs_cert_threshold_witness := chsh_a5_n n;
  |}.

(**
    THE W2 N CHSH TRIALS REQUIRE N CHSH_TRIAL INSTRUCTIONS.

    Formal content:
    Starting from a state with zero accumulated trials, any trace that
    brings witness_total to ≥ N must execute at least N valid CHSH_TRIAL
    instructions (instructions with chsh_trial_cost = 1).

    The vm_witness field CANNOT be incremented by any other instruction.
    This is a formal proof of trial authenticity: the count is unforgeable.

    INFORMATION-THEORETIC READING:
    Each valid CHSH_TRIAL contributes one bit of quantum evidence.
    Accumulating N bits of quantum evidence requires N quantum measurements.
    Cost(evidence) ≥ N ≥ evidence_count.

    This is the W2 instantiation of the quantitative NoFI principle.
*)
Theorem chsh_trial_count_lower_bound :
  forall (n : nat) (trace : list vm_instruction) (s0 : VMState),
    (** Start from zero accumulated trials *)
    witness_total s0.(vm_witness) = 0 ->
    (** Reach N accumulated trials *)
    chsh_cert_n n (cs_run (chsh_cert_system_n n) trace s0) = true ->
    (** Conclusion: executed at least N valid CHSH_TRIAL instructions *)
    cs_total_cost (chsh_cert_system_n n) trace >= n.
Proof.
  intros n trace s0 Hinit Hcert.
  apply (universal_nfi_quantitative (chsh_qcs_n n) trace s0).
  - (* initial witness = 0 *)
    simpl. exact Hinit.
  - (* final state certified *)
    exact Hcert.
Qed.

(** Corollary: chsh_qcs_n 1 = chsh_qcs (definitionally). *)
Lemma chsh_qcs_n_1_matches :
  forall (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0 ->
    chsh_cert_n 1 (cs_run (chsh_cert_system_n 1) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n 1) trace >= 1.
Proof.
  intros trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound 1 trace s0 Hinit Hcert).
Qed.

(**
    SUMMARY: WHAT IS DONE AND WHAT COMES NEXT

    DONE (this file):
    1. QCS record with A2/A3/A5, telescoping lemma, universal_nfi_quantitative.
    2. Thiele trivial instantiation (threshold=1, cert_addr channel, mu-cost).
    3. CHSH threshold=1 instantiation (one trial requires one instruction).
    4. W2 PROPER: chsh_trial_count_lower_bound — N trials require N instructions.
       - chsh_cert_n N: parameterized cert predicate (N <=? witness_total)
       - chsh_a2_n: A2 for any N (same proof structure as threshold=1)
       - chsh_a5_n: A5 for any N (trivial from Nat.leb_le)
       - chsh_a3_n: A3 for any N (delegates to chsh_a3_obligation)
       - chsh_qcs_n: family of QCS parameterized by threshold N
       - chsh_trial_count_lower_bound: the W2 theorem for arbitrary N
    The vm_witness field is an unforgeable trial counter.
    Any state with witness_total ≥ N was reached via ≥ N valid CHSH_TRIALs.
    Cost(N quantum measurements) ≥ N.

    COMPLETED: STATISTICAL CONNECTION (W2 statistical):
    CHSHStatisticalBridge.v imports W2 and applies Hoeffding concentration
    bounds to prove witness_total ≥ N_min → CHSH violation statistically
    certified at confidence (1 - δ).

    LATER:
    W1 (cert payload bits): cost ≥ |cert_content|_bits.
    W4 (Shannon entropy): cost ≥ H(X) for certified distribution.
    W5 (Kolmogorov): cost ≥ K(x) — requires oracle axiom (Chaitin-style).

*)
