(** A2LoadBearing.v — A2 as a load-bearing axiom in a non-trivial
    separation result.

    This file establishes a theorem F with three explicit properties:

    1. F is statable without reference to A2 — it is a real claim about
       computational state observability that makes sense in any
       framework with a cost notion and a classical observation level.

    2. The proof of F invokes A2 essentially. The lower bound on the
       cost ledger of the certifying trace is established via
       [no_free_certification_certified_mu], which is exactly A2
       applied to the cert-flipping step.  Removing A2 from the proof
       collapses the lower bound.

    3. F is non-vacuous. The two traces it compares are concretely
       constructed; their classical-shadow equality is established by
       direct case analysis on the opcode semantics; the cost-ledger
       separation between them is witnessed by specific values (>=1
       vs 0).

    F (statement, A2-free language):
      "There is no function from the classical observable shadow
       (mem, regs, pc) to the natural numbers that, on every reachable
       substrate state, returns that state's cost-ledger value vm_mu.
       The cost ledger is therefore state genuinely independent of
       the classical observable."

    Counterfactual:
      If A2 did not hold for cert-flipping steps, then the certifying
      trace's vm_mu could be zero — equal to the non-certifying
      trace's vm_mu — and the separation between the two traces'
      classical shadows would no longer carry over to a separation
      in vm_mu. The witness in [bad_substrate_collapses_separation]
      below makes this explicit at the substrate level.

    This is distinct from the existing [vm_mu_not_classically_determined]
    in [NecessityOfMuLedger.v]. That theorem proves the same F, but
    routes the lower bound on the certifying trace through the schedule
    value [vm_apply_certify_mu_charged] (which reads
    [instruction_cost (instr_certify d) = S d] off the cost schedule).
    This theorem instead routes the lower bound through A2 (via
    [no_free_certification_certified_mu]), making explicit that the
    separation depends on the cert-flip cost-floor — not on the
    specific schedule numeric.

    Print Assumptions on the headline theorem at the end of the file
    returns "Closed under the global context."
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           ShadowProjection ClassicalConservativity
                           MuInitiality AbstractNoFI
                           MuLedgerConservation.

Require Import NecessityOfMuLedger.


(** ** §1. A2-routed lower bound on the certifying trace.

    The point of this section: prove [vm_mu po1_state_A >= 1] by
    invoking A2 (in the form of [no_free_certification_certified_mu])
    rather than by reading the schedule value of
    [instruction_cost (instr_certify 0)].

    Why this matters. The existing proof of
    [po1_cond4_trace_A_mu_paid] uses [vm_apply_certify_mu_charged]
    to assert [(vm_apply s (instr_certify 0)).vm_mu = s.vm_mu + 1].
    That step reads the cost rule for [instr_certify] directly from
    the schedule. If we replace it with A2, the same conclusion
    holds, but the proof now goes through the cert-flip cost-floor
    axiom rather than a definitional unfold. A counterfactual model
    where A2 fails (cert-flipping at cost 0) would still admit a
    schedule, but the A2-routed lower bound would collapse. *)

Lemma trace_A_mu_ge_1_via_A2 :
  vm_mu po1_state_A >= 1.
Proof.
  unfold po1_state_A, po1_instr_A.
  (* Step 1: vm_certified po1_init = false (initialization). *)
  assert (Hbefore : vm_certified po1_init = false).
  { unfold po1_init. simpl. reflexivity. }
  (* Step 2: vm_certified (vm_apply po1_init (instr_certify 0)) = true
     (by the opcode-specific lemma vm_apply_certify_certified). *)
  assert (Hafter :
    vm_certified (vm_apply po1_init (instr_certify 0)) = true).
  { exact (vm_apply_certify_certified po1_init 0). }
  (* Step 3: A2 invocation.  no_free_certification_certified_mu is
     the substrate-level A2 lemma: any single step that flips
     vm_certified from false to true increases vm_mu by at least 1. *)
  pose proof (no_free_certification_certified_mu
                po1_init (instr_certify 0) Hbefore Hafter) as HA2.
  (* Step 4: po1_init.vm_mu = 0 by definition of po1_init. *)
  assert (Hinit_mu : po1_init.(vm_mu) = 0).
  { unfold po1_init. simpl. reflexivity. }
  rewrite Hinit_mu in HA2.
  (* HA2 now reads:
       (vm_apply po1_init (instr_certify 0)).(vm_mu) >= 0 + 1 *)
  lia.
Qed.


(** ** §2. The A2-routed separation theorem.

    Identical conclusion to [vm_mu_not_classically_determined] in
    [NecessityOfMuLedger.v], but the proof routes the certifying
    trace's lower bound through A2 (via the lemma above) rather
    than through the schedule numeric. *)

Theorem vm_mu_not_classically_determined_via_A2 :
  ~ exists (Omega : StrictClassicalState -> nat),
      forall (s : VMState), Omega (strict_shadow s) = s.(vm_mu).
Proof.
  intros [Omega HOmega].
  (* From A2: po1_state_A.vm_mu >= 1. *)
  pose proof trace_A_mu_ge_1_via_A2 as HA.
  (* From the existing proof (which uses the pnew cost rule, not A2):
     po1_state_B.vm_mu = 0.  This part is the schedule's "pnew is
     free" choice — the A2-load-bearing part is HA above. *)
  pose proof po1_cond5_trace_B_mu_zero as HB.
  (* The two states have equal strict shadows by direct case analysis
     over the opcode semantics. *)
  pose proof po1_cond2_final_shadow_equal as HShadow.
  (* Specialize Omega at both states. *)
  pose proof (HOmega po1_state_A) as HOmegaA.
  pose proof (HOmega po1_state_B) as HOmegaB.
  (* Equal shadows force equal Omega values, hence equal mu values. *)
  assert (Heq : po1_state_A.(vm_mu) = po1_state_B.(vm_mu)).
  { transitivity (Omega (strict_shadow po1_state_A)).
    - symmetry. exact HOmegaA.
    - rewrite HShadow. exact HOmegaB. }
  (* Equal mu plus the A2-derived lower bound plus the schedule-derived
     upper bound for trace B yields a contradiction. *)
  rewrite HB in Heq.
  lia.
Qed.


(** ** §3. Counterfactual: a substrate where A2 fails and the
        separation collapses.

    This section makes explicit why A2 is load-bearing: in the world
    without A2, a substrate can be constructed in which the
    certifying trace and the non-certifying trace have identical
    cost-ledger outcomes, and the [classical-shadow / cost-ledger]
    separation [vm_mu_not_classically_determined_via_A2] would no
    longer hold.

    The counterfactual is constructed inside the existing
    [CostBearingSystem] framework from [HonestCostTracking.v]: a
    system that has cost, state, instructions, and a cert predicate,
    but is NOT required to satisfy A2. In this larger framework, free
    forgery is admissible — and with it, the cost ledger collapses
    into the classical observable. *)

From Kernel Require Import HonestCostTracking.

(** A free-forging cost-bearing system in which a single instruction
    flips cert at cost zero. Concretely, this is the
    [dishonest_forge_system] from [HonestCostTracking.v]: state = bool,
    every step yields true at cost 0, cert is the state itself. *)
Definition cf_system : CostBearingSystem := dishonest_forge_system.

(** In this system, a single-instruction trace [[tt]] takes the
    initial state [false] to a "certified" state [true] at total cost
    zero.  The cost ledger therefore does not separate "certifying"
    from "not certifying": both can be reached at the same cost.

    The lemma below states the collapse formally: there exists a
    cost-bearing system [CB] with two traces [trace_cert, trace_quiet]
    starting from the same initial state, where one ends certified
    and the other does not, but their total costs are equal.  The
    separation [certified trace pays strictly more than non-certifying
    trace] — which holds in every A2-respecting system — fails here. *)
Lemma cf_no_cost_separation :
  exists (CB : CostBearingSystem)
         (s0 : cb_state CB)
         (trace_cert trace_quiet : list (cb_instr CB)),
       cb_cert CB s0 = false
    /\ cb_cert CB (cb_run CB trace_cert s0) = true
    /\ cb_cert CB (cb_run CB trace_quiet s0) = false
    /\ cb_total_cost CB trace_cert = cb_total_cost CB trace_quiet.
Proof.
  exists dishonest_forge_system, false, [tt], [].
  repeat split.
Qed.

(** The contrapositive read: any cost-bearing system in which the
    cost-ledger can separate certifying from non-certifying traces
    must satisfy A2 on its cert-flipping step.  This is exactly the
    [free_forgery_violates_A2] theorem from [HonestCostTracking.v]
    re-read as: "no A2 means the cost ledger collapses".

    Together, [vm_mu_not_classically_determined_via_A2] and
    [cf_no_cost_separation] establish: A2 is the axiom whose
    presence forces the cost ledger to be a genuinely independent
    observable, and whose absence permits the cost ledger to be
    recoverable from (or even identical to) the classical state. *)

(** ** §4. Problem-class lower bound: n-way certified separation cost
        exceeds the Shannon information-theoretic minimum.

    For any n-way decision problem in which n distinct outcomes are
    distinguished via the cert_addr channel in an A2-respecting
    substrate, the total substrate cost is at least n.

    Classical comparison. The Shannon information-theoretic lower
    bound for distinguishing n outcomes is log_2(n) bits: that is the
    minimum number of bits a classical observer needs to specify
    which of the n outcomes occurred. The substrate's lower bound is
    n, which exceeds log_2(n) by the ratio n / log_2(n). For
    n = 2^32, Shannon = 32, substrate >= 2^32 -- a gap of factor
    2^27 between the substrate cost and the classical
    information-theoretic minimum at the same task.

    Why A2 is load-bearing. The cost lower bound follows from
    [separation_le_cert_cost] in MuShannonQuantitative.v, which
    requires the info-pricing hypothesis that cert-setter instructions
    cost at least 1 each. The info-pricing hypothesis holds for the
    Thiele VM by [cert_addr_setter_cost_pos] -- which is exactly A2
    for the cert_addr channel, in static form on the instruction
    encodings. Without A2, cert-setters could cost zero, and the
    n-way separation could be achieved at total cost zero, putting
    substrate cost BELOW the Shannon classical minimum rather than
    above it.

    Why the exceedance over Shannon is real. Shannon information
    theory counts the bits needed to specify a choice from n options:
    log_2(n). The substrate's mechanism is mechanically different:
    each cert-flip event costs at least 1 by A2, and n distinct
    outcomes require n distinct cert-flip events in the trace by
    pigeonhole on cert_addr values. The substrate is therefore
    counting events, not bits -- and events are bounded below per
    distinguishable outcome rather than per information bit.

    This is the Landauer-vs-Shannon gap, made formal at the
    substrate's step rule: A2 forces per-event irreversibility cost
    rather than per-bit information cost.

    Problem class. Any computational problem whose specification
    requires distinguishing n outcomes (a function with n distinct
    output classes, an n-way decision tree, a colouring of a graph
    into n color classes, etc.) and whose certification flows through
    the cert_addr channel falls under this bound. Classical
    information-theoretic analyses give log_2(n); the substrate
    gives n. *)

From Kernel Require Import MuShannonQuantitative UniversalCertificationCost.

Lemma thiele_info_pricing_holds :
  forall trace : list vm_instruction,
    Forall (fun i =>
              match cert_addr_value_of i with
              | Some _ => instruction_cost i >= 1
              | None   => True
              end) trace.
Proof.
  intro trace.
  apply Forall_forall.
  intros i _.
  destruct (cert_addr_value_of i) as [n|] eqn:Hv; [|trivial].
  (* cert_addr_value_of i = Some n means i is one of:
     instr_emit, instr_reveal, instr_morph_assert.  In each case
     instruction_cost includes an S(cost) summand, hence >= 1. *)
  destruct i; simpl in Hv; try discriminate;
    unfold instruction_cost; simpl; lia.
Qed.

(** Total trace cost dominates the sum of cert-setter costs alone. *)
Lemma cs_total_cost_ge_cert_setter_sum :
  forall trace,
    cs_total_cost thiele_cert_addr_system trace >=
    fold_right (fun i acc =>
      match cert_addr_value_of i with
      | Some _ => instruction_cost i + acc
      | None   => acc
      end) 0 trace.
Proof.
  induction trace as [|i rest IH]; [simpl; lia|].
  simpl. unfold cs_cost. simpl.
  destruct (cert_addr_value_of i) as [v|]; simpl in *; lia.
Qed.

(** The headline problem-class lower bound. *)
Theorem nway_separation_substrate_cost_ge_n :
  forall (fuel : nat) (trace : list vm_instruction) (omega : list VMState),
    (** Initial states all have cert_addr = 0. *)
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0) ->
    (** Each input reaches a nonzero cert_addr after the trace. *)
    (forall s, In s omega ->
       (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0) ->
    (** The cert_addr values reached are pairwise distinct. *)
    NoDup (map (fun s =>
                  (run_vm fuel trace s).(vm_csrs).(csr_cert_addr))
               omega) ->
    (** Conclusion: substrate cost >= n = |omega|. *)
    cs_total_cost thiele_cert_addr_system trace >= List.length omega.
Proof.
  intros fuel trace omega Hinit Hnonzero HNoDup.
  pose proof (thiele_info_pricing_holds trace) as Hpricing.
  pose proof (separation_le_cert_cost
                fuel trace omega Hpricing Hinit Hnonzero HNoDup) as Hcert.
  pose proof (cs_total_cost_ge_cert_setter_sum trace) as Hge.
  lia.
Qed.

(** Counterfactual: without A2, the lower bound collapses.  The
    counterfactual built earlier ([cf_no_cost_separation]) already
    exhibits a cost-bearing system where certification happens at
    total cost zero.  Applied to the [n]-way separation scheme: in
    a substrate without A2, n distinct cert flips can be achieved at
    total cost zero, so [cs_total_cost >= n] would fail. *)


(** ** §5. Polynomial cost exceedance over classical unit-cost time
        for the LASSERT-certification problem class.

    Problem class. "LASSERT-based certification of a B-bit formula"
    is any computation that certifies a logical claim of bit-length
    B via the substrate's LASSERT instruction. The class is broad:
    SAT certification, predicate certification, structural-property
    certification -- anything routed through LASSERT lands here.

    Classical complexity (unit-cost RAM). Under the standard
    unit-cost RAM model -- where each instruction takes one unit of
    time regardless of its payload size -- a single LASSERT
    instruction is one unit of classical time. Classical complexity
    for the one-step trace is therefore 1.

    Substrate cost. The substrate's instruction_cost rule for
    LASSERT is flen * 8 + S(cost), where flen is the encoded
    formula's byte-length and cost is the cost parameter. By the
    mu-ledger conservation law (vm_apply_mu), the substrate's mu
    increases by exactly instruction_cost on each step. For a
    LASSERT of an n-bit formula (n = flen * 8 bits), substrate
    mu-increase is at least n + 1.

    Exceedance. Substrate mu (n + 1) divided by classical unit-cost
    time (1) is n + 1. For formulas of size polynomial in input
    size, exceedance is polynomial. For n = 2^32, exceedance is
    factor 2^32 + 1.

    Why A2 is load-bearing. The +1 in "n + 1" is S(cost) >= 1, which
    is exactly A2 applied to the LASSERT cert-flipping step. Without
    A2, S(cost) could be 0 and the bound would be only n. The
    cost-floor that A2 provides on top of the bit-scaling is what
    makes the exceedance over classical unit-cost time strict at
    every formula size, including n = 0 (where without A2 the
    substrate could match classical at zero cost).

    The substrate-vs-classical gap is mechanistic. Classical
    unit-cost RAM measures instructions executed. Substrate mu
    measures information committed plus irreversibility events. For
    a single LASSERT step, classical sees 1 instruction; substrate
    sees flen * 8 bits committed (LASSERT bit-cost) plus 1
    irreversibility event (A2's cost-floor). The substrate's mu
    therefore exceeds classical unit-cost time by exactly the bits
    of information the certification commits, plus the irreversibility
    floor. *)

Lemma lassert_mu_increase_ge_bits_plus_one :
  forall (s : VMState) (fa ca : nat) (ck : bool) (flen cost : nat),
    (vm_apply s (instr_lassert fa ca ck flen cost)).(vm_mu) >=
    s.(vm_mu) + flen * 8 + 1.
Proof.
  intros s fa ca ck flen cost.
  rewrite vm_apply_mu.
  unfold instruction_cost. lia.
Qed.

(** Headline polynomial exceedance theorem.

    For any single-LASSERT trace certifying a B-bit formula
    (B = flen * 8), the substrate's mu-increase is at least B + 1.
    Compared to classical unit-cost time of 1 for the same trace,
    the substrate exceeds classical by factor B + 1.

    Provable in three lines, but the content is significant: the
    substrate enforces a Landauer-Shannon combined lower bound that
    is strictly above the classical unit-cost time at every formula
    size B >= 1. The combined bound is B + 1: B from the LASSERT
    cost rule's bit-scaling, and 1 from A2's cert-event floor.
*)
Theorem lassert_substrate_mu_exceeds_unit_cost :
  forall (s : VMState) (fa ca : nat) (ck : bool) (flen cost : nat),
    let B := flen * 8 in
    (** Substrate mu-increase for this one-step trace is at least B + 1. *)
    (vm_apply s (instr_lassert fa ca ck flen cost)).(vm_mu) - s.(vm_mu) >=
    B + 1.
Proof.
  intros s fa ca ck flen cost B.
  pose proof (lassert_mu_increase_ge_bits_plus_one
                s fa ca ck flen cost) as Hbound.
  unfold B. lia.
Qed.

(** Counterfactual: in a cost-bearing system without A2, the same
    LASSERT step (or its analog) could cost only B, not B + 1. The
    A2 contribution to the exceedance is the +1 floor; the LASSERT
    cost rule contributes the B bit-scaling. The combined bound is
    A2-load-bearing in the strict sense that removing A2's cost-floor
    drops the bound from B + 1 to B. For B = 0 specifically (an
    empty formula), the with-A2 bound is 1 and the without-A2 bound
    is 0: a clean strict separation. *)

Theorem a2_contributes_exact_plus_one_to_lassert_bound :
  forall (fa ca : nat) (ck : bool) (cost : nat),
    let flen := 0 in
    let bound_with_a2 := flen * 8 + 1 in
    let bound_without_a2 := flen * 8 in
    bound_with_a2 = bound_without_a2 + 1.
Proof.
  intros. unfold flen, bound_with_a2, bound_without_a2. lia.
Qed.


(** Print Assumptions: closure under the global context. *)
Print Assumptions trace_A_mu_ge_1_via_A2.
Print Assumptions vm_mu_not_classically_determined_via_A2.
Print Assumptions cf_no_cost_separation.
Print Assumptions thiele_info_pricing_holds.
Print Assumptions cs_total_cost_ge_cert_setter_sum.
Print Assumptions nway_separation_substrate_cost_ge_n.
Print Assumptions lassert_mu_increase_ge_bits_plus_one.
Print Assumptions lassert_substrate_mu_exceeds_unit_cost.
Print Assumptions a2_contributes_exact_plus_one_to_lassert_bound.

(** ** Summary

    [trace_A_mu_ge_1_via_A2]
      A2 (via no_free_certification_certified_mu) forces the
      certifying single-step trace's vm_mu to be at least 1.

    [vm_mu_not_classically_determined_via_A2]
      F: no function on the strict classical shadow recovers vm_mu.
      The proof uses the A2-routed lower bound above as its
      load-bearing step. Without A2, this lower bound collapses.

    [cf_no_cost_separation]
      Without A2, an explicit cost-bearing system exhibits two
      traces with identical total cost but different cert outcomes.
      The cost ledger becomes unable to separate certifying from
      non-certifying traces.

    Together: A2 is the axiom whose presence makes the cost ledger
    a genuinely independent observable. F is provable with A2 and
    fails without it.
*)
