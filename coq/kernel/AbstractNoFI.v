(** AbstractNoFI: No Free Insight for the abstract cert machine

    The No Free Insight theorem is not a quirk of the Thiele VM's implementation.
    It is a theorem about any machine that processes this vm_instruction
    vocabulary and satisfies four properties:

      A1. The system has a state that includes a certification indicator.
      A2. The certification indicator starts unset.
      A3. Cert-setter instructions are the ONLY instructions that can SET the
          certification indicator (non-cert-setters preserve it exactly).
      A4. Every cert-setter instruction has cost ≥ 1 (no free certification).

    CONSEQUENCE:
    Any execution from an uncertified state to a certified state MUST contain
    at least one cert-setter instruction AND must have spent ≥ 1 unit of cost.

    THE THIELE VM IS AN INSTANCE:
    We prove that the Thiele VM satisfies A1–A4, so all consequences apply.
    A machine that does not satisfy A1–A4 is outside this theorem. It may be
    doing something interesting, but it is not doing this honest cert-accounting
    discipline. A machine that does satisfy A1–A4 is covered by this proof.

*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof RevelationRequirement
                           MuLedgerConservation PrimeAxiom.

Import RevelationProof.

(** The Abstract Machine Model

    I parameterize over the state type S but fix the instruction set to
    vm_instruction. This is the right generalization: the universality is
    about machines processing the SAME instruction vocabulary with different
    internal state representations.

    Any machine that processes vm_instructions must, if it implements honest
    cert accounting (A3), satisfy NoFI.
*)

(** cert_addr_setterb: the instructions that can SET csr_cert_addr.

    IMPORTANT DISTINCTION from is_cert_setterb:
    - is_cert_setterb includes instr_read_port and instr_certify
    - instr_read_port does NOT set csr_cert_addr (see step_read_port: uses s.(vm_csrs) unchanged)
    - instr_certify sets vm_certified but NOT csr_cert_addr (see step_certify)
    - has_supra_cert checks csr_cert_addr ≠ 0, not vm_certified

    cert_addr_setterb is the PRECISE predicate for "can set csr_cert_addr."
*)
Definition cert_addr_setterb (i : vm_instruction) : bool :=
  match i with
  | instr_reveal _ _ _ _ => true
  | instr_emit _ _ _ => true
  | instr_ljoin _ _ _ => true
  | instr_lassert _ _ _ _ _ => true
  | instr_morph_assert _ _ _ _ => true
  | _ => false
  end.

(** cost_of: the μ-cost charged by an instruction in the Thiele VM. *)
Definition cost_of (i : vm_instruction) : nat := instruction_cost i.

(** AbstractCertMachine: any machine that processes vm_instructions with:
    - A state type S (parameterized)
    - A step function acm_step: S → vm_instruction → S
    - A boolean cert indicator acm_cert: S → bool
    - Field acm_preserve: non-cert-setters preserve the cert indicator
      (this is the formal statement of "cert can only be SET by cert-setters")
*)
Record AbstractCertMachine (S : Type) := {
  acm_step    : S -> vm_instruction -> S;
  acm_cert    : S -> bool;
  (** A3: Only cert-setters can change cert from false to true *)
  acm_preserve : forall (s : S) (i : vm_instruction),
    acm_cert s = false ->
    cert_addr_setterb i = false ->
    acm_cert (acm_step s i) = false
}.

Arguments acm_step    {S} _ _.
Arguments acm_cert    {S} _ _.
Arguments acm_preserve {S} _ _ _ _ _.

(** Sequential execution of a trace on an abstract machine.
    Note: this is NOT PC-indexed; it executes instructions in list order.
    The universality theorem holds for this list-order model. The PC-indexed
    Thiele VM connection is proven separately below. *)
Fixpoint acm_run {S : Type} (M : AbstractCertMachine S)
                  (trace : list vm_instruction) (s : S) : S :=
  match trace with
  | []       => s
  | i :: rest => acm_run M rest (acm_step M s i)
  end.

(** The Universality Theorem

    THEOREM (abstract_nfi):
    For any abstract cert machine M satisfying A3,
    if execution starts uncertified and ends certified,
    then the trace contains at least one cert-setter instruction.

    PROOF: Induction on the trace.
    - Base: empty trace → cert stays false → contradicts certified at end.
    - Step: if first instruction IS a cert-setter, done.
            if first instruction is NOT a cert-setter, by A3 cert stays false
            after it, so the rest of the trace must contain a cert-setter (IH).
*)

Theorem abstract_nfi :
  forall (S : Type) (M : AbstractCertMachine S)
         (trace : list vm_instruction) (s0 : S),
    acm_cert M s0 = false ->
    acm_cert M (acm_run M trace s0) = true ->
    exists i, In i trace /\ cert_addr_setterb i = true.
Proof.
  intros S M trace.
  induction trace as [| i rest IH].
  - (* Empty trace: cert must stay false. Contradicts hypothesis. *)
    intros s0 Hfalse Htrue.
    simpl in Htrue.
    rewrite Hfalse in Htrue.
    discriminate.
  - (* Nonempty trace: check if i is a cert-setter *)
    intros s0 Hfalse Htrue.
    simpl in Htrue.
    destruct (cert_addr_setterb i) eqn:Hi.
    + (* i is a cert-setter: witness found immediately *)
      exists i. split.
      { left. reflexivity. }
      { exact Hi. }
    + (* i is NOT a cert-setter: by A3, cert stays false after i *)
      assert (Hstep_false : acm_cert M (acm_step M s0 i) = false).
      { apply (acm_preserve M s0 i Hfalse Hi). }
      (* By IH, the rest of the trace must contain a cert-setter *)
      destruct (IH (acm_step M s0 i) Hstep_false Htrue) as [j [Hj_in Hj_cert]].
      exists j. split.
      { right. exact Hj_in. }
      { exact Hj_cert. }
Qed.

(** COROLLARY (abstract_nfi_in_trace): same theorem, stated as list membership *)
Corollary abstract_nfi_in_trace :
  forall (S : Type) (M : AbstractCertMachine S)
         (trace : list vm_instruction) (s0 : S),
    acm_cert M s0 = false ->
    acm_cert M (acm_run M trace s0) = true ->
    ~ Forall (fun i => cert_addr_setterb i = false) trace.
Proof.
  intros S M trace s0 Hfalse Htrue Hforall.
  apply abstract_nfi in Htrue; [| exact Hfalse].
  destruct Htrue as [i [Hin Hi_cert]].
  rewrite Forall_forall in Hforall.
  apply Hforall in Hin.
  rewrite Hin in Hi_cert.
  discriminate.
Qed.

(** Cost Bound

    A4 (formal): Every cert-setter has cost ≥ 1.

    This is the "no free" part: not only must there BE a cert-setter,
    but that cert-setter MUST have spent ≥ 1 unit of μ-cost.

    PROOF: By case analysis on all cert-setter constructors.
    Each uses S(cost) as its instruction_cost, so cost ≥ 1 by construction.
*)

Lemma cert_addr_setter_cost_pos :
  forall i,
    cert_addr_setterb i = true ->
    cost_of i >= 1.
Proof.
  intros i Hi.
  unfold cost_of, instruction_cost.
  destruct i; simpl in Hi; try discriminate; lia.
Qed.

(** The Thiele VM Is An Instance

    I prove the Thiele VM satisfies axiom A3 with cert = has_supra_cert.
    That is: non-cert-addr-setters preserve csr_cert_addr exactly.

    The key lemma bridges cert_addr_setterb = false to the 5 ≠-premises
    that non_cert_setter_preserves_cert requires.
*)

(** thiele_non_cert_addr_setter_preserves :
    If cert_addr_setterb i = false, then vm_apply preserves csr_cert_addr.

    PROOF NOTE: non_cert_setter_preserves_cert from RevelationRequirement.v
    takes a premise (forall mu, i <> instr_certify mu). But instr_certify is
    NOT in cert_addr_setterb (it sets vm_certified, not csr_cert_addr), so
    we handle it as a special case before calling non_cert_setter_preserves_cert.
*)
Lemma thiele_non_cert_addr_setter_preserves :
  forall (s : VMState) (i : vm_instruction),
    cert_addr_setterb i = false ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s i Hi.
  (* Split on whether i is instr_certify or something else.
     instr_certify preserves csr_cert_addr (uses vm_csrs := s.(vm_csrs)).
     non_cert_setter_preserves_cert asks us to exclude it, so handle it here. *)
  assert (is_certify_or_not : (exists mu, i = instr_certify mu) \/
                               (forall mu, i <> instr_certify mu)).
  { destruct i; try (right; intros mu H; discriminate H).
    left; eauto. }
  destruct is_certify_or_not as [[mu Hceq] | Hne_cert].
  - (* i = instr_certify mu: step_certify uses vm_csrs := s.(vm_csrs) *)
    subst i.
    unfold vm_apply.
    simpl.
    reflexivity.
  - (* i ≠ instr_certify: the 5 cert-addr-setters are excluded by Hi *)
    apply non_cert_setter_preserves_cert.
    + intros m b c mu H. rewrite H in Hi. simpl in Hi. discriminate.
    + intros m p mu H.   rewrite H in Hi. simpl in Hi. discriminate.
    + intros c1 c2 mu H. rewrite H in Hi. simpl in Hi. discriminate.
    + intros fa ca k fl mu H. rewrite H in Hi. simpl in Hi. discriminate.
    + exact Hne_cert.
    + intros mid p c mu H. rewrite H in Hi. simpl in Hi. discriminate.
Qed.

(** thiele_cert_bool: the Thiele VM's cert indicator as a bool *)
Definition thiele_cert_bool (s : VMState) : bool :=
  negb (Nat.eqb (s.(vm_csrs).(csr_cert_addr)) 0).

Lemma thiele_cert_bool_zero_iff :
  forall s,
    thiele_cert_bool s = false <->
    s.(vm_csrs).(csr_cert_addr) = 0.
Proof.
  intros s.
  unfold thiele_cert_bool.
  rewrite Bool.negb_false_iff.
  rewrite Nat.eqb_eq.
  reflexivity.
Qed.

Lemma thiele_cert_bool_nonzero_iff :
  forall s,
    thiele_cert_bool s = true <->
    s.(vm_csrs).(csr_cert_addr) <> 0.
Proof.
  intros s.
  unfold thiele_cert_bool.
  rewrite Bool.negb_true_iff.
  rewrite Nat.eqb_neq.
  reflexivity.
Qed.

(** thiele_vm_axiom_A3: the Thiele VM satisfies A3 with thiele_cert_bool *)
Lemma thiele_vm_axiom_A3 :
  forall (s : VMState) (i : vm_instruction),
    thiele_cert_bool s = false ->
    cert_addr_setterb i = false ->
    thiele_cert_bool (vm_apply s i) = false.
Proof.
  intros s i Hfalse Hi.
  rewrite thiele_cert_bool_zero_iff in *.
  rewrite (thiele_non_cert_addr_setter_preserves s i Hi).
  exact Hfalse.
Qed.

(** The Thiele VM as an AbstractCertMachine *)
Definition thiele_cert_machine : AbstractCertMachine VMState :=
  {| acm_step    := vm_apply;
     acm_cert    := thiele_cert_bool;
     acm_preserve := thiele_vm_axiom_A3 |}.

(** Consequences For The Thiele VM

    We now derive the NoFI consequences for the Thiele VM specifically.
    These connect the abstract universality theorem to the concrete VM.
*)

(** thiele_abstract_nfi: NoFI for Thiele VM in sequential (list) execution model.
    Starting from csr_cert_addr = 0, reaching cert_addr ≠ 0 requires
    a cert-setter instruction in the trace. *)
Theorem thiele_abstract_nfi :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    exists i, In i trace /\ cert_addr_setterb i = true.
Proof.
  intros trace s0 Hzero Hnonzero.
  apply (abstract_nfi VMState thiele_cert_machine trace s0).
  - rewrite thiele_cert_bool_zero_iff. exact Hzero.
  - rewrite thiele_cert_bool_nonzero_iff. exact Hnonzero.
Qed.

(** thiele_abstract_nfi_cost: Any cert-setter in the trace costs ≥ 1 μ. *)
Theorem thiele_abstract_nfi_cost :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    exists i, In i trace /\ cert_addr_setterb i = true /\ cost_of i >= 1.
Proof.
  intros trace s0 Hzero Hnonzero.
  apply thiele_abstract_nfi in Hnonzero; [| exact Hzero].
  destruct Hnonzero as [i [Hin Hi_cert]].
  exists i. split.
  { exact Hin. }
  split.
  { exact Hi_cert. }
  { apply cert_addr_setter_cost_pos. exact Hi_cert. }
Qed.

(** PC-Indexed Connection Helpers *)

(** uses_revelation_has_reveal: uses_revelation trace → ∃ reveal in trace *)
Lemma uses_revelation_has_reveal :
  forall (trace : list vm_instruction),
    uses_revelation trace ->
    exists i, In i trace /\ cert_addr_setterb i = true.
Proof.
  induction trace as [| i rest IH].
  - simpl. intro H. destruct H.
  - intro Hrev.
    (* Destruct first, then simplify Hrev per-branch *)
    destruct i; cbn [uses_revelation] in Hrev;
    (* Non-reveal: Hrev : uses_revelation rest, so apply IH. *)
    try ( apply IH in Hrev;
          destruct Hrev as [w [Hw_in Hw_cert]];
          exists w; split; [ right; exact Hw_in | exact Hw_cert ] );
    (* instr_reveal: Hrev : True, so the head is the witness. *)
    ( eexists; split; [ left; reflexivity | simpl; reflexivity ] ).
Qed.

(** Connection To PC-Indexed Execution

    The above theorems use sequential (list-order) execution.
    The Thiele VM uses PC-indexed execution (run_vm).
    We connect them via the existing nonlocal_correlation_requires_revelation,
    which proves the same property for PC-indexed execution.

    THEOREM (thiele_nfi_pc_indexed): For PC-indexed execution,
    starting from cert_addr = 0 and ending with cert_addr ≠ 0,
    the trace must contain a cert-setter (REVEAL/EMIT/LJOIN/LASSERT/MORPH_ASSERT).
    This is exactly nonlocal_correlation_requires_revelation from
    RevelationRequirement.v, restated in our vocabulary.
*)

Theorem thiele_nfi_pc_indexed :
  forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
    trace_run fuel trace s_init = Some s_final ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    s_final.(vm_csrs).(csr_cert_addr) <> 0 ->
    exists i, In i trace /\ cert_addr_setterb i = true.
Proof.
  intros trace s_init s_final fuel Hrun Hzero Hnonzero.
  (* has_supra_cert s_final holds because cert_addr ≠ 0 *)
  assert (Hsupra : has_supra_cert s_final).
  { unfold has_supra_cert. exact Hnonzero. }
  (* Apply the core kernel theorem *)
  apply nonlocal_correlation_requires_revelation
    with (s_init := s_init) (s_final := s_final) (fuel := fuel)
    in Hrun; [| exact Hzero | exact Hsupra].
  (* Translate the disjunction into our cert_addr_setterb vocabulary *)
  destruct Hrun as [Hrev | [Hemit | [Hljoin | [Hlassert | Hmorph]]]].
  - (* uses_revelation: contains an instr_reveal → use helper *)
    exact (uses_revelation_has_reveal trace Hrev).
  - (* instr_emit in trace *)
    destruct Hemit as [n [m [p [mu Hnth]]]].
    apply nth_error_In in Hnth.
    exists (instr_emit m p mu). split.
    { exact Hnth. }
    { simpl. reflexivity. }
  - (* instr_ljoin in trace *)
    destruct Hljoin as [n [c1 [c2 [mu Hnth]]]].
    apply nth_error_In in Hnth.
    exists (instr_ljoin c1 c2 mu). split.
    { exact Hnth. }
    { simpl. reflexivity. }
  - (* instr_lassert in trace (new ISA: formula_addr_reg cert_addr_reg cert_kind formula_len mu_delta) *)
    destruct Hlassert as [n [fa [ca [k [fl [mu Hnth]]]]]].
    apply nth_error_In in Hnth.
    exists (instr_lassert fa ca k fl mu). split.
    { exact Hnth. }
    { simpl. reflexivity. }
  - (* instr_morph_assert in trace *)
    destruct Hmorph as [n [mid [p [c [mu Hnth]]]]].
    apply nth_error_In in Hnth.
    exists (instr_morph_assert mid p c mu). split.
    { exact Hnth. }
    { simpl. reflexivity. }
Qed.

(** The Complete Statement

    THEOREM (universal_nfi): The complete No Free Insight universality claim.

    FOR ANY MACHINE M satisfying A3 (cert preserved by non-cert-setters),
    executing any trace from an uncertified state to a certified state
    requires a cert-setter instruction, and that instruction costs ≥ 1.

    THE THIELE VM SATISFIES THIS: proven above (thiele_cert_machine).
    ANY OTHER MACHINE satisfying A3 also satisfies this: proven by abstract_nfi.

    This is the formal meaning of "No other machine in this model can bypass NoFI":
    any machine that processes vm_instructions with honest cert accounting
    (= satisfies A3) is subject to this theorem. A machine that does NOT
    satisfy A3 is not doing honest cert accounting. It allows free forgery,
    which is exactly the property we are proving cannot happen here.
*)

Theorem universal_nfi :
  forall (S : Type) (M : AbstractCertMachine S)
         (trace : list vm_instruction) (s0 : S),
    (* Precondition: start uncertified *)
    acm_cert M s0 = false ->
    (* Postcondition: end certified *)
    acm_cert M (acm_run M trace s0) = true ->
    (* Then: trace contains a cert-setter with cost ≥ 1 *)
    exists i, In i trace /\
              cert_addr_setterb i = true /\
              cost_of i >= 1.
Proof.
  intros S M trace s0 Hfalse Htrue.
  apply abstract_nfi in Htrue; [| exact Hfalse].
  destruct Htrue as [i [Hin Hi_cert]].
  exists i. split.
  { exact Hin. }
  split.
  { exact Hi_cert. }
  { apply cert_addr_setter_cost_pos. exact Hi_cert. }
Qed.

(** The Structural Lower Bound

    THE GAP-CLOSING THEOREM.

    The challenge: is the cost lower bound for cert-setters forced by the
    machine's structure, or is it an arbitrary design choice baked into
    instruction_cost with S(cost)?

    ANSWER: It is structurally forced. Here is the derivation chain:

      (1) Observe: cert_addr changed (0 → nonzero) in one vm_apply step.
      (2) By contrapositive of thiele_non_cert_addr_setter_preserves:
            cert_addr_setterb i = true
          [STRUCTURAL: which instructions can alter csr_cert_addr, proven
           by case analysis over the vm_instruction constructors]
      (3) By cert_addr_setter_cost_pos:
            instruction_cost i ≥ 1
          [DEFINITIONAL: the 5 cert-addr-setters all use S(cost)]
      (4) By vm_apply_mu (MuLedgerConservation):
            (vm_apply s i).(vm_mu) = s.(vm_mu) + instruction_cost i ≥ s.(vm_mu) + 1
          [CONSERVATION: μ exactly tracks cumulative instruction_cost]

    WHY THIS IS NON-CIRCULAR:
    The lower bound is derived from OBSERVATION OF STATE CHANGE, not from
    reading the cost definition. Step (2) is the structural pivot: we observe
    cert_addr changed, and from that alone (using the preservation lemma,
    which is proven by case analysis over the vm_instruction constructors)
    we conclude the instruction must be a cert-setter.

    The cost bound in step (3) then follows from the structural definition
    of cert-setters. The chain cert_addr-change → cert_addr_setterb → cost ≥ 1
    is the non-arbitrary core: any instruction set where cert_addr can be
    set by a zero-cost instruction would violate this structural guarantee.
*)

(** no_free_certification: the structural lower bound.
    A single vm_apply step that moves cert_addr from 0 to nonzero
    must have instruction_cost ≥ 1.
    This is proven by structural observation of state change, not
    by reading the cost definition directly. *)
Theorem no_free_certification :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_csrs).(csr_cert_addr) = 0 ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) <> 0 ->
    instruction_cost i >= 1.
Proof.
  intros s i Hbefore Hafter.
  (* Step (2): The instruction must be a cert_addr_setter.
     If it were not, thiele_non_cert_addr_setter_preserves would give
     cert_addr unchanged = 0, contradicting Hafter. *)
  assert (Hsetter : cert_addr_setterb i = true).
  { destruct (cert_addr_setterb i) eqn:Hb.
    - reflexivity.
    - exfalso. apply Hafter.
      rewrite <- Hbefore.
      exact (thiele_non_cert_addr_setter_preserves s i Hb). }
  (* Step (3): cert-setters always cost ≥ 1 *)
  exact (cert_addr_setter_cost_pos i Hsetter).
Qed.

(** no_free_certification_mu: the μ-level corollary.
    If cert_addr changes from 0 to nonzero in one step, then μ increased by ≥ 1.
    Connects the structural lower bound to the monotone cost ledger (μ-conservation). *)
Corollary no_free_certification_mu :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_csrs).(csr_cert_addr) = 0 ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) <> 0 ->
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i Hbefore Hafter.
  rewrite vm_apply_mu.
  pose proof (no_free_certification s i Hbefore Hafter).
  lia.
Qed.

(** Trace-Level Structural Lower Bound

    Extends the single-step theorem to SEQUENCES of instructions.
    If cert_addr changes from 0 to nonzero anywhere over a trace,
    then total μ growth across the trace is at least 1.

    This closes the "smuggling through a sequence" objection:
    no finite sequence of zero-cost instructions can produce cert_addr ≠ 0.
*)

(** trace_mu_delta: the total μ cost of running a trace.
    By vm_apply_mu, each step contributes exactly instruction_cost i.
    So trace_mu_delta is the exact net μ increase from running the trace. *)
Fixpoint trace_mu_delta (trace : list vm_instruction) : nat :=
  match trace with
  | []        => 0
  | i :: rest => instruction_cost i + trace_mu_delta rest
  end.

(** acm_run_mu_exact: μ after running a trace equals initial μ plus trace cost.
    Uses vm_apply_mu (MuLedgerConservation) at each step. *)
Lemma acm_run_mu_exact :
  forall (trace : list vm_instruction) (s : VMState),
    (acm_run thiele_cert_machine trace s).(vm_mu) =
    s.(vm_mu) + trace_mu_delta trace.
Proof.
  induction trace as [| i rest IH]; intros s.
  - simpl. lia.
  - (* acm_run M (i::rest) s = acm_run M rest (vm_apply s i) since
       acm_step thiele_cert_machine = vm_apply by definition *)
    change (acm_run thiele_cert_machine (i :: rest) s) with
           (acm_run thiele_cert_machine rest (vm_apply s i)).
    rewrite (IH (vm_apply s i)).
    rewrite vm_apply_mu.
    simpl. lia.
Qed.

(** In_cert_setter_trace_cost_ge: if trace contains a cert-setter, then
    trace_mu_delta ≥ 1. The cert-setter's cost (≥ 1) contributes to the sum. *)
Lemma In_cert_setter_trace_cost_ge :
  forall (trace : list vm_instruction) (i : vm_instruction),
    In i trace ->
    cert_addr_setterb i = true ->
    trace_mu_delta trace >= 1.
Proof.
  induction trace as [| j rest IH]; intros i Hin Hi_cert.
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hrest].
    + subst j. simpl.
      pose proof (cert_addr_setter_cost_pos i Hi_cert).
      unfold cost_of in *. lia.
    + simpl. specialize (IH i Hrest Hi_cert). lia.
Qed.

(** no_free_certification_trace_mu: THE TRACE-LEVEL LOWER BOUND.
    If cert_addr is absent at s0 and present after running a full trace,
    then μ grew by ≥ 1 over the entire trace.

    This is strictly stronger than the single-step version:
    it covers ANY finite sequence. No "smuggling through a sequence" loophole.
*)
Theorem no_free_certification_trace_mu :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    (acm_run thiele_cert_machine trace s0).(vm_mu) >= s0.(vm_mu) + 1.
Proof.
  intros trace s0 Hzero Hnonzero.
  (* By thiele_abstract_nfi_cost: trace contains cert-setter with cert_addr_setterb = true *)
  destruct (thiele_abstract_nfi_cost trace s0 Hzero Hnonzero) as [i [Hin [Hi_cert _]]].
  (* By acm_run_mu_exact: final mu = initial mu + trace_mu_delta *)
  rewrite acm_run_mu_exact.
  (* Suffices: trace_mu_delta trace ≥ 1 *)
  apply Nat.add_le_mono_l.
  exact (In_cert_setter_trace_cost_ge trace i Hin Hi_cert).
Qed.

(** The vm_certified Channel

    The machine has two distinct certification channels:
    (A) csr_cert_addr ≠ 0: structural evidence from revelation/assertion ops
    (B) vm_certified = true: direct certification flag from CERTIFY opcode

    Both are non-free. This section proves the cost lower bound for channel B.

    Key structural fact (from PrimeAxiom.vm_apply_certified):
      (vm_apply s i).vm_certified = match i with
        | instr_certify n => true | _ => s.vm_certified end

    Therefore: if vm_certified went false → true, then i = instr_certify n for
    some n, and instruction_cost (instr_certify n) = S n ≥ 1.
*)

(** no_free_certification_certified: structural lower bound for the vm_certified channel.
    If vm_certified changes false→true in one step, the instruction cost is ≥ 1.
    Proof follows from vm_apply_certified: only instr_certify can set this flag. *)
Theorem no_free_certification_certified :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_certified) = false ->
    (vm_apply s i).(vm_certified) = true ->
    instruction_cost i >= 1.
Proof.
  intros s i Hbefore Hafter.
  rewrite vm_apply_certified in Hafter.
  (* vm_apply_certified: result is (match i with | instr_certify _ => true | _ => s.vm_certified end) *)
  destruct i; simpl in Hafter;
    (* For all non-certify: Hafter : s.vm_certified = true; contradicts Hbefore *)
    try (rewrite Hbefore in Hafter; discriminate).
  (* Only instr_certify n remains: instruction_cost (instr_certify n) = S n ≥ 1 *)
  unfold instruction_cost. simpl. lia.
Qed.

(** no_free_certification_certified_mu: μ-level corollary for vm_certified channel. *)
Corollary no_free_certification_certified_mu :
  forall (s : VMState) (i : vm_instruction),
    s.(vm_certified) = false ->
    (vm_apply s i).(vm_certified) = true ->
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i Hbefore Hafter.
  rewrite vm_apply_mu.
  pose proof (no_free_certification_certified s i Hbefore Hafter).
  lia.
Qed.

(** The Master Theorem

    Packages both certification channels into a single canonical statement.

    CLAIM TIER: KERNEL / PROVEN
    DEPENDS ON: no_free_certification_mu and no_free_certification_certified_mu
    WHAT IT PROVES: Neither cert channel can activate for free (in one step)
    WHAT IT DOES NOT PROVE: Cost is tight / exact; trace-level composition;
      that "insight" in the broad sense always costs ≥ 1

    CHANNEL TAXONOMY:
      csr_cert_addr ≠ 0  ↔  has_supra_cert  ↔  supra_cert in Python
        Set by: REVEAL, EMIT, LJOIN, LASSERT, MORPH_ASSERT (all use S cost)
      vm_certified = true
        Set by: CERTIFY (uses S cost)
      vm_witness counters: NOT a cert channel; set by CHSH_TRIAL without S cost
        (witness counters are observational data, not authorization tokens)
*)
Theorem certification_requires_positive_mu :
  forall (s : VMState) (i : vm_instruction),
    (** Channel A absent: csr_cert_addr was 0 and is now nonzero *)
    (s.(vm_csrs).(csr_cert_addr) = 0 /\
     (vm_apply s i).(vm_csrs).(csr_cert_addr) <> 0)
    \/
    (** Channel B absent: vm_certified was false and is now true *)
    (s.(vm_certified) = false /\
     (vm_apply s i).(vm_certified) = true)
    ->
    (** Conclusion: μ strictly increased by at least 1 *)
    (vm_apply s i).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros s i [[Haddr_before Haddr_after] | [Hcert_before Hcert_after]].
  - exact (no_free_certification_mu s i Haddr_before Haddr_after).
  - exact (no_free_certification_certified_mu s i Hcert_before Hcert_after).
Qed.
