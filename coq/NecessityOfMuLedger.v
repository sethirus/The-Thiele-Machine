(** NecessityOfMuLedger.v — Proof Obligation 1: Formal Necessity of the μ-Ledger

    PROOF BY CONTRADICTION (Seven Conditions)

    We construct two computation traces, Trace A and Trace B, satisfying all
    seven conditions of Proof Obligation 1.  From conditions (1)–(2) we derive
    that P(State_A(final)) = P(State_B(final)) for the strict classical shadow P.
    From conditions (4)–(5) we derive contradictory μ-ledger and certification
    outcomes.  Any classical observer Ω on the strict shadow must therefore
    return incompatible structural receipts for the same input — a contradiction.

    This proves: no function of the strict classical state (mem, regs, pc) can
    determine either the μ-ledger balance or the certification status of a
    Thiele Machine execution.  The μ-ledger and vm_certified flag are the sole
    records of earned structural entitlement; their omission renders the
    computational model formally incomplete with respect to certification.

    SEVEN CONDITIONS (per Proof Obligation 1):
      (1) Identical starting classical state: po1_init
      (2) Identical strict shadow at every step: proved in §4
      (3) Identical classical resource footprint (trace length 1): proved in §4
      (4) Trace A certifies and pays μ=1
      (5) Trace B does not certify and remains at μ=0
      (6) A classically-definable observer Ω : StrictClassicalState → A
      (7) Contradiction: any Ω that predicts certification or μ returns
          incompatible outputs for the same strict classical input.

    WITNESS PROGRAMS:
      Trace A: [instr_certify 0]
        Advances PC by 1, sets vm_certified := true, charges μ += 1.
        Preserves vm_mem and vm_regs exactly.

      Trace B: [instr_pnew [] 0]
        Advances PC by 1, preserves vm_certified (stays false), charges μ += 0.
        Preserves vm_mem and vm_regs exactly.
        Modifies only vm_graph (creates a new empty partition module) —
        invisible to the strict classical shadow.

    The programs are different — they diverge in the structural layer — but
    their strict classical traces (mem, regs, pc at each step) are provably
    identical.  The divergence lives entirely in vm_certified, vm_mu, and
    vm_graph, which no function of (mem, regs, pc) can observe.

    KEY COST DISTINCTION:
      instruction_cost (instr_certify 0) = S 0 = 1   (S-floor guaranteed)
      instruction_cost (instr_pnew [] 0) = 0          (no S-floor for pnew)

    This means Trace A must pay to certify; Trace B pays nothing and cannot
    certify.  The μ-ledger is the accounting system that records this payment.

    STRUCTURE:
      §1  Strict Classical Shadow definition
      §2  Helper lemmas for advance_state fields
      §3  Witness state definitions (po1_init, po1_state_A, po1_state_B)
      §4  The Seven Conditions
      §5  The Necessity Theorem and corollaries
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           ShadowProjection ClassicalConservativity
                           MuInitiality.


(** ** §1. Strict classical shadow

    The [ClassicalState] defined in [ShadowProjection.v] includes
    [vm_mu] and [vm_certified]. For this proof we need the strictly
    Turing-classical shadow: just [(mem, regs, pc)], matching what any
    RAM or Turing machine can observe. There is no μ-ledger, no
    certification flag, and no partition graph. *)

Record StrictClassicalState := mk_strict_classical {
  scs_mem  : list nat;
  scs_regs : list nat;
  scs_pc   : nat
}.

(** strict_shadow: total projection onto the Turing-classical observable.
    Forgets: vm_mu, vm_certified, vm_graph, vm_csrs, vm_witness,
             vm_mstatus, vm_mu_tensor, vm_err, vm_logic_acc. *)
Definition strict_shadow (s : VMState) : StrictClassicalState := {|
  scs_mem  := s.(vm_mem);
  scs_regs := s.(vm_regs);
  scs_pc   := s.(vm_pc)
|}.

(** Two states are strictly shadow-equal when all three classical fields agree. *)
Definition strict_shadow_equal (s1 s2 : VMState) : Prop :=
  strict_shadow s1 = strict_shadow s2.

Lemma strict_shadow_equal_iff :
  forall s1 s2,
    strict_shadow_equal s1 s2 <->
    s1.(vm_mem) = s2.(vm_mem) /\
    s1.(vm_regs) = s2.(vm_regs) /\
    s1.(vm_pc) = s2.(vm_pc).
Proof.
  intros s1 s2. split.
  - intro H. unfold strict_shadow_equal, strict_shadow in H.
    injection H. intros Hpc Hregs Hmem. repeat split; assumption.
  - intros [Hmem [Hregs Hpc]].
    unfold strict_shadow_equal, strict_shadow.
    f_equal; assumption.
Qed.

(** Any function of strict classical state gives equal results on
    strictly-shadow-equal states.  This is the core functional consequence. *)
Lemma strict_shadow_functional :
  forall {A : Type} (f : StrictClassicalState -> A) (s1 s2 : VMState),
    strict_shadow_equal s1 s2 ->
    f (strict_shadow s1) = f (strict_shadow s2).
Proof.
  intros A f s1 s2 Heq.
  unfold strict_shadow_equal in Heq.
  rewrite Heq. reflexivity.
Qed.


(** ** §2. Helper lemmas for [advance_state] fields

    [advance_state] is the state builder for structural instructions
    (PNEW, PSPLIT, PMERGE, EMIT, …). Its [vm_mem], [vm_regs], [vm_pc],
    and [vm_certified] fields are determined solely by the source
    state [s]; they do not depend on the [graph'] argument. The
    lemmas below expose this so PNEW steps can be reasoned about
    without evaluating [graph_add_module]. *)

Lemma advance_state_mem_eq :
  forall s i g c e, (advance_state s i g c e).(vm_mem) = s.(vm_mem).
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

Lemma advance_state_regs_eq :
  forall s i g c e, (advance_state s i g c e).(vm_regs) = s.(vm_regs).
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

Lemma advance_state_pc_eq :
  forall s i g c e, (advance_state s i g c e).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

Lemma advance_state_certified_eq :
  forall s i g c e, (advance_state s i g c e).(vm_certified) = s.(vm_certified).
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

Lemma advance_state_mu_eq :
  forall s i g c e, (advance_state s i g c e).(vm_mu) = apply_cost s i.
Proof. intros. unfold advance_state. simpl. reflexivity. Qed.

(** PNEW field consequences: vm_apply (instr_pnew r c) preserves mem, regs,
    certified and advances pc by 1.  Proved by destructuring graph_add_module
    (whose return value does not affect the advance_state mem/regs/pc fields). *)

Lemma vm_apply_pnew_mem_preserved :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_mem) = s.(vm_mem).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  apply advance_state_mem_eq.
Qed.

Lemma vm_apply_pnew_regs_preserved :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_regs) = s.(vm_regs).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  apply advance_state_regs_eq.
Qed.

Lemma vm_apply_pnew_pc_advances :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_pc) = S s.(vm_pc).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  apply advance_state_pc_eq.
Qed.

Lemma vm_apply_pnew_certified_preserved :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_certified) = s.(vm_certified).
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  apply advance_state_certified_eq.
Qed.

Lemma vm_apply_pnew_mu_charged :
  forall s r c, (vm_apply s (instr_pnew r c)).(vm_mu) = s.(vm_mu) + c.
Proof.
  intros s r c. unfold vm_apply.
  destruct (graph_add_module s.(vm_graph) (List.seq 0 _) []) as [g' _].
  unfold advance_state, apply_cost, instruction_cost. simpl. reflexivity.
Qed.

(** CERTIFY field consequences: vm_apply (instr_certify d) preserves mem and
    regs, advances pc by 1, and unconditionally sets vm_certified := true.
    These follow directly from the inline record constructor in vm_apply. *)

Lemma vm_apply_certify_mem_preserved :
  forall s d, (vm_apply s (instr_certify d)).(vm_mem) = s.(vm_mem).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma vm_apply_certify_regs_preserved :
  forall s d, (vm_apply s (instr_certify d)).(vm_regs) = s.(vm_regs).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma vm_apply_certify_pc_advances :
  forall s d, (vm_apply s (instr_certify d)).(vm_pc) = S s.(vm_pc).
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma vm_apply_certify_certified :
  forall s d, (vm_apply s (instr_certify d)).(vm_certified) = true.
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

Lemma vm_apply_certify_mu_charged :
  forall s d, (vm_apply s (instr_certify d)).(vm_mu) = s.(vm_mu) + S d.
Proof. intros. unfold vm_apply. simpl. reflexivity. Qed.

(** The strict shadow is preserved equally by both CERTIFY and PNEW
    relative to any source state: both advance pc by 1 and leave mem/regs
    untouched.  This general form is used in the final shadow-equality proof. *)
Lemma vm_apply_certify_strict_shadow :
  forall s d,
    strict_shadow (vm_apply s (instr_certify d)) =
    {| scs_mem := s.(vm_mem); scs_regs := s.(vm_regs); scs_pc := S s.(vm_pc) |}.
Proof.
  intros s d.
  unfold strict_shadow.
  rewrite vm_apply_certify_mem_preserved,
          vm_apply_certify_regs_preserved,
          vm_apply_certify_pc_advances.
  reflexivity.
Qed.

Lemma vm_apply_pnew_strict_shadow :
  forall s r c,
    strict_shadow (vm_apply s (instr_pnew r c)) =
    {| scs_mem := s.(vm_mem); scs_regs := s.(vm_regs); scs_pc := S s.(vm_pc) |}.
Proof.
  intros s r c.
  unfold strict_shadow.
  rewrite vm_apply_pnew_mem_preserved,
          vm_apply_pnew_regs_preserved,
          vm_apply_pnew_pc_advances.
  reflexivity.
Qed.


(** ** §3. Witness state definitions

    Five names defined in this section:

      - [po1_init]: the common initial state for both traces.
      - [po1_instr_A]: the single instruction in Trace A
        ([instr_certify 0]).
      - [po1_state_A]: the final state of Trace A.
      - [po1_instr_B]: the single instruction in Trace B
        ([instr_pnew [] 0]).
      - [po1_state_B]: the final state of Trace B. *)

Definition po1_empty_graph : PartitionGraph := {|
  pg_next_id       := 0;
  pg_modules       := [];
  pg_next_morph_id := 0;
  pg_morphisms     := []
|}.

Definition po1_empty_csrs : CSRState :=
  {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |}.

Definition po1_empty_witness : WitnessCounts :=
  {| wc_same_00 := 0; wc_diff_00 := 0;
     wc_same_01 := 0; wc_diff_01 := 0;
     wc_same_10 := 0; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 0 |}.

(** po1_init: the common starting state.
    Condition (1): both Trace A and Trace B begin here.
    Strict classical shadow: (mem=[], regs=[], pc=0).
    Structural state: μ=0, certified=false, empty graph. *)
Definition po1_init : VMState := {|
  vm_graph     := po1_empty_graph;
  vm_csrs      := po1_empty_csrs;
  vm_regs      := [];
  vm_mem       := [];
  vm_pc        := 0;
  vm_mu        := 0;
  vm_mu_tensor := repeat 0 16;
  vm_err       := false;
  vm_logic_acc := 0;
  vm_mstatus   := 0;
  vm_witness   := po1_empty_witness;
  vm_certified := false
|}.

(** Trace A: execute CERTIFY from po1_init.
    Final state: pc=1, μ=1, certified=true, mem=[], regs=[]. *)
Definition po1_instr_A : vm_instruction := instr_certify 0.
Definition po1_state_A : VMState := vm_apply po1_init po1_instr_A.

(** Trace B: execute PNEW [] 0 from po1_init.
    instruction_cost (instr_pnew [] 0) = 0  (no S-floor for pnew).
    Final state: pc=1, μ=0, certified=false, mem=[], regs=[].
    vm_graph gains one empty partition module — invisible to strict_shadow. *)
Definition po1_instr_B : vm_instruction := instr_pnew [] 0.
Definition po1_state_B : VMState := vm_apply po1_init po1_instr_B.

Definition po1_strict_trace_A : list StrictClassicalState :=
  [strict_shadow po1_init; strict_shadow po1_state_A].

Definition po1_strict_trace_B : list StrictClassicalState :=
  [strict_shadow po1_init; strict_shadow po1_state_B].


(** ** §4. The seven conditions

    Each condition is stated and proved as a named theorem. *)

(** CONDITION (1): Identical starting point.
    Both strict-shadow traces begin at the same head element, namely
    [strict_shadow po1_init].  Stated as agreement of the step-0 entries
    of [po1_strict_trace_A] and [po1_strict_trace_B], a fact about the
    actual trace lists, not just a normalization of [strict_shadow] on
    the empty VM state.  Any classical observer sees the same starting
    configuration in both traces. *)
Theorem po1_cond1_identical_start :
  nth_error po1_strict_trace_A 0 = Some (strict_shadow po1_init) /\
  nth_error po1_strict_trace_B 0 = Some (strict_shadow po1_init).
Proof. split; reflexivity. Qed.

(** CONDITION (2a): At step 0, the strict-classical shadows of the two
    traces agree element-wise. *)
Theorem po1_cond2_step0 :
  nth_error po1_strict_trace_A 0 = nth_error po1_strict_trace_B 0.
Proof. reflexivity. Qed.

(** CONDITION (2b): At the final step (step 1), the strict shadows are equal.
    Both programs advance pc by 1 and preserve mem and regs; the only
    differences are in vm_mu, vm_certified, and vm_graph, which strict_shadow
    does not observe. *)
Theorem po1_cond2_final_shadow_equal :
  strict_shadow po1_state_A = strict_shadow po1_state_B.
Proof.
  unfold po1_state_A, po1_state_B, po1_instr_A, po1_instr_B.
  rewrite vm_apply_certify_strict_shadow,
          vm_apply_pnew_strict_shadow.
  unfold po1_init. simpl. reflexivity.
Qed.

(** CONDITION (2c): The complete strict-classical shadow traces are equal.
    Since both executions have length one, step 0 and step 1 are the whole
    trace. *)
Theorem po1_cond2_shadow_traces_equal :
  po1_strict_trace_A = po1_strict_trace_B.
Proof.
  unfold po1_strict_trace_A, po1_strict_trace_B.
  rewrite po1_cond2_final_shadow_equal.
  reflexivity.
Qed.

(** CONDITION (3): Identical classical resource footprint.
    Both traces consist of exactly one instruction step.
    Classical time complexity is equal (length 1); classical space complexity
    is equal (both start and end with empty data memory). *)
Theorem po1_cond3_equal_trace_length :
  length [po1_instr_A] = length [po1_instr_B].
Proof. simpl. reflexivity. Qed.

Theorem po1_cond3_equal_mem_size :
  length po1_state_A.(vm_mem) = length po1_state_B.(vm_mem).
Proof.
  unfold po1_state_A, po1_state_B, po1_instr_A, po1_instr_B.
  rewrite vm_apply_certify_mem_preserved,
          vm_apply_pnew_mem_preserved.
  reflexivity.
Qed.

(** CONDITION (4): Trace A certifies.
    CERTIFY unconditionally sets vm_certified := true by definition of vm_apply. *)
Theorem po1_cond4_trace_A_certified :
  po1_state_A.(vm_certified) = true.
Proof.
  unfold po1_state_A, po1_instr_A.
  apply vm_apply_certify_certified.
Qed.

Theorem po1_cond4_trace_A_mu_paid :
  po1_state_A.(vm_mu) = 1.
Proof.
  unfold po1_state_A, po1_instr_A.
  rewrite vm_apply_certify_mu_charged.
  unfold po1_init. simpl. reflexivity.
Qed.

(** CONDITION (5): Trace B does not certify.
    PNEW preserves vm_certified from the source state.
    po1_init.(vm_certified) = false by definition. *)
Theorem po1_cond5_trace_B_not_certified :
  po1_state_B.(vm_certified) = false.
Proof.
  unfold po1_state_B, po1_instr_B.
  rewrite vm_apply_pnew_certified_preserved.
  unfold po1_init. simpl. reflexivity.
Qed.

Theorem po1_cond5_trace_B_mu_zero :
  po1_state_B.(vm_mu) = 0.
Proof.
  unfold po1_state_B, po1_instr_B.
  rewrite vm_apply_pnew_mu_charged.
  unfold po1_init. simpl. reflexivity.
Qed.

(** CONDITION (6): A classically-definable predicate.
    Any observer whose input is only StrictClassicalState must give equal
    answers on the two final states, because the inputs are equal.  Omega_pc1
    is a concrete example: it tests whether the program counter equals 1. *)
Definition Omega_pc1 (cs : StrictClassicalState) : bool :=
  Nat.eqb cs.(scs_pc) 1.

Theorem po1_cond6_any_strict_shadow_function_equal :
  forall {A : Type} (f : StrictClassicalState -> A),
    f (strict_shadow po1_state_A) = f (strict_shadow po1_state_B).
Proof.
  intros A f.
  rewrite po1_cond2_final_shadow_equal.
  reflexivity.
Qed.

Theorem po1_cond6_omega_gives_equal_results :
  Omega_pc1 (strict_shadow po1_state_A) = Omega_pc1 (strict_shadow po1_state_B).
Proof.
  apply po1_cond6_any_strict_shadow_function_equal.
Qed.

(** CONDITION (7): The contradiction.
    Suppose Omega : StrictClassicalState → bool satisfies
      ∀ s, Omega (strict_shadow s) = s.(vm_certified).
    Then:
      Omega (strict_shadow po1_state_A) = true    (by cond 4)
      Omega (strict_shadow po1_state_B) = false   (by cond 5)
    But strict_shadow po1_state_A = strict_shadow po1_state_B  (by cond 2),
    so the same function on the same input returns both true and false. □ *)
Theorem po1_cond7_contradiction_components :
  forall (Omega : StrictClassicalState -> bool),
    (forall (s : VMState), Omega (strict_shadow s) = s.(vm_certified)) ->
    Omega (strict_shadow po1_state_A) = true /\
    Omega (strict_shadow po1_state_B) = false /\
    strict_shadow po1_state_A = strict_shadow po1_state_B.
Proof.
  intros Omega HOmega.
  refine (conj _ (conj _ po1_cond2_final_shadow_equal)).
  - rewrite HOmega. exact po1_cond4_trace_A_certified.
  - rewrite HOmega. exact po1_cond5_trace_B_not_certified.
Qed.

Theorem po1_cond7_mu_contradiction_components :
  forall (Omega : StrictClassicalState -> nat),
    (forall (s : VMState), Omega (strict_shadow s) = s.(vm_mu)) ->
    Omega (strict_shadow po1_state_A) = 1 /\
    Omega (strict_shadow po1_state_B) = 0 /\
    strict_shadow po1_state_A = strict_shadow po1_state_B.
Proof.
  intros Omega HOmega.
  refine (conj _ (conj _ po1_cond2_final_shadow_equal)).
  - rewrite HOmega. exact po1_cond4_trace_A_mu_paid.
  - rewrite HOmega. exact po1_cond5_trace_B_mu_zero.
Qed.


(** ** §5. The necessity theorem

    Main result: there is no function of the strict classical state
    [(mem, regs, pc)] that correctly predicts both the μ-ledger and
    [vm_certified] for all Thiele Machine states.

    The proof is by contradiction. Assume such an Omega exists. Apply
    it to [po1_state_A] and [po1_state_B]:

      - Omega predicts [(1, true)] for A.
      - Omega predicts [(0, false)] for B.
    But both states have identical strict shadows  (cond 2).
    Since Omega is a function, equal inputs must give equal outputs.
    Therefore [(1, true) = (0, false)] — a contradiction.

    This establishes the μ-ledger as a logically necessary additional
    state variable: it cannot be recovered from, or reduced to, the
    classical computational state. *)

(** The main necessity theorem.
    No classical observer on (mem, regs, pc) can predict the structural receipt
    pair consisting of the μ-ledger and certification flag. *)
Theorem mu_ledger_necessity :
  ~ exists (Omega : StrictClassicalState -> nat * bool),
      forall (s : VMState),
        Omega (strict_shadow s) = (s.(vm_mu), s.(vm_certified)).
Proof.
  intros [Omega HOmega].
  assert (HA : Omega (strict_shadow po1_state_A) = (1, true)).
  { rewrite HOmega.
    rewrite po1_cond4_trace_A_mu_paid, po1_cond4_trace_A_certified.
    reflexivity. }
  assert (HB : Omega (strict_shadow po1_state_B) = (0, false)).
  { rewrite HOmega.
    rewrite po1_cond5_trace_B_mu_zero, po1_cond5_trace_B_not_certified.
    reflexivity. }
  rewrite po1_cond2_final_shadow_equal in HA.
  rewrite HA in HB.
  discriminate HB.
Qed.

(** Direct μ-ledger form: no classical function can recover vm_mu. *)
Theorem vm_mu_not_classically_determined :
  ~ exists (Omega : StrictClassicalState -> nat),
      forall (s : VMState), Omega (strict_shadow s) = s.(vm_mu).
Proof.
  intros [Omega HOmega].
  pose proof (po1_cond7_mu_contradiction_components Omega HOmega)
    as [HA [HB Heq]].
  rewrite Heq in HA.
  rewrite HA in HB.
  discriminate HB.
Qed.

(** Direct certification form: no classical predicate can recover vm_certified. *)
Theorem certification_necessity :
  ~ exists (Omega : StrictClassicalState -> bool),
      forall (s : VMState), Omega (strict_shadow s) = s.(vm_certified).
Proof.
  intros [Omega HOmega].
  pose proof (po1_cond7_contradiction_components Omega HOmega) as [HA [HB Heq]].
  rewrite Heq in HA.
  rewrite HA in HB.
  discriminate HB.
Qed.

(** Constructive form: for any claimed classical structural-receipt predictor
    Omega, there exist two explicit states that falsify it — they have equal
    classical shadows but different μ/certification status, so Omega cannot be
    correct for both. *)
Corollary mu_ledger_necessity_constructive :
  forall (Omega : StrictClassicalState -> nat * bool),
    ~ (forall (s : VMState),
          Omega (strict_shadow s) = (s.(vm_mu), s.(vm_certified))).
Proof.
  intros Omega HOmega.
  exact (mu_ledger_necessity (ex_intro _ Omega HOmega)).
Qed.

(** Witness form: explicit states with equal strict shadow but divergent μ and
    certification, both reachable in one step from the same starting state.
    This is the constructive certificate for the separation. *)
Theorem po1_separation_witnesses :
  exists (s_init s_A s_B : VMState) (i_A i_B : vm_instruction),
    strict_shadow s_init = strict_shadow s_init /\
    s_A = vm_apply s_init i_A /\
    s_B = vm_apply s_init i_B /\
    strict_shadow s_A = strict_shadow s_B /\
    s_A.(vm_mu) = 1 /\
    s_B.(vm_mu) = 0 /\
    s_A.(vm_certified) = true /\
    s_B.(vm_certified) = false.
Proof.
  exists po1_init, po1_state_A, po1_state_B, po1_instr_A, po1_instr_B.
  exact (conj (eq_refl _)
        (conj (eq_refl _)
        (conj (eq_refl _)
        (conj po1_cond2_final_shadow_equal
        (conj po1_cond4_trace_A_mu_paid
        (conj po1_cond5_trace_B_mu_zero
        (conj po1_cond4_trace_A_certified
              po1_cond5_trace_B_not_certified))))))).
Qed.

(** The structural state (vm_certified) is strictly not a function of the
    strict classical state.  No function of type StrictClassicalState → bool
    can serve as a correct oracle for vm_certified on all reachable states.
    Equivalently: vm_certified is orthogonal to (mem, regs, pc). *)
Theorem vm_certified_not_classically_determined :
  ~ exists (f : StrictClassicalState -> bool),
      forall (s : VMState), f (strict_shadow s) = s.(vm_certified).
Proof. exact certification_necessity. Qed.

(** Pointwise μ-ledger form: for any f, there exist two states with the same
    strict shadow on which f disagrees with vm_mu on at least one of them. *)
Corollary vm_mu_classical_oracle_fails :
  forall (f : StrictClassicalState -> nat),
    exists (s1 s2 : VMState),
      strict_shadow s1 = strict_shadow s2 /\
      (f (strict_shadow s1) <> s1.(vm_mu) \/
       f (strict_shadow s2) <> s2.(vm_mu)).
Proof.
  intro f.
  exists po1_state_A, po1_state_B.
  split.
  { exact po1_cond2_final_shadow_equal. }
  destruct (Nat.eq_dec (f (strict_shadow po1_state_A)) 1) as [HfA | HfA].
  - right.
    rewrite po1_cond5_trace_B_mu_zero.
    rewrite <- po1_cond2_final_shadow_equal.
    rewrite HfA.
    discriminate.
  - left.
    rewrite po1_cond4_trace_A_mu_paid.
    exact HfA.
Qed.

(** Pointwise form: for any f, there exist two states with the same strict
    shadow on which f disagrees with vm_certified on at least one of them. *)
Corollary vm_certified_classical_oracle_fails :
  forall (f : StrictClassicalState -> bool),
    exists (s1 s2 : VMState),
      strict_shadow s1 = strict_shadow s2 /\
      (f (strict_shadow s1) <> s1.(vm_certified) \/
       f (strict_shadow s2) <> s2.(vm_certified)).
Proof.
  intro f.
  exists po1_state_A, po1_state_B.
  split.
  { exact po1_cond2_final_shadow_equal. }
  (* Either f mispredicts A or f mispredicts B — in both cases f fails.
     We derive this from the fact that both shadows are equal: f returns
     one value, but vm_certified differs between A and B. *)
  destruct (f (strict_shadow po1_state_A)) eqn:HfA.
  - (* f returns true on the common shadow — it must mispredict B (false) *)
    right.
    rewrite po1_cond5_trace_B_not_certified.
    rewrite <- po1_cond2_final_shadow_equal.
    rewrite HfA.
    discriminate.
  - (* f returns false on the common shadow — it must mispredict A (true).
       After destruct, the goal's LHS is already the literal false, so
       rewriting po1_cond4_trace_A_certified yields false <> true directly. *)
    left.
    rewrite po1_cond4_trace_A_certified.
    discriminate.
Qed.


(** ** §6. Trace-level necessity and universality

    §5 proves necessity using witnesses rooted at [po1_init]. This
    section strengthens the result in two directions:

      - (A) Universality: the divergence holds from any state, not
        only [po1_init]. For any [VMState] [s], CERTIFY 0 and PNEW [] 0
        produce the same strict shadow but different μ and
        certification. No matter what prefix program has run, the
        next-step separation remains intact.
      - (B) Trace-level: for any common prefix program, extending with
        CERTIFY 0 versus PNEW [] 0 yields two programs with equal
        final strict shadows but strictly different μ-ledgers. The
        separation cannot be closed by accumulating more classical
        computation before the diverging step.

    Together these say that μ-ledger independence is not an artefact
    of a single crafted witness; it is a structural property of every
    reachable state of the Thiele Machine. *)

(** Multi-step execution: apply a list of instructions in sequence. *)
Fixpoint run_instrs (s : VMState) (instrs : list vm_instruction) : VMState :=
  match instrs with
  | [] => s
  | i :: rest => run_instrs (vm_apply s i) rest
  end.

Lemma run_instrs_append :
  forall (s : VMState) (p q : list vm_instruction),
    run_instrs s (p ++ q) = run_instrs (run_instrs s p) q.
Proof.
  intros s p q. revert s.
  induction p as [| i p' IH]; intro s; simpl.
  - reflexivity.
  - exact (IH (vm_apply s i)).
Qed.

Lemma run_instrs_single :
  forall (s : VMState) (i : vm_instruction),
    run_instrs s [i] = vm_apply s i.
Proof. intros s i. unfold run_instrs. reflexivity. Qed.

(** §6A — UNIVERSALITY: From any state, CERTIFY 0 and PNEW [] 0 produce
    the same strict shadow but different μ-ledger and certification status.

    CERTIFY 0 charges S(0) = 1 and sets vm_certified := true.
    PNEW [] 0 charges 0 and preserves vm_certified from the source state.
    Both advance pc by 1 and leave mem and regs unchanged: same strict shadow. *)
Theorem mu_ledger_necessity_universal :
  forall (s : VMState),
    strict_shadow (vm_apply s (instr_certify 0)) =
    strict_shadow (vm_apply s (instr_pnew [] 0)) /\
    (vm_apply s (instr_certify 0)).(vm_mu) = s.(vm_mu) + 1 /\
    (vm_apply s (instr_pnew [] 0)).(vm_mu) = s.(vm_mu) /\
    (vm_apply s (instr_certify 0)).(vm_certified) = true.
Proof.
  intro s.
  refine (conj _ (conj _ (conj _ _))).
  - rewrite vm_apply_certify_strict_shadow, vm_apply_pnew_strict_shadow.
    reflexivity.
  - rewrite vm_apply_certify_mu_charged. simpl. lia.
  - rewrite vm_apply_pnew_mu_charged. simpl. lia.
  - apply vm_apply_certify_certified.
Qed.

(** §6B — TRACE-LEVEL: For any common prefix program, the two extensions
    (CERTIFY 0 vs. PNEW [] 0) reach the same strict shadow but different μ.

    This means: no amount of classical computation before the diverging step
    can make the μ-ledger recoverable from the strict classical shadow. *)
Theorem po1_trace_necessity :
  forall (prefix : list vm_instruction),
    strict_shadow (run_instrs po1_init (prefix ++ [instr_certify 0])) =
    strict_shadow (run_instrs po1_init (prefix ++ [instr_pnew [] 0])) /\
    (run_instrs po1_init (prefix ++ [instr_certify 0])).(vm_mu) >
    (run_instrs po1_init (prefix ++ [instr_pnew [] 0])).(vm_mu).
Proof.
  intro prefix.
  rewrite !run_instrs_append, !run_instrs_single.
  pose proof (mu_ledger_necessity_universal (run_instrs po1_init prefix))
    as [Hsh [Hmu1 [Hmu0 _]]].
  split.
  - exact Hsh.
  - rewrite Hmu1, Hmu0. lia.
Qed.

(** Corollary: the base case (empty prefix) recovers the single-step result,
    and for any prefix of length n, programs of length n+1 maintain the
    separation.  No extension of classical computation closes the gap. *)
Corollary po1_trace_necessity_any_length :
  forall (n : nat) (prefix : list vm_instruction),
    length prefix = n ->
    strict_shadow (run_instrs po1_init (prefix ++ [instr_certify 0])) =
    strict_shadow (run_instrs po1_init (prefix ++ [instr_pnew [] 0])) /\
    (run_instrs po1_init (prefix ++ [instr_certify 0])).(vm_mu) >
    (run_instrs po1_init (prefix ++ [instr_pnew [] 0])).(vm_mu).
Proof.
  intros n prefix _. exact (po1_trace_necessity prefix).
Qed.


(** ** §7. The latent-μ theorem: μ-cost is intrinsic to computation

    §§4–6 prove that the μ-ledger is inaccessible to classical
    observers. This section proves the converse direction: the μ-cost
    is not just hidden from classical machines, it is latent in every
    computation, present whether or not any ledger exists to record
    it.

    Three named results in this section:

      - [shadow_mu_is_computation_intrinsic]: total μ accumulated by
        running any instruction sequence equals the sum of instruction
        costs. The sum is determined entirely by the instruction
        sequence and does not depend on starting μ, [vm_graph],
        [vm_regs], [vm_mem], or any other state.
      - [shadow_mu_delta_universal]: any two Thiele VM states running
        the same instruction sequence accumulate the same additional
        μ. The δ is written into the program; the starting state does
        not change it. This is universality across starting states,
        not across substrates — the substrate-independent claim lives
        in [UniversalCertificationCost.v].
      - [shadow_mu_inevitable]: for any non-empty program containing
        at least one instruction with positive cost, the accumulated
        δ-μ on the Thiele VM is strictly positive. There is no free
        certification under the cost law.

    The cost is in the instruction sequence, not in the machine. Any
    system running this trace under the Thiele cost law accumulates
    exactly [trace_total_cost]. The substrate-independent layer that
    gives this teeth is [universal_nfi_any_substrate] in
    [UniversalCertificationCost.v]: under A2 (cert-flip costs ≥ 1),
    every uncertified-to-certified trace pays ≥ 1 in total on any
    substrate. A Turing machine that satisfies A2 — for example by
    mapping μ to an address and incrementing on cert-flip — is a
    witness for that theorem, not a counterexample.
    [thiele_morphism_exists] then makes the Thiele VM the initial
    cost-preserving simulation.

    Read together: honest cost-tracking on any substrate forces the
    receipt to exist; the strict-classical shadow [(mem, regs, pc)]
    by construction cannot host it; the Thiele VM is the canonical
    instance that exposes it. The ledger does not create the cost,
    it reveals what A2 forces on every honest implementation. *)

(** Bridge: run_instrs and exec_trace_from (MuInitiality.v) are the same
    function.  Both are left-folds of vm_apply over an instruction list. *)
Lemma run_instrs_eq_exec_trace_from :
  forall (s : VMState) (prog : list vm_instruction),
    run_instrs s prog = exec_trace_from s prog.
Proof.
  intros s prog. revert s.
  induction prog as [|i rest IH]; intro s; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** THE CORE THEOREM: the total μ accumulated by any program equals the
    starting μ plus the sum of instruction costs.  The accumulation is a
    pure function of the instruction sequence — it does not depend on any
    other field of the machine state (graph, regs, mem, pc, certified). *)
Theorem shadow_mu_is_computation_intrinsic :
  forall (prog : list vm_instruction) (s : VMState),
    (run_instrs s prog).(vm_mu) = s.(vm_mu) + trace_total_cost prog.
Proof.
  intros prog s.
  rewrite run_instrs_eq_exec_trace_from.
  apply mu_accumulates_trace_cost.
Qed.

(** UNIVERSALITY: two machines running the same program — from any two
    starting states, with any starting μ-values — accumulate the same
    additional μ.  The δ-μ is a property of the computation, not the
    machine. *)
Theorem shadow_mu_delta_universal :
  forall (prog : list vm_instruction) (s1 s2 : VMState),
    (run_instrs s1 prog).(vm_mu) + s2.(vm_mu) =
    (run_instrs s2 prog).(vm_mu) + s1.(vm_mu).
Proof.
  intros prog s1 s2.
  rewrite !shadow_mu_is_computation_intrinsic. lia.
Qed.

(** Helper: any instruction-consistent M accumulates exactly its cost
    over any run.  Proved by direct induction — avoids the inline-fixpoint
    form of consistent_accumulates_trace_cost. *)
Lemma M_run_instrs_eq :
  forall (M : VMState -> nat),
    instruction_consistent M canonical_cost ->
    forall (prog : list vm_instruction) (s : VMState),
      M (run_instrs s prog) = M s + trace_total_cost prog.
Proof.
  intros M Hcons prog.
  induction prog as [|i rest IH]; intro s.
  - simpl. lia.
  - simpl run_instrs. simpl trace_total_cost.
    rewrite IH.
    unfold instruction_consistent in Hcons.
    rewrite (Hcons s i).
    unfold canonical_cost. lia.
Qed.

(** UNIQUENESS OF THE SHADOW: any instruction-consistent accounting system
    that assigns zero to a starting state will assign exactly trace_total_cost
    to the result of running any program from that state.  The cost is not a
    choice — it is forced by the instruction sequence.

    Replace the Thiele Machine's vm_mu counter with any other
    instruction-consistent measure and you get the same number.  The Turing
    machine paid this cost in every execution; it simply had no counter to
    store the receipt. *)
Theorem shadow_mu_unique_accounting :
  forall (prog : list vm_instruction) (s : VMState),
    forall (M : VMState -> nat),
      instruction_consistent M canonical_cost ->
      M s = 0 ->
      M (run_instrs s prog) = trace_total_cost prog.
Proof.
  intros prog s M Hcons HMs.
  rewrite (M_run_instrs_eq M Hcons prog s).
  rewrite HMs. lia.
Qed.

(** Canonical witness: running from init_state (vm_mu = 0), the accumulated
    μ equals trace_total_cost exactly.  The shadow cost of any program
    starting from zero is uniquely and completely determined. *)
Corollary shadow_mu_from_init :
  forall (prog : list vm_instruction),
    (run_instrs init_state prog).(vm_mu) = trace_total_cost prog.
Proof.
  intro prog.
  rewrite shadow_mu_is_computation_intrinsic.
  rewrite init_state_mu_zero. lia.
Qed.

(** INEVITABILITY: any program containing an instruction with positive
    declared cost accumulates strictly positive total μ — from any
    starting state.  There is no free computation. *)
Theorem shadow_mu_inevitable :
  forall (prog : list vm_instruction) (s : VMState) (i : vm_instruction),
    In i prog ->
    instruction_cost i > 0 ->
    (run_instrs s prog).(vm_mu) > s.(vm_mu).
Proof.
  intros prog s i Hin Hcost.
  rewrite shadow_mu_is_computation_intrinsic.
  assert (H : trace_total_cost prog >= instruction_cost i).
  { induction prog as [|h rest IH].
    - contradiction.
    - simpl in Hin. simpl.
      destruct Hin as [Heq | Hin'].
      + subst. lia.
      + pose proof (IH Hin'). lia. }
  lia.
Qed.
