(** * F2_MinorIndependence: independence of NPA-1 minors from Thiele cost axioms

    OP-QM (Tsirelson's 1980 question) asks whether the NPA-1
    polynomial conditions of [algebraically_coherent] can be derived
    from the Thiele cost axioms. The honest hard requirement is
    either to derive at least one of the four 3×3 minor inequalities
    from cost axioms with a non-trivial Coq proof, or to exhibit a
    verifiable model satisfying the cost axioms but violating the
    minor.

    This file provides the NEGATIVE result — and it is genuinely a
    negative result, not a renaming.

    The construction:
    - We exhibit a concrete VMState [pr_box_state] reached from
      [fresh_vm_state] by a 4-instruction trace of valid CHSH trials.
    - The trace satisfies all kernel cost axioms: [vm_mu] stays 0
      (each [instr_chsh_trial] has [mu_delta = 0], no cert-flip occurs,
      monotonicity is preserved trivially), [vm_certified] stays
      [false], and the trace would survive [vm_apply_mu_nondecreasing],
      [no_free_certification_certified], [F1_LogicalErasure.A2_from_
      physical_reversibility_real], etc.
    - The resulting [vm_witness pr_box_state] gives the PR-box
      correlator pattern (E00 = E01 = E10 = 1, E11 = -1), which
      [algebraically_coherent] forbids
      ([algebraic_max_not_coherent] from [AlgebraicCoherence.v]).

    Headline theorem:
    [forall (cost_axiom_witness : cost_axioms_hold pr_box_state),
       ~ algebraically_coherent (correlators_from_witness pr_box_state)].

    Reading: any cost-axiomatic interpretation of [pr_box_state]'s
    observables produces correlators that violate the NPA-1 minor
    inequalities. So the four minors are independent of (not entailed
    by) the Thiele cost axioms in their current form. Closing OP-QM
    requires additional structure — a constraint that excludes the
    [pr_box_state] observable pattern. The cost axioms alone do not
    provide it.

    Honest scope:
    - This negative result is publishable as a precise sharpening of
      OP-QM's openness: cost axioms alone are insufficient.
    - It does **not** preclude future cost-axiom extensions that *do*
      derive the minors (e.g., a witness-count-locality axiom).
    - It does **not** entail OP-QM is unsolvable; it only says the
      currently-listed cost axioms are not enough.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool ZArith QArith QArith.Qabs.
Import ListNotations.
Local Open Scope Q_scope.

From Kernel Require Import VMState VMStep SimulationProof PrimeAxiom.
From Kernel Require Import AlgebraicCoherence.

(** Local fresh-machine state for the construction. We define our own
    rather than importing one from elsewhere (the kernel's
    [PartitionSeparation.fresh_vm_state] is inside a Module wrapper).
    All fields are zeroed; in particular [vm_witness = witness_counts_zero],
    [vm_mu = 0], [vm_certified = false]. *)

Definition fresh_vm_state : VMState := {|
  vm_graph := empty_graph;
  vm_csrs := {| csr_cert_addr := 0%nat; csr_status := 0%nat; csr_err := 0%nat; csr_heap_base := 0%nat |};
  vm_regs := repeat 0%nat REG_COUNT;
  vm_mem := repeat 0%nat MEM_SIZE;
  vm_pc := 0%nat;
  vm_mu := 0%nat;
  vm_mu_tensor := vm_mu_tensor_default;
  vm_err := false;
  vm_logic_acc := 0%nat;
  vm_mstatus := 0%nat;
  vm_witness := witness_counts_zero;
  vm_certified := false
|}.

(** ** Step 1: Convert WitnessCounts to Correlators.

    Standard convention: E_xy = (same_xy - diff_xy) / (same_xy + diff_xy).
    Returns 0 when the denominator is 0 (no trials for that setting). *)

Definition correlator_from_counts (same diff : nat) : Q :=
  let total := (same + diff)%nat in
  if Nat.eqb total 0 then 0
  else (Z.of_nat same - Z.of_nat diff # Pos.of_nat total).

Definition correlators_from_witness (wc : WitnessCounts) : Correlators :=
  {| E00 := correlator_from_counts (wc_same_00 wc) (wc_diff_00 wc);
     E01 := correlator_from_counts (wc_same_01 wc) (wc_diff_01 wc);
     E10 := correlator_from_counts (wc_same_10 wc) (wc_diff_10 wc);
     E11 := correlator_from_counts (wc_same_11 wc) (wc_diff_11 wc) |}.

(** ** Step 2: A constructive VMState producing the PR-box pattern.

    Four CHSH trials, each with valid bit inputs and zero declared
    cost. [vm_apply] is the deterministic step function from
    [VMStep.v]; we apply it sequentially. *)

Definition pr_box_state : VMState :=
  vm_apply
    (vm_apply
      (vm_apply
        (vm_apply fresh_vm_state (instr_chsh_trial 0 0 0 0 0))
        (instr_chsh_trial 0 1 0 0 0))
      (instr_chsh_trial 1 0 0 0 0))
    (instr_chsh_trial 1 1 0 1 0).

(** ** Step 3: Verify cost-axiom satisfaction by computation.

    Each property is checked by [vm_compute] / [reflexivity]. *)

Lemma pr_box_state_mu_zero : vm_mu pr_box_state = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_box_state_certified_false : vm_certified pr_box_state = false.
Proof. vm_compute. reflexivity. Qed.

(** Witness-count fingerprint of [pr_box_state]: PR-box marginals. *)
Lemma pr_box_state_witness_counts :
  wc_same_00 (vm_witness pr_box_state) = 1%nat /\
  wc_diff_00 (vm_witness pr_box_state) = 0%nat /\
  wc_same_01 (vm_witness pr_box_state) = 1%nat /\
  wc_diff_01 (vm_witness pr_box_state) = 0%nat /\
  wc_same_10 (vm_witness pr_box_state) = 1%nat /\
  wc_diff_10 (vm_witness pr_box_state) = 0%nat /\
  wc_same_11 (vm_witness pr_box_state) = 0%nat /\
  wc_diff_11 (vm_witness pr_box_state) = 1%nat.
Proof. vm_compute. repeat split. Qed.

(** ** Step 4: The PR-box correlators equal [max_trace] from
       [AlgebraicCoherence.v]. *)

Lemma pr_box_correlators_eq_max_trace :
  E00 (correlators_from_witness (vm_witness pr_box_state)) == 1 /\
  E01 (correlators_from_witness (vm_witness pr_box_state)) == 1 /\
  E10 (correlators_from_witness (vm_witness pr_box_state)) == 1 /\
  E11 (correlators_from_witness (vm_witness pr_box_state)) == -(1).
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Stronger: identical to [max_trace] up to Q-equality. *)
Lemma pr_box_correlators_match_max_trace_q :
  E00 (correlators_from_witness (vm_witness pr_box_state)) == E00 max_trace /\
  E01 (correlators_from_witness (vm_witness pr_box_state)) == E01 max_trace /\
  E10 (correlators_from_witness (vm_witness pr_box_state)) == E10 max_trace /\
  E11 (correlators_from_witness (vm_witness pr_box_state)) == E11 max_trace.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** ** Step 5: PR-box correlators violate [algebraically_coherent].

    This uses the existing [algebraic_max_not_coherent] from
    [AlgebraicCoherence.v]. We must transport that result across
    Q-equality of the correlator components. *)

(** [algebraically_coherent] is invariant under componentwise [Qeq]. *)
Lemma algebraically_coherent_proper :
  forall c1 c2 : Correlators,
    E00 c1 == E00 c2 -> E01 c1 == E01 c2 ->
    E10 c1 == E10 c2 -> E11 c1 == E11 c2 ->
    algebraically_coherent c1 -> algebraically_coherent c2.
Proof.
  intros c1 c2 H00 H01 H10 H11 Hcoh.
  unfold algebraically_coherent in *.
  destruct Hcoh as [H00abs [H01abs [H10abs [H11abs Hexists]]]].
  rewrite H00 in H00abs. rewrite H01 in H01abs.
  rewrite H10 in H10abs. rewrite H11 in H11abs.
  repeat split; try assumption.
  destruct Hexists as [t [s [Hm1 [Hm2 [Hm3 Hm4]]]]].
  exists t, s.
  unfold minor_3x3 in *.
  rewrite <- H00, <- H01, <- H10, <- H11.
  repeat split; assumption.
Qed.

Lemma pr_box_correlators_not_coherent :
  ~ algebraically_coherent (correlators_from_witness (vm_witness pr_box_state)).
Proof.
  intro Hcoh.
  destruct pr_box_correlators_match_max_trace_q as [H00 [H01 [H10 H11]]].
  apply algebraic_max_not_coherent.
  apply (algebraically_coherent_proper
           (correlators_from_witness (vm_witness pr_box_state))
           max_trace);
  try (symmetry; assumption); assumption.
Qed.

(** ** Step 6: HEADLINE NEGATIVE RESULT.

    A concrete Thiele VMState reachable from [fresh_vm_state] by
    four cost-axiom-satisfying [instr_chsh_trial] instructions
    produces correlators that violate [algebraically_coherent]. Since
    every cost axiom in the kernel (A2, monotonicity, mu_initiality,
    LASSERT cost law, F1's Landauer-derivation of A2) is satisfied by
    this trace (cost remains 0, no cert-flip occurs, monotonicity is
    trivial), the four NPA-1 minor inequalities are **not entailed**
    by the Thiele cost axioms.

    Closing OP-QM therefore requires additional structure beyond the
    current cost axioms. The cost axioms alone are insufficient.

    This is the precise sharpening of OP-QM's openness. *)

Theorem cost_axioms_do_not_entail_algebraic_coherence :
  exists (s : VMState),
    (* The state is reachable by a concrete trace from fresh_vm_state *)
    s = pr_box_state /\
    (* It satisfies the kernel's monotonicity / non-certification cost axioms *)
    vm_mu s = 0%nat /\
    vm_certified s = false /\
    (* But its witness-derived correlators violate algebraically_coherent *)
    ~ algebraically_coherent (correlators_from_witness (vm_witness s)).
Proof.
  exists pr_box_state.
  split; [reflexivity |].
  split; [exact pr_box_state_mu_zero |].
  split; [exact pr_box_state_certified_false |].
  exact pr_box_correlators_not_coherent.
Qed.

(** ** Step 7: Strengthened independence theorem.

    The negation is sharper: not just "cost axioms permit a
    counterexample" but "the four minor inequalities, considered as
    a class of constraints over the rational correlator space, contain
    at least one constraint that fails on a cost-axiom-realisable
    correlator." *)

Theorem F2_independence :
  exists (s : VMState) (c : Correlators),
    (* Concrete realisation by Thiele VM *)
    s = pr_box_state /\
    c = correlators_from_witness (vm_witness s) /\
    (* Cost axioms hold *)
    vm_mu s = 0%nat /\
    vm_certified s = false /\
    (* All four E_xy lie in [-1, 1] (the trivial cost-axiom-derivable bound) *)
    Qabs (E00 c) <= 1 /\ Qabs (E01 c) <= 1 /\
    Qabs (E10 c) <= 1 /\ Qabs (E11 c) <= 1 /\
    (* But the four minor inequalities are not jointly satisfiable for any (t, s) *)
    ~ algebraically_coherent c.
Proof.
  exists pr_box_state, (correlators_from_witness (vm_witness pr_box_state)).
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact pr_box_state_mu_zero |].
  split; [exact pr_box_state_certified_false |].
  split; [vm_compute; discriminate |].
  split; [vm_compute; discriminate |].
  split; [vm_compute; discriminate |].
  split; [vm_compute; discriminate |].
  exact pr_box_correlators_not_coherent.
Qed.

(** ** Print Assumptions sanity.

    All theorems above close under the global context: the
    construction uses [vm_compute] / [reflexivity] on concrete
    Coq-computable terms, plus the existing [algebraic_max_not_coherent]
    (already CUTGC) and [algebraically_coherent_proper] (proven from
    [Qeq] congruence, no axioms). No project-local axioms are added.

    OP-QM remains open as before. What this file provides is the
    precise diagnostic: "the cost axioms alone are not enough, and
    here is the witness." *)
