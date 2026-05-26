(** * MuDirectSum.v — direct-sum theorem and amortisation counterexample.

    Direct-sum: certifying n independent claims costs ≥ n × (cost of
    one). The classical pattern is well known to be sensitive to the
    *definition* of independence — too weak, and amortisation is
    possible; too strong, and the result is trivial. This file makes
    that sensitivity explicit by proving both sides.

    **Independence definition.** Two claims [P] and [Q] are
    *cert-disjoint independent* if any joint certification of them
    executes at least two cert-setter instructions — one for each
    claim. Concretely: the trace cannot use a single cert-setter event
    to discharge both. Under this definition, direct-sum follows from
    additive ledger accounting:
      [cert_events(P ∧ Q) ≥ 2 = cert_events(P) + cert_events(Q)]
    when each component requires ≥ 1 cert event.

    **Amortisation counterexample.** For a weaker independence
    definition that allows shared cert-setters, a single cert-setter
    can discharge multiple atomic claims. The natural example: the
    claims [is_certified s := vm_certified s = true] and
    [nonzero_mu s := vm_mu s ≥ 1] are both satisfied by a single
    [instr_certify 0] from [init_state] at total cost 1, not 2.

    Direct-sum's truth value is therefore not a property of μ; it is a
    property of the independence definition. Both sides are formal
    facts; both close under the global context with zero [Admitted].
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import MuShannonBridge.
From Kernel Require Import MuHierarchyTheorem.

(* -------------------------------------------------------------------- *)
(** ** Cert-disjoint independence: each component requires its own
    cert-setter execution. *)

Definition cert_events_required_by (k : nat) (s_final : VMState) : Prop :=
  forall fuel trace,
    run_vm fuel trace init_state = s_final ->
    s_final.(vm_certified) = true ->
    cert_setter_executions fuel trace init_state >= k.

(** Strong independence: two claims jointly require the *sum* of
    their individual cert-event lower bounds. We state this as a
    property of the joint final state. *)
Definition cert_disjoint_independent
    (k1 k2 : nat) (s_final : VMState) : Prop :=
  cert_events_required_by (k1 + k2) s_final.

(* -------------------------------------------------------------------- *)
(** ** Direct-sum lower bound under cert-disjoint independence.

    The Δμ on any trace from init_state is the ledger sum, and the
    ledger sum dominates the cert-setter event count
    ([info_priced_cert_executions_bound]). Combining with the
    independence hypothesis gives the additive lower bound.
*)

Theorem direct_sum_lower_bound :
  forall (k1 k2 : nat) (s_final : VMState),
    cert_disjoint_independent k1 k2 s_final ->
    s_final.(vm_certified) = true ->
    forall fuel trace,
      run_vm fuel trace init_state = s_final ->
      s_final.(vm_mu) >= k1 + k2.
Proof.
  intros k1 k2 s_final Hindep Hcert fuel trace Hrun.
  pose proof (Hindep fuel trace Hrun Hcert) as Hevents.
  pose proof (info_priced_cert_executions_bound fuel trace init_state)
    as Hbound.
  rewrite Hrun in Hbound.
  rewrite init_state_mu_zero in Hbound.
  simpl in Hbound.
  rewrite Nat.sub_0_r in Hbound.
  lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** The amortization side: under a weaker independence, a single
    cert-setter discharges multiple "atomic claims."

    The two atomic claims:
    - `is_certified s` := `s.(vm_certified) = true`
    - `nonzero_mu s` := `s.(vm_mu) >= 1`

    A naive independence definition that does not require disjoint
    cert-setter events would treat these as two claims; but a single
    `instr_certify 0` applied to `init_state` produces a state
    satisfying both at cost 1, not 2.
*)

Definition is_certified (s : VMState) : Prop := s.(vm_certified) = true.
Definition nonzero_mu (s : VMState) : Prop := s.(vm_mu) >= 1.

(** The amortizing certifier. *)
Definition amortizing_state : VMState :=
  vm_apply init_state (instr_certify 0).

Lemma amortizing_state_is_certified : is_certified amortizing_state.
Proof.
  unfold is_certified, amortizing_state.
  apply vm_apply_certify_sets_certified.
Qed.

Lemma amortizing_state_nonzero_mu : nonzero_mu amortizing_state.
Proof.
  unfold nonzero_mu, amortizing_state.
  rewrite vm_apply_mu.
  unfold instruction_cost.
  rewrite init_state_mu_zero.
  simpl. lia.
Qed.

(** **The amortization theorem.** Two atomic claims (vm_certified
    and vm_mu ≥ 1) are simultaneously satisfied by a SINGLE
    cert-setter event at total cost 1 — refuting any direct-sum
    formulation that does not enforce cert-event-disjoint independence. *)
Theorem amortization_succeeds :
  is_certified amortizing_state /\
  nonzero_mu amortizing_state /\
  amortizing_state.(vm_mu) = 1.
Proof.
  split; [|split].
  - apply amortizing_state_is_certified.
  - apply amortizing_state_nonzero_mu.
  - unfold amortizing_state. rewrite vm_apply_mu.
    unfold instruction_cost. rewrite init_state_mu_zero.
    simpl. reflexivity.
Qed.

Print Assumptions direct_sum_lower_bound.
Print Assumptions amortization_succeeds.
