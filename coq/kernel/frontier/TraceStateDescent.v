(** Exact descent conditions for the existing VM trace evaluator.
    Results concern reachable states. A selector is explicit where an
    executable function on VMState is constructed; no choice axiom is used. *)
From Coq Require Import List.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof MuInitiality
  UniversalCertificationCost ThieleInitiality PrimeAxiom AbstractNoFI ObservationPolicy.

Definition vm_trace_eval (t : list vm_instruction) := fold_left vm_apply t init_state.
Definition target_trace_eval (M : CertCostMachine) (base : ccm_state M)
    (t : list vm_instruction) := fold_left (ccm_step M) t base.

Definition trace_fiber_compatible (M : CertCostMachine) (base : ccm_state M) :=
  forall t u, vm_trace_eval t = vm_trace_eval u ->
    target_trace_eval M base t = target_trace_eval M base u.
Definition trace_cert_compatible (M : CertCostMachine) (base : ccm_state M) :=
  forall t, vm_certified (vm_trace_eval t) =
    ccm_cert M (target_trace_eval M base t).
Definition descended_value (M : CertCostMachine) (base : ccm_state M)
    (s : VMState) (value : ccm_state M) :=
  exists t, vm_trace_eval t = s /\ target_trace_eval M base t = value.

Theorem trace_descent_unique_value_iff :
  forall M base, trace_fiber_compatible M base <->
    forall t, exists! value, descended_value M base (vm_trace_eval t) value.
Proof.
  intros M base. split.
  - intros H t. exists (target_trace_eval M base t). split.
    + exists t. auto.
    + intros value [u [Hu Hv]]. rewrite <- Hv. apply H. symmetry. exact Hu.
  - intros H t u E. destruct (H t) as [value [Hex Hunique]].
    assert (Ht : value = target_trace_eval M base t).
    { apply Hunique. exists t. auto. }
    assert (Hu : value = target_trace_eval M base u).
    { apply Hunique. exists u. split; [symmetry; exact E|reflexivity]. }
    rewrite <- Ht, <- Hu. reflexivity.
Qed.

Lemma vm_trace_eval_extend : forall t i,
  vm_trace_eval (t ++ [i]) = vm_apply (vm_trace_eval t) i.
Proof. intros. unfold vm_trace_eval. rewrite fold_left_app. reflexivity. Qed.
Lemma target_trace_eval_extend : forall M base t i,
  target_trace_eval M base (t ++ [i]) = ccm_step M (target_trace_eval M base t) i.
Proof. intros. unfold target_trace_eval. rewrite fold_left_app. reflexivity. Qed.

Record ReachableCertSimulation (M : CertCostMachine) (base : ccm_state M) := {
  reachable_map : VMState -> ccm_state M;
  reachable_map_base : reachable_map init_state = base;
  reachable_map_step : forall t i,
    reachable_map (vm_apply (vm_trace_eval t) i) =
      ccm_step M (reachable_map (vm_trace_eval t)) i;
  reachable_map_cert : forall t,
    vm_certified (vm_trace_eval t) = ccm_cert M (reachable_map (vm_trace_eval t))
}.

Theorem reachable_simulation_evaluates_trace :
  forall M base (simulation : ReachableCertSimulation M base) t,
    reachable_map M base simulation (vm_trace_eval t) = target_trace_eval M base t.
Proof.
  intros M base simulation t. induction t using rev_ind.
  - exact (reachable_map_base M base simulation).
  - rewrite vm_trace_eval_extend, target_trace_eval_extend.
    rewrite reachable_map_step, IHt. reflexivity.
Qed.

Theorem reachable_simulation_requires_compatibility :
  forall M base, ReachableCertSimulation M base ->
    trace_fiber_compatible M base /\ trace_cert_compatible M base.
Proof.
  intros M base simulation. split.
  - intros t u E. rewrite <- (reachable_simulation_evaluates_trace M base simulation t).
    rewrite <- (reachable_simulation_evaluates_trace M base simulation u), E. reflexivity.
  - intro t. rewrite <- (reachable_simulation_evaluates_trace M base simulation t).
    apply reachable_map_cert.
Qed.


  Definition build_reachable_simulation (representative : VMState -> list vm_instruction)
      (representative_correct : forall t,
        vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t) (M : CertCostMachine) (base : ccm_state M)
      (Hfiber : trace_fiber_compatible M base)
      (Hcert : trace_cert_compatible M base) : ReachableCertSimulation M base.
  Proof.
    refine {| reachable_map := fun s => target_trace_eval M base (representative s) |}.
    - change (target_trace_eval M base (representative (vm_trace_eval [])) =
        target_trace_eval M base []). apply Hfiber. apply representative_correct.
    - intros t i. rewrite <- vm_trace_eval_extend.
      rewrite (Hfiber _ _ (representative_correct (t ++ [i]))).
      rewrite target_trace_eval_extend.
      rewrite (Hfiber _ _ (representative_correct t)). reflexivity.
    - intro t. rewrite (Hfiber _ _ (representative_correct t)). apply Hcert.
  Defined.

  Theorem reachable_simulation_exists_iff (representative : VMState -> list vm_instruction)
      (representative_correct : forall t,
        vm_trace_eval (representative (vm_trace_eval t)) = vm_trace_eval t) : forall M base,
    inhabited (ReachableCertSimulation M base) <->
    trace_fiber_compatible M base /\ trace_cert_compatible M base.
  Proof.
    intros M base. split.
    - intros [simulation]. apply (reachable_simulation_requires_compatibility M base simulation).
    - intros [Hfiber Hcert]. constructor. exact (build_reachable_simulation representative representative_correct M base Hfiber Hcert).
  Qed.

Theorem reachable_simulation_unique : forall M base
    (left right : ReachableCertSimulation M base) t,
  reachable_map M base left (vm_trace_eval t) =
  reachable_map M base right (vm_trace_eval t).
Proof. intros. rewrite !reachable_simulation_evaluates_trace. reflexivity. Qed.

(** A nontrivial inhabitant: the target forgets everything except certification.
    It reaches both false and true, and is a genuine quotient simulation. *)
Definition certification_quotient : CertCostMachine.
Proof.
  refine {| ccm_state := bool;
            ccm_step := fun certified i =>
              match i with instr_certify _ => true | _ => certified end;
            ccm_cost := instruction_cost;
            ccm_cert := fun certified => certified |}.
  intros certified i Hfalse Htrue.
  destruct i; simpl in *; try congruence; auto with arith.
Defined.

Definition certification_quotient_simulation : ReachableCertSimulation certification_quotient false.
Proof.
  refine (@Build_ReachableCertSimulation certification_quotient false vm_certified _ _ _).
  - reflexivity.
  - intros t i. rewrite vm_apply_certified. destruct i; reflexivity.
  - intro t. reflexivity.
Defined.

Theorem certification_quotient_satisfies_descent :
  trace_fiber_compatible certification_quotient false /\
  trace_cert_compatible certification_quotient false /\
  target_trace_eval certification_quotient false [] = false /\
  target_trace_eval certification_quotient false [instr_certify 0] = true.
Proof.
  destruct (reachable_simulation_requires_compatibility _ _ certification_quotient_simulation).
  repeat split; assumption || reflexivity.
Qed.

(** Certification agreement alone is insufficient. This target keeps the
    complete trace, uses the VM's own certification reading and cost schedule,
    and satisfies A2. A zero-cost VM self-loop still extends its history. *)
Definition trace_history_machine : CertCostMachine.
Proof.
  refine {| ccm_state := list vm_instruction;
            ccm_step := fun t i => t ++ [i];
            ccm_cost := instruction_cost;
            ccm_cert := fun t => vm_certified (vm_trace_eval t) |}.
  intros t i Hbefore Hafter. rewrite vm_trace_eval_extend in Hafter.
  exact (no_free_certification_certified (vm_trace_eval t) i Hbefore Hafter).
Defined.

Lemma history_target_evaluates_to_input : forall t,
  target_trace_eval trace_history_machine [] t = t.
Proof.
  intro t. induction t using rev_ind; [reflexivity|].
  rewrite target_trace_eval_extend, IHt. reflexivity.
Qed.

Theorem certification_agreement_does_not_imply_descent :
  trace_cert_compatible trace_history_machine [] /\
  ~ trace_fiber_compatible trace_history_machine [].
Proof.
  split.
  - intro t. rewrite history_target_evaluates_to_input. reflexivity.
  - intro H.
    assert (E : vm_trace_eval [] = vm_trace_eval [instr_jump 0 0]) by reflexivity.
    specialize (H [] [instr_jump 0 0] E).
    rewrite !history_target_evaluates_to_input in H. discriminate.
Qed.


Definition zero_cost_vm_jump_has_injective_history_lift :=
  ObservationPolicy.zero_cost_vm_jump_has_injective_history_lift.
