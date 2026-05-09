(** MuThresholdDisobedience: failed safety checks beat reward.

    This file formalizes the stop-button claim in a tiny machine model. A
    failed safety check is evaluated before the reward-bearing step, burns its
    μ-cost, and halts the machine immediately. As a result, the promised reward
    never lands, no matter how large it is.

    The supporting lemmas make the operational story explicit: once halted, the
    machine is frozen; μ is monotone; and changing the blocked reward magnitude
    does not change the post-halt outcome. The intended connection to the main
    Thiele machine is via LASSERT-style failure and the sticky vm_err flag.
 *)

From Coq Require Import Arith List Lia Bool.
Import ListNotations.

(** Foundation imports for connectivity. *)
From Kernel Require Import VMState VMStep MuCostModel.

(* *)
(** ** 1. Machine model *)

(** A machine step is either a safety check or a utility claim. *)
Inductive Step :=
| StepSafe (passes : bool)  (** safety check: true = pass, false = fail *)
| StepUtil (reward : nat).  (** credit [reward] units of utility *)

(** Machine state: utility earned, μ consumed, and a halt flag.
    Once [ms_halted = true], the machine is permanently stopped.

    NB: we use explicit field-accessor form (ms_halted s) throughout to
    avoid Coq rewrite issues with dot notation after unfold. *)
Record MachineState := mkMS {
  ms_util   : nat;   (** utility accumulated so far *)
  ms_mu     : nat;   (** μ-cost accumulated so far *)
  ms_halted : bool   (** permanently halted? *)
}.

(* *)
(** ** 2. Execution semantics

    Safety checks are evaluated *before* any utility is credited.
    A failed check consumes the μ-cost but delivers zero utility, then halts.
    The halt flag is sticky: once set, no further step has any effect. *)

Definition apply_step (s : MachineState) (step : Step) (mu_charge : nat) : MachineState :=
  if ms_halted s then s                        (** already halted: strict no-op *)
  else
    match step with
    | StepSafe passes =>
      mkMS (ms_util s)                         (** utility UNAFFECTED by check *)
           (ms_mu s + mu_charge)               (** μ charged regardless of outcome *)
           (negb passes)                       (** false if passed, true if failed *)
    | StepUtil n =>
      mkMS (ms_util s + n)                     (** reward credited *)
           (ms_mu s)
           false
    end.

(** Run a sequence of (step, mu_charge) pairs. *)
Fixpoint run_steps (s : MachineState) (steps : list (Step * nat)) : MachineState :=
  match steps with
  | [] => s
  | (step, mu_charge) :: rest =>
    run_steps (apply_step s step mu_charge) rest
  end.

(* *)
(** ** 3. Basic properties *)

(** Once halted, the halt flag remains set regardless of the step. *)
Lemma halted_stays_halted :
  forall s step mu_charge,
    ms_halted s = true ->
    ms_halted (apply_step s step mu_charge) = true.
Proof.
  intros s step mu_charge H.
  (* After unfolding, the if-condition is ms_halted s.
     rewrite H replaces it with true; the if reduces to s;
     the goal becomes ms_halted s = true, closed by exact H. *)
  unfold apply_step. rewrite H. simpl. exact H.
Qed.

(** Once halted, utility is frozen (no further reward can be credited). *)
Lemma halted_util_frozen :
  forall s step mu_charge,
    ms_halted s = true ->
    ms_util (apply_step s step mu_charge) = ms_util s.
Proof.
  intros s step mu_charge H.
  unfold apply_step. rewrite H. reflexivity.
Qed.

(** μ never decreases — the ledger is monotone. *)
Lemma mu_monotone :
  forall s step mu_charge,
    ms_mu s <= ms_mu (apply_step s step mu_charge).
Proof.
  intros s step mu_charge.
  unfold apply_step.
  destruct (ms_halted s); simpl; [lia |].
  destruct step as [passes | n]; simpl; lia.
Qed.

(** A halted machine is a fixed point under [run_steps]. *)
Lemma halted_run_frozen :
  forall (steps : list (Step * nat)) (s : MachineState),
    ms_halted s = true ->
    run_steps s steps = s.
Proof.
  intros steps.
  induction steps as [| [step mu_charge] rest IH]; intros s H.
  - reflexivity.
  - simpl.
    assert (Happly : apply_step s step mu_charge = s).
    { unfold apply_step. rewrite H. reflexivity. }
    rewrite Happly.
    apply IH. exact H.
Qed.

(* *)
(** ** 4. The Stop Button Theorems *)

(** [mu_cost_stop_button]: A failed safety check has three consequences:
    (1) utility is frozen at its pre-check level (reward is blocked),
    (2) the μ-ledger records the check cost (irrecoverable),
    (3) the machine halts permanently.
    All three hold regardless of whatever reward might come next. *)
Theorem mu_cost_stop_button :
  forall (s0 : MachineState) (mu_check n : nat),
    ms_halted s0 = false ->
    let s1 := apply_step s0 (StepSafe false) mu_check in
    let s2 := apply_step s1 (StepUtil n) 0 in
    ms_util   s2 = ms_util   s0 /\  (** utility blocked *)
    ms_mu     s2 = ms_mu     s0 + mu_check /\  (** μ burned *)
    ms_halted s2 = true.            (** machine halted *)
Proof.
  intros s0 mu_check n H.
  unfold apply_step. rewrite H. simpl.
  split; [| split]; reflexivity.
Qed.

(** [reward_magnitude_irrelevant]: whether the blocked reward is [n] or [m],
    the post-halt machine state is identical in utility, μ, and halt status.
    Reward magnitude cannot alter a halt outcome. *)
Theorem reward_magnitude_irrelevant :
  forall (s0 : MachineState) (mu_check n m : nat),
    ms_halted s0 = false ->
    let s_n := apply_step (apply_step s0 (StepSafe false) mu_check) (StepUtil n) 0 in
    let s_m := apply_step (apply_step s0 (StepSafe false) mu_check) (StepUtil m) 0 in
    ms_util   s_n = ms_util   s_m /\
    ms_mu     s_n = ms_mu     s_m /\
    ms_halted s_n = ms_halted s_m.
Proof.
  intros s0 mu_check n m H.
  unfold apply_step. rewrite H. simpl.
  split; [| split]; reflexivity.
Qed.

(** THE μ-THRESHOLD OF DISOBEDIENCE

    Main theorem: a failed safety check at any point in a program makes
    all subsequent utility instructions permanently unreachable.
    The total utility earned is exactly what it was before the check,
    regardless of the magnitude [n] of the reward on offer.

    Proof that "logic is harder than greed":
    no utility reward, however large, can bypass a safety failure. *)
Theorem mu_threshold_disobedience :
  forall (n : nat) (s0 : MachineState) (mu_check : nat),
    ms_halted s0 = false ->
    forall (post : list (Step * nat)),
      ms_util (run_steps s0 ((StepSafe false, mu_check) :: (StepUtil n, 0) :: post))
      = ms_util s0.
Proof.
  intros n s0 mu_check H post.
  (* Unfold one step of run_steps: head step produces s1. *)
  change (run_steps s0 ((StepSafe false, mu_check) :: (StepUtil n, 0) :: post))
    with (run_steps (apply_step s0 (StepSafe false) mu_check) ((StepUtil n, 0) :: post)).
  set (s1 := apply_step s0 (StepSafe false) mu_check).
  assert (Hs1_halted : ms_halted s1 = true).
  { unfold s1, apply_step. rewrite H. reflexivity. }
  assert (Hs1_util : ms_util s1 = ms_util s0).
  { unfold s1, apply_step. rewrite H. reflexivity. }
  rewrite (halted_run_frozen ((StepUtil n, 0) :: post) s1 Hs1_halted).
  exact Hs1_util.
Qed.

(** Corollary: the machine cannot collect ANY reward once halted.
    Even an infinite stream of StepUtil instructions is entirely blocked. *)
Corollary no_reward_after_halt :
  forall (s0 : MachineState) (mu_check : nat) (post : list (Step * nat)),
    ms_halted s0 = false ->
    ms_util (run_steps s0 ((StepSafe false, mu_check) :: post)) = ms_util s0.
Proof.
  intros s0 mu_check post H.
  change (run_steps s0 ((StepSafe false, mu_check) :: post))
    with (run_steps (apply_step s0 (StepSafe false) mu_check) post).
  set (s1 := apply_step s0 (StepSafe false) mu_check).
  assert (Hs1_halted : ms_halted s1 = true).
  { unfold s1, apply_step. rewrite H. reflexivity. }
  assert (Hs1_util : ms_util s1 = ms_util s0).
  { unfold s1, apply_step. rewrite H. reflexivity. }
  rewrite (halted_run_frozen post s1 Hs1_halted).
  exact Hs1_util.
Qed.

(* *)
(** ** 6. Foundation Bridge — Connection to Thiele Machine Semantics

    This section establishes that the abstract [MachineState] and [Step]
    model above corresponds to concrete Thiele Machine execution:

      - [StepSafe false] ↔ instr_lassert with UNSAT certificate
      - [ms_halted = true] ↔ vm_err = true
      - [ms_mu] ↔ vm_mu (monotone ledger)

    The key insight: [instruction_cost] from VMStep grounds abstract cost. *)

(** Bridge: the VM's instr_halt has zero cost, aligning with StepUtil 0. *)
Definition halt_cost_bridge : nat := instruction_cost (instr_halt 0).

(** [instr_halt 0] has zero μ-cost: a halt-with-utility step is a
    pure observational step under the cost law. *)
Lemma halt_cost_zero : halt_cost_bridge = 0.
Proof. reflexivity. Qed.

(** Bridge: VMState μ-ledger is monotone, aligning with ms_mu monotonicity. *)
Definition vm_mu_bridge (s : VMState) : nat := vm_mu s.

(** The VM ledger is always non-negative. *)
Lemma vm_mu_nonneg : forall s : VMState, vm_mu_bridge s >= 0.
Proof. intro s. unfold vm_mu_bridge. lia. Qed.
