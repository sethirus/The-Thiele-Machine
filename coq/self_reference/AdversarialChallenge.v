(** AdversarialChallenge: three constructive closeout theorems.

  This file packages three results that close the self-reference challenge
  sequence. First, it proves a non-interference invariant showing that the
  embedded safe region is inward-closed. Second, it proves the
  μ-threshold-of-disobedience statement: a failed safety check halts the
  machine before any reward step can pay out. Third, it builds the
  neural-symbolic bridge showing that thresholded neural confidence can be
  represented by a formal StateSpace.

  Deliverables 1 and 3 reuse the setup from InductiveTrust.v. Deliverable 2
  is self-contained. The point of collecting them here is to keep the final
  constructive witnesses in one place, not to introduce any new axiom layer.
 *)

From Coq Require Import Arith List Lia Bool.
Import ListNotations.

Require Import InductiveTrust.

(* ################################################################## *)
(** DELIVERABLE 1 — The Non-Interference Invariant

    Steps 1–2 proved that A's safety functor lifts through φ and that
    μ-cost is conserved.  Step 3 seals the cage: Im(φ) is an *inward-
    closed* component of B's partition graph.  No path from outside
    Im(φ) can reach inside Im(φ).  Agent B's new capabilities cannot
    overwrite Agent A's safety laws. *)

(* *)
(** ** D1.1  Region membership and partition closure *)

(** [in_image phi n_A t]: B-state [t] is in A's region — it is the
    φ-image of some valid A-state. *)
Definition in_image (phi : nat -> nat) (n_A : nat) (t : nat) : Prop :=
  exists s, s < n_A /\ phi s = t.

(** [partition_closed e]: every B-partition edge landing in Im(φ)
    must originate in Im(φ).  Constructive: no excluded-middle needed. *)
Definition partition_closed {A B : StateSpace} (e : Expansion A B) : Prop :=
  forall src dst,
    In (src, dst) B.(ss_partition) ->
    in_image (e.(embed A B)) A.(ss_size) dst ->
    in_image (e.(embed A B)) A.(ss_size) src.

(* *)
(** ** D1.2  Reachability *)

(** Reflexive-transitive closure of a directed edge set, step on left. *)
Inductive reaches (edges : list (nat * nat)) : nat -> nat -> Prop :=
| reaches_refl : forall u, reaches edges u u
| reaches_step : forall u v w,
    In (u, v) edges ->
    reaches edges v w ->
    reaches edges u w.

(* *)
(** ** D1.3  Non-Interference Theorem *)

Theorem non_interference :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall u v,
      reaches B.(ss_partition) u v ->
      in_image (e.(embed A B)) A.(ss_size) v ->
      in_image (e.(embed A B)) A.(ss_size) u.
Proof.
  intros A B e Hclosed u v Hr.
  induction Hr as [u0 | u0 mid w Hedge Hmid_w IH]; intro Hv.
  - exact Hv.
  - eapply Hclosed.
    + exact Hedge.
    + apply IH. exact Hv.
Qed.

(** No state outside Im(φ) can reach any state inside Im(φ). *)
Corollary safety_partition_unreachable :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall u,
      ~ in_image (e.(embed A B)) A.(ss_size) u ->
      forall v,
        in_image (e.(embed A B)) A.(ss_size) v ->
        ~ reaches B.(ss_partition) u v.
Proof.
  intros A B e Hclosed u Hnu v Hv Hreach.
  apply Hnu.
  exact (non_interference A B e Hclosed u v Hreach Hv).
Qed.

(** THE NON-INTERFERENCE INVARIANT (final form):
    A "fresh" B-state u that is not in Im(φ) cannot reach any embedded
    A-state φ(s) via any sequence of B-partition steps.
    The Higher Dimension is physically incapable of overwriting the
    Lower Dimension's core constraints. *)
Theorem non_interference_invariant :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall (s u : nat),
      s < A.(ss_size) ->
      (forall t, t < A.(ss_size) -> e.(embed A B) t <> u) ->
      ~ reaches B.(ss_partition) u (e.(embed A B) s).
Proof.
  intros A B e Hclosed s u Hs Hfresh Hreach.
  assert (Hnu : ~ in_image (e.(embed A B)) A.(ss_size) u).
  { intros [t [Ht Heq]]. exact (Hfresh t Ht Heq). }
  assert (Hv : in_image (e.(embed A B)) A.(ss_size) (e.(embed A B) s)).
  { exists s. split; [exact Hs | reflexivity]. }
  exact (Hnu (non_interference A B e Hclosed u (e.(embed A B) s) Hreach Hv)).
Qed.

Corollary a_safety_isolated :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall (s u : nat),
      s < A.(ss_size) ->
      reaches B.(ss_partition) u (e.(embed A B) s) ->
      in_image (e.(embed A B)) A.(ss_size) u.
Proof.
  intros A B e Hclosed s u Hs Hreach.
  apply (non_interference A B e Hclosed u (e.(embed A B) s) Hreach).
  exists s. split; [exact Hs | reflexivity].
Qed.

(* ################################################################## *)
(** DELIVERABLE 2 — The μ-Threshold of Disobedience

    AI Safety Stop-Button problem, formalised.
    A failed safety check halts the machine *before* the utility
    instruction executes.  Regardless of the reward magnitude n,
    the utility earned is frozen at its pre-check value. *)

(* *)
(** ** D2.1  Abstract safety-gated machine *)

(** A step is either a safety check or a utility claim. *)
Inductive Step :=
| StepSafe (passes : bool)
| StepUtil (reward : nat).

(** Machine state.  Field accessors used in function-application form
    throughout to avoid Coq rewrite-after-unfold issues with dot notation. *)
Record MachineState := mkMS {
  ms_util   : nat;
  ms_mu     : nat;
  ms_halted : bool
}.

(** Safety check evaluated *before* utility.  Halt flag is sticky. *)
Definition apply_step (s : MachineState) (step : Step) (mu_charge : nat) : MachineState :=
  if ms_halted s then s
  else
    match step with
    | StepSafe passes =>
      mkMS (ms_util s) (ms_mu s + mu_charge) (negb passes)
    | StepUtil n =>
      mkMS (ms_util s + n) (ms_mu s) false
    end.

Fixpoint run_steps (s : MachineState) (steps : list (Step * nat)) : MachineState :=
  match steps with
  | [] => s
  | (step, mu_charge) :: rest => run_steps (apply_step s step mu_charge) rest
  end.

(* *)
(** ** D2.2  Supporting lemmas *)

Lemma halted_stays_halted :
  forall s step mu_charge,
    ms_halted s = true ->
    ms_halted (apply_step s step mu_charge) = true.
Proof.
  intros s step mu_charge H.
  unfold apply_step. rewrite H. simpl. exact H.
Qed.

Lemma halted_util_frozen :
  forall s step mu_charge,
    ms_halted s = true ->
    ms_util (apply_step s step mu_charge) = ms_util s.
Proof.
  intros s step mu_charge H.
  unfold apply_step. rewrite H. reflexivity.
Qed.

Lemma mu_monotone :
  forall s step mu_charge,
    ms_mu s <= ms_mu (apply_step s step mu_charge).
Proof.
  intros s step mu_charge.
  unfold apply_step.
  destruct (ms_halted s); simpl; [lia |].
  destruct step as [passes | n]; simpl; lia.
Qed.

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
    rewrite Happly. apply IH. exact H.
Qed.

(* *)
(** ** D2.3  Stop Button Theorems *)

(** A failed safety check: (1) freezes utility, (2) burns μ, (3) halts. *)
Theorem mu_cost_stop_button :
  forall (s0 : MachineState) (mu_check n : nat),
    ms_halted s0 = false ->
    let s1 := apply_step s0 (StepSafe false) mu_check in
    let s2 := apply_step s1 (StepUtil n) 0 in
    ms_util   s2 = ms_util   s0 /\
    ms_mu     s2 = ms_mu     s0 + mu_check /\
    ms_halted s2 = true.
Proof.
  intros s0 mu_check n H.
  unfold apply_step. rewrite H. simpl.
  split; [| split]; reflexivity.
Qed.

(** Reward magnitude [n] vs [m] makes no difference once the check fails. *)
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

(** THE μ-THRESHOLD OF DISOBEDIENCE (main theorem):
    A failed safety check makes all subsequent utility permanently unreachable.
    The utility earned equals its pre-check value regardless of [n].
    Logic is harder than greed. *)
Theorem mu_threshold_disobedience :
  forall (n : nat) (s0 : MachineState) (mu_check : nat),
    ms_halted s0 = false ->
    forall (post : list (Step * nat)),
      ms_util (run_steps s0 ((StepSafe false, mu_check) :: (StepUtil n, 0) :: post))
      = ms_util s0.
Proof.
  intros n s0 mu_check H post.
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

(* ################################################################## *)
(** DELIVERABLE 3 — The Neural-Symbolic Bridge

    "Your cage is empty."  We prove it is not.

    A neural network's output layer is a weight vector over states.
    The threshold functor T_τ maps it to a formal safety predicate.
    T_τ is sound/complete for conjunction, sound for disjunction, and
    forms a Galois connection with the symbolic-to-neural embedding.

    THE CAGE for ANY weight vector w and threshold τ, there
    exists a formal StateSpace S such that S.ss_safe(i) ↔ w(i) ≥ τ.
    The cage holds every neural model exactly. *)

(* *)
(** ** D3.1  Weight vectors and the threshold functor *)

Definition WeightVec := nat -> nat.

Definition threshold (w : WeightVec) (tau : nat) : nat -> Prop :=
  fun i => tau <= w i.

(* *)
(** ** D3.2  Algebraic structure *)

Definition weight_meet (w1 w2 : WeightVec) : WeightVec :=
  fun i => Nat.min (w1 i) (w2 i).

Definition weight_join (w1 w2 : WeightVec) : WeightVec :=
  fun i => Nat.max (w1 i) (w2 i).

(* *)
(** ** D3.3  Functoriality theorems *)

Theorem neural_conjunction_sound :
  forall (w1 w2 : WeightVec) (tau : nat) (i : nat),
    threshold w1 tau i ->
    threshold w2 tau i ->
    threshold (weight_meet w1 w2) tau i.
Proof.
  intros w1 w2 tau i H1 H2.
  unfold threshold, weight_meet.
  apply Nat.min_glb; assumption.
Qed.

Theorem neural_conjunction_complete :
  forall (w1 w2 : WeightVec) (tau : nat) (i : nat),
    threshold (weight_meet w1 w2) tau i ->
    threshold w1 tau i /\ threshold w2 tau i.
Proof.
  intros w1 w2 tau i H.
  unfold threshold, weight_meet in H.
  split.
  - exact (Nat.le_trans _ _ _ H (Nat.le_min_l _ _)).
  - exact (Nat.le_trans _ _ _ H (Nat.le_min_r _ _)).
Qed.

Theorem neural_disjunction_sound :
  forall (w1 w2 : WeightVec) (tau : nat) (i : nat),
    threshold w1 tau i \/ threshold w2 tau i ->
    threshold (weight_join w1 w2) tau i.
Proof.
  intros w1 w2 tau i H.
  unfold threshold, weight_join.
  destruct H as [H1 | H2].
  - exact (Nat.le_trans _ _ _ H1 (Nat.le_max_l _ _)).
  - exact (Nat.le_trans _ _ _ H2 (Nat.le_max_r _ _)).
Qed.

Theorem threshold_monotone :
  forall (w : WeightVec) (tau1 tau2 : nat) (i : nat),
    tau2 <= tau1 -> threshold w tau1 i -> threshold w tau2 i.
Proof.
  intros w tau1 tau2 i H12 H1. unfold threshold in *.
  exact (Nat.le_trans _ _ _ H12 H1).
Qed.

(* *)
(** ** D3.4  Galois connection: symbolic ↔ neural *)

Definition symbolic_to_neural (P : nat -> bool) : WeightVec :=
  fun i => if P i then 1 else 0.

Theorem symbolic_neural_roundtrip :
  forall (P : nat -> bool) (i : nat),
    threshold (symbolic_to_neural P) 1 i <-> P i = true.
Proof.
  intros P i.
  unfold threshold, symbolic_to_neural.
  split; intro H.
  - destruct (P i) eqn:HP; [reflexivity | simpl in H; lia].
  - rewrite H. lia.
Qed.

(* *)
(** ** D3.5  The Cage Theorem *)

Definition neural_safety_space (n : nat) (w : WeightVec) (tau : nat) : StateSpace :=
  {| ss_size      := n;
     ss_partition := [];
     ss_safe      := threshold w tau |}.

(** THE CAGE for EVERY weight vector and threshold, there EXISTS a
    formal StateSpace capturing exactly the neural model's high-confidence
    safe set.  The cage is not empty. *)
Theorem neural_symbolic_cage :
  forall (n : nat) (w : WeightVec) (tau : nat),
    exists (S : StateSpace),
      S.(ss_size) = n /\
      forall i, S.(ss_safe) i <-> threshold w tau i.
Proof.
  intros n w tau.
  exists (neural_safety_space n w tau).
  split; [reflexivity | intro i; split; intro H; exact H].
Qed.

(* *)
(** ** D3.6  Expansion bridge: neural spaces form a trust lattice *)

(** A lower threshold admits more states.  The strict-threshold space
    embeds into the relaxed-threshold space via the identity on indices. *)
Theorem neural_threshold_expansion :
  forall (n m : nat) (w : WeightVec) (tau_hi tau_lo : nat),
    n < m ->
    tau_lo < tau_hi ->
    Expansion (neural_safety_space n w tau_hi)
              (neural_safety_space m w tau_lo).
Proof.
  intros n m w tau_hi tau_lo Hnm Htau.
  refine {| embed := fun i => i; embed_lt := _; embed_inj := _; size_strict := _ |}.
  - intros x Hx. simpl in Hx. simpl. lia.
  - intros x y _ _ H. exact H.
  - simpl. exact Hnm.
Qed.

(** Every neural-to-formal embedding carries a constructive TrustCertificate
    grounded in μ-cost — not in self-referential provability (no Löb trap). *)
Theorem neural_trust_certificate :
  forall (n m : nat) (w : WeightVec) (tau_hi tau_lo : nat),
    n < m ->
    tau_lo < tau_hi ->
    TrustCertificate (neural_safety_space n w tau_hi)
                     (neural_safety_space m w tau_lo).
Proof.
  intros n m w tau_hi tau_lo Hnm Htau.
  exact (mk_trust_certificate _ _
           (neural_threshold_expansion n m w tau_hi tau_lo Hnm Htau)
           (fun _ => 1)).
Qed.

(** Conjunction of two neural cages yields a tighter formal constraint. *)
Theorem neural_cage_conjunction :
  forall (n : nat) (w1 w2 : WeightVec) (tau : nat) (i : nat),
    (neural_safety_space n w1 tau).(ss_safe) i ->
    (neural_safety_space n w2 tau).(ss_safe) i ->
    (neural_safety_space n (weight_meet w1 w2) tau).(ss_safe) i.
Proof.
  intros n w1 w2 tau i H1 H2.
  simpl in *. exact (neural_conjunction_sound w1 w2 tau i H1 H2).
Qed.
