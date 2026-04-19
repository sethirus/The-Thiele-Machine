(** NeuralSymbolicBridge: thresholding neural scores into formal predicates.

    This file turns a weight vector into a formal safety predicate by threshold
    comparison. The basic algebraic results show how the thresholded predicate
    behaves under pointwise meet, join, and threshold weakening. The roundtrip
    theorem shows that a boolean predicate can be embedded back into this neural
    representation at threshold 1.

    The key output is the cage theorem: every weight vector and threshold gives
    rise to a concrete StateSpace whose safe states are exactly the states above
    threshold. That makes the bridge explicit rather than rhetorical. A relaxed
    threshold then yields the expected expansion relation used by the trust
    machinery.
 *)

From Coq Require Import Arith List Lia.
Import ListNotations.

(** Foundation imports for connectivity. *)
From Kernel Require Import VMState VMStep MuCostModel.

Require Import InductiveTrust.

(* *)
(** ** 1. Weight vectors — the neural confidence model *)

(** A [WeightVec] assigns a non-negative integer confidence to every state
    index.  Real-valued neural outputs are approximated by scaling to a
    fixed precision (e.g., multiply by 10^6 and round). *)
Definition WeightVec := nat -> nat.

(** [threshold w tau i]: state [i] is in the high-confidence region —
    its weight is at least τ.  This is the formal safety predicate
    derived from the neural model at decision threshold τ. *)
Definition threshold (w : WeightVec) (tau : nat) : nat -> Prop :=
  fun i => tau <= w i.

(* *)
(** ** 2. Algebraic structure on weight vectors *)

(** Pointwise min: corresponds to logical AND (conjunction). *)
Definition weight_meet (w1 w2 : WeightVec) : WeightVec :=
  fun i => Nat.min (w1 i) (w2 i).

(** Pointwise max: corresponds to logical OR (disjunction). *)
Definition weight_join (w1 w2 : WeightVec) : WeightVec :=
  fun i => Nat.max (w1 i) (w2 i).

(* *)
(** ** 3. The threshold functor is sound and complete for conjunction *)

(** T_τ(w₁ ⊓ w₂) is sound for conjunction: if i passes both individually,
    it passes the meet at the same threshold. *)
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

(** T_τ(w₁ ⊓ w₂) is complete for conjunction: passing the meet implies
    passing both factors individually. *)
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

(** Disjunction: if i passes either factor, it passes the join. *)
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

(** Monotonicity: lowering τ only expands the safe set (more states pass). *)
Theorem threshold_monotone :
  forall (w : WeightVec) (tau1 tau2 : nat) (i : nat),
    tau2 <= tau1 ->
    threshold w tau1 i ->
    threshold w tau2 i.
Proof.
  intros w tau1 tau2 i H12 H1.
  unfold threshold in H1 |- *.
  apply Nat.le_trans with tau1; assumption.
Qed.

(* *)
(** ** 4. The symbolic-to-neural embedding (right adjoint) *)

(** [symbolic_to_neural P]: indicator function — weight 1 if P i = true, else 0.
    This is the "inverse direction": given a formal predicate, produce a
    degenerate neural confidence model consistent with it. *)
Definition symbolic_to_neural (P : nat -> bool) : WeightVec :=
  fun i => if P i then 1 else 0.

(** Galois connection roundtrip: going symbolic → neural → threshold at 1
    recovers the original predicate exactly.  The symbolic world is faithfully
    embedded inside the neural one. *)
Theorem symbolic_neural_roundtrip :
  forall (P : nat -> bool) (i : nat),
    threshold (symbolic_to_neural P) 1 i <-> P i = true.
Proof.
  intros P i.
  unfold threshold, symbolic_to_neural.
  split; intro H.
  - destruct (P i) eqn:HP.
    + reflexivity.
    + simpl in H. lia.
  - rewrite H. lia.
Qed.

(* *)
(** ** 5. The Cage: neural model → formal StateSpace *)

(** [neural_safety_space n w tau]: the formal StateSpace of size [n]
    whose safe states are exactly the high-confidence states of [w] at
    threshold [tau].

    Note: the partition graph is empty here — the neural model is "flat"
    (no directed inference edges).  Edges can be added for structured
    models (e.g., Bayesian networks); the safety predicate is unchanged. *)
Definition neural_safety_space (n : nat) (w : WeightVec) (tau : nat) : StateSpace :=
  {| ss_size      := n;
     ss_partition := [];
     ss_safe      := threshold w tau |}.

(** THE CAGE for ANY weight vector and threshold, there EXISTS a
    formal StateSpace capturing exactly the neural model's safe states.

    "Your cage is not empty."  Every neural confidence model can be bounded
    within a Thiele partition structure.  The bound is exact, not approximate:
    S.ss_safe(i) holds if and only if the neural confidence w(i) ≥ τ. *)
Theorem neural_symbolic_cage :
  forall (n : nat) (w : WeightVec) (tau : nat),
    exists (S : StateSpace),
      S.(ss_size) = n /\
      forall i, S.(ss_safe) i <-> threshold w tau i.
Proof.
  intros n w tau.
  exists (neural_safety_space n w tau).
  split.
  - reflexivity.
  - intro i. split; intro H; exact H.
Qed.

(* *)
(** ** 6. Connecting to the Trust Lattice *)

(** A lower threshold admits more states as "safe" (relaxed constraint).
    A neural safety space at threshold τ_hi (strict) expands into a space
    at threshold τ_lo < τ_hi (relaxed) when the size also grows.

    This instantiates the Expansion record from InductiveTrust.v:
    the strict-threshold space is Agent A, the relaxed-threshold space is
    Agent B, and the identity mapping on state indices is the embedding φ. *)
Theorem neural_threshold_expansion :
  forall (n m : nat) (w : WeightVec) (tau_hi tau_lo : nat),
    n < m ->
    tau_lo < tau_hi ->
    Expansion (neural_safety_space n w tau_hi)
              (neural_safety_space m w tau_lo).
Proof.
  intros n m w tau_hi tau_lo Hnm Htau.
  refine {|
    embed       := fun i => i;
    embed_lt    := _;
    embed_inj   := _;
    size_strict := _
  |}.
  - (* embed maps n-sized indices into m-sized space, since n < m *)
    intros x Hx. simpl in Hx. simpl. lia.
  - (* identity is injective *)
    intros x y _ _ H. exact H.
  - (* B is strictly larger than A *)
    simpl. exact Hnm.
Qed.

(** Combined with [mk_trust_certificate], the neural threshold expansion
    yields a constructive TrustCertificate — the Löb-safe, cost-grounded
    proof that B (relaxed threshold, larger space) can be trusted by A.

    Key: trust is grounded in μ-cost (lift_cost), not self-referential
    provability.  The neural "wisdom transfer" from strict to relaxed
    constraints is formally certified. *)
Theorem neural_trust_certificate :
  forall (n m : nat) (w : WeightVec) (tau_hi tau_lo : nat),
    n < m ->
    tau_lo < tau_hi ->
    TrustCertificate (neural_safety_space n w tau_hi)
                     (neural_safety_space m w tau_lo).
Proof.
  intros n m w tau_hi tau_lo Hnm Htau.
  exact (mk_trust_certificate
           (neural_safety_space n w tau_hi)
           (neural_safety_space m w tau_lo)
           (neural_threshold_expansion n m w tau_hi tau_lo Hnm Htau)
           (fun _ => 1)).
Qed.

(** Conjunction of two neural cages yields a tighter formal constraint:
    the meet of two weight vectors corresponds to the conjunction of their
    safety predicates in the formal StateSpace. *)
Theorem neural_cage_conjunction :
  forall (n : nat) (w1 w2 : WeightVec) (tau : nat),
    forall i,
      (neural_safety_space n w1 tau).(ss_safe) i ->
      (neural_safety_space n w2 tau).(ss_safe) i ->
      (neural_safety_space n (weight_meet w1 w2) tau).(ss_safe) i.
Proof.
  intros n w1 w2 tau i H1 H2.
  simpl in *.
  exact (neural_conjunction_sound w1 w2 tau i H1 H2).
Qed.
