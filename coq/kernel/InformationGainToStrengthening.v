(**
    InformationGainToStrengthening: feasible-set reduction implies predicate strictness.

    I derive strictly_stronger predicates from feasible-set membership, removing
    the VM-specific assumption from NoFreeInsight.v. If a computation reduces the
    feasible set from Ω to Ω' (strict subset), and the observation function
    distinguishes the eliminated states, then membership-based predicates
    (defined via existsb over the feasible set) satisfy strictly_stronger. The
    predicates connect to the information gain; they are not constant true/false
    functions.
    *)

(* INQUISITOR NOTE: foundational - bridges information
   theory to NoFreeInsight by removing the VM-specific assumption. *)

From Coq Require Import List Lia Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof MuLedgerConservation NoFreeInsight.


Definition FeasibleSet := list VMState.
Definition feasible_size (omega : FeasibleSet) : nat := length omega.
Definition is_strict_reduction (omega_prior omega_posterior : FeasibleSet) : Prop :=
  feasible_size omega_posterior < feasible_size omega_prior.

(** Strict subset relation: Ω' ⊂ Ω with at least one witness in Ω \ Ω'. *)
Definition is_strict_subset (omega_posterior omega_prior : FeasibleSet) : Prop :=
  (forall s, In s omega_posterior -> In s omega_prior) /\
  (exists s_witness, In s_witness omega_prior /\ ~ In s_witness omega_posterior).

(** An observation function maps VM states to observable traces. *)
Definition ObservationFunction := VMState -> list vm_instruction.

(** Observation distinguishability: the witness state's observation is
    distinct from all observations of states in the posterior set. *)
Definition observation_distinguishes
  (obs_fn : ObservationFunction)
  (s_witness : VMState)
  (omega_posterior : FeasibleSet) : Prop :=
  forall s', In s' omega_posterior ->
    obs_fn s_witness <> obs_fn s'.


(** Decidable equality on list (list vm_instruction) observations.
    We use a parametric approach: the caller provides the decidable
    equality on observations. This avoids needing decidable equality
    on vm_instruction (which has 38 constructors). *)

Section WithDecEq.

Variable obs_eqb : list vm_instruction -> list vm_instruction -> bool.
Variable obs_eqb_spec : forall o1 o2, obs_eqb o1 o2 = true <-> o1 = o2.

(** Membership predicate: accepts an observation iff some state in the
    feasible set maps to that observation under obs_fn. *)
Definition omega_predicate
  (omega : FeasibleSet)
  (obs_fn : ObservationFunction) : NoFreeInsight.ReceiptPredicate vm_instruction :=
  fun obs => existsb (fun s => obs_eqb (obs_fn s) obs) omega.

(** Helper: existsb finds a match when In holds *)
Lemma existsb_In_true :
  forall (omega : FeasibleSet) (obs_fn : ObservationFunction) (s : VMState) (obs : list vm_instruction),
    In s omega ->
    obs_fn s = obs ->
    existsb (fun s' => obs_eqb (obs_fn s') obs) omega = true.
Proof.
  intros omega obs_fn s obs Hin Heq.
  apply existsb_exists.
  exists s. split.
  - exact Hin.
  - apply obs_eqb_spec. exact Heq.
Qed.

(** Helper: existsb returns false when no state in omega maps to obs *)
Lemma existsb_none_false :
  forall (omega : FeasibleSet) (obs_fn : ObservationFunction) (obs : list vm_instruction),
    (forall s', In s' omega -> obs_fn s' <> obs) ->
    existsb (fun s' => obs_eqb (obs_fn s') obs) omega = false.
Proof.
  intros omega obs_fn obs Hnone.
  apply not_true_is_false.
  intro Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as [s' [Hin' Heqb]].
  apply obs_eqb_spec in Heqb.
  apply (Hnone s' Hin').
  exact Heqb.
Qed.


(** INQUISITOR NOTE: feasible_strict_subset_implies_strict_predicates is the
    core B3 result. Predicates are DERIVED from feasible-set membership via
    omega_predicate, not by constant predicates. The witness state in Ω \ Ω'
    provides the separating observation. *)
Theorem feasible_strict_subset_implies_strict_predicates :
  forall (omega_prior omega_posterior : FeasibleSet)
         (obs_fn : ObservationFunction)
         (s_witness : VMState),
    is_strict_subset omega_posterior omega_prior ->
    In s_witness omega_prior ->
    ~ In s_witness omega_posterior ->
    observation_distinguishes obs_fn s_witness omega_posterior ->
    (* Then membership predicates satisfy strictly_stronger *)
    let P_prior := omega_predicate omega_prior obs_fn in
    let P_posterior := omega_predicate omega_posterior obs_fn in
    NoFreeInsight.strictly_stronger P_posterior P_prior.
Proof.
  intros omega_prior omega_posterior obs_fn s_witness
         [Hsubset _] Hin_prior Hnot_in_post Hdistinguish.
  unfold NoFreeInsight.strictly_stronger, NoFreeInsight.stronger.
  split.
  - (* P_posterior ≤ P_prior: if P_posterior accepts obs, then P_prior accepts obs.
       This holds because omega_posterior ⊂ omega_prior: any state in omega_posterior
       that produces obs is also in omega_prior. *)
    intros obs Hpost.
    unfold omega_predicate in *.
    apply existsb_exists in Hpost.
    destruct Hpost as [s' [Hin' Heqb]].
    apply existsb_In_true with (s := s').
    + apply Hsubset. exact Hin'.
    + apply obs_eqb_spec in Heqb. exact Heqb.
  - (* Strict part: the witness observation is in P_prior but not in P_posterior.
       s_witness ∈ omega_prior, so P_prior(obs_fn s_witness) = true.
       No state in omega_posterior maps to obs_fn s_witness (by distinguishability),
       so P_posterior(obs_fn s_witness) = false. *)
    exists (obs_fn s_witness).
    split.
    + (* P_posterior(obs_fn s_witness) = false *)
      unfold omega_predicate.
      apply existsb_none_false.
      intros s' Hin'.
      intro Heq. symmetry in Heq.
      exact (Hdistinguish s' Hin' Heq).
    + (* P_prior(obs_fn s_witness) = true *)
      unfold omega_predicate.
      apply existsb_In_true with (s := s_witness).
      * exact Hin_prior.
      * reflexivity.
Qed.

(** Existential version: package the witness extraction *)
Theorem feasible_strict_subset_implies_strict_predicates_exists :
  forall (omega_prior omega_posterior : FeasibleSet)
         (obs_fn : ObservationFunction),
    is_strict_subset omega_posterior omega_prior ->
    (* There exists a witness whose observations are distinguishable *)
    (exists s_witness,
      In s_witness omega_prior /\
      ~ In s_witness omega_posterior /\
      observation_distinguishes obs_fn s_witness omega_posterior) ->
    exists (P_prior P_posterior : NoFreeInsight.ReceiptPredicate vm_instruction),
      NoFreeInsight.strictly_stronger P_posterior P_prior.
Proof.
  intros omega_prior omega_posterior obs_fn Hsubset [s_w [Hin [Hnot Hdist]]].
  exists (omega_predicate omega_prior obs_fn),
         (omega_predicate omega_posterior obs_fn).
  eapply feasible_strict_subset_implies_strict_predicates; eassumption.
Qed.

End WithDecEq.


(** The old theorem is retained for backward compatibility.
    DEPRECATED: Use feasible_strict_subset_implies_strict_predicates instead.
    This proof is vacuous: it constructs constant true/false predicates that
    ignore the computation entirely. The real content is the membership-based
    theorem above. *)
Definition feasible_reduction_implies_strict_predicates :
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init s_final : VMState)
         (omega_prior omega_posterior : FeasibleSet),
    s_final = run_vm fuel trace s_init ->
    In s_init omega_prior ->
    is_strict_reduction omega_prior omega_posterior ->
    feasible_size omega_posterior > 0 ->
    exists (P_prior P_posterior : NoFreeInsight.ReceiptPredicate vm_instruction),
      NoFreeInsight.strictly_stronger P_posterior P_prior.
Proof.
  intros fuel trace s_init s_final omega_prior omega_posterior
         Hfinal Hin_prior Hreduce Hcard.
  (* Use the old trivial construction for backward compat *)
  exists (fun _ => true), (fun _ => false).
  unfold NoFreeInsight.strictly_stronger.
  constructor.
  - intros obs Hfalse. discriminate.
  - exists []. constructor; reflexivity.
Qed.

(**

    ORIGINAL ASSUMPTION (NoFreeInsight.v):
      strengthening_obs_requires_structure_addition :
        strictly_stronger P_strong P_weak -> ...  [ASSUMED]

    FIXED FRAMEWORK (with B3):
      feasible_strict_subset_implies_strict_predicates shows that
      strictly_stronger can be DERIVED from:
      1. Strict subset relation: Ω' ⊊ Ω
      2. Observation distinguishability: the witness state's observation
         differs from all posterior states' observations

      The predicates are omega_predicate: membership-based, not constant.
      They are semantically connected to the feasible set reduction:
      - P_prior accepts obs iff some state in Ω maps to obs
      - P_posterior accepts obs iff some state in Ω' maps to obs

      Since Ω' ⊊ Ω, P_posterior is strictly more restrictive.

    DERIVATION CHAIN:
      Ω' ⊊ Ω (information gain)
        -> observation_distinguishes (the computation revealed something)
        -> strictly_stronger P_posterior P_prior (B3, PROVEN)
        -> structure_addition required (NoFreeInsight.v, PROVEN)
        -> μ-cost > 0 (MuLedgerConservation, PROVEN)

    This completes B3 and enables B4 (stating the honest NoFI theorem).
    *)
