(** * NonAdaptiveLowerBound: unconditional lower bound for non-adaptive SAT

    [MuComplexity.v] expresses the structural-advantage gap as
    arithmetic on declared cost constants: [blind_sat_steps k := 4^k]
    and [sighted_sat_steps k := 2 * 2^k]. That file's header is
    honest about scope — the separation is at the witness level, not a
    complexity-class lower bound. This file lifts the [4^k] constant
    from a declared cost to a worst-case theorem.

    ** What is proven here

    A non-adaptive SAT decider commits in advance to a list of probe
    assignments, observes the formula's value at each probe, and
    decides SAT/UNSAT based only on the observation vector. The
    headline theorem proves that any such decider that is correct on
    every Boolean predicate over n-bit assignments must probe every
    assignment in [0, 2^n). Hence [length probes >= 2^n],
    unconditionally.

    Specialised to factored 2k-bit SAT, this gives the
    [4^k = 2^(2k)] lower bound that [blind_sat_steps k] declares. The
    constant is no longer a declared cost; it is a worst-case
    theorem.

    What is NOT proven here
    -----------------------
    - This is a lower bound for *non-adaptive* solvers only.  Adaptive
      solvers (DPLL, CDCL) can do much better in practice.  The bound for
      arbitrary blind adaptive solvers in the Thiele VM remains M4b in
      [CRITIQUE_REMEDIATION.md].
    - The matching upper bound (a sighted Thiele program achieving 2*2^k
      probes with 1 μ paid for the factorization CERTIFY) is implicit in
      `sighted_sat_steps` but is not constructed inside the VM here.
*)

From Kernel Require Import FiniteInformation.
From Kernel Require Import MuComplexity.
From Kernel Require Import MuCostModel.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** The cost-foundation connection: this file's lower bounds match the
    `blind_sat_steps` constant declared in [MuComplexity.v].  Until this
    file, that constant was a chosen number; now it is the worst-case
    trace length any non-adaptive solver must pay. *)

(** A Boolean predicate on the n-bit assignment space, encoded as a
    function from nat indices to bool.  The "n-bit" structure is implicit:
    the predicate is meaningful on indices in [0, 2^n).  For any index
    outside that range the predicate's value is irrelevant to SAT. *)
Definition Predicate := nat -> bool.

(** SAT predicate: there is some assignment in [0, 2^n) where phi is true. *)
Definition is_sat (n : nat) (phi : Predicate) : bool :=
  existsb phi (seq 0 (2 ^ n)).

(** A non-adaptive decider is a fixed list of probes and a decision function
    that operates only on the observation vector.  No adaptivity allowed. *)
Record NonAdaptiveDecider := mk_nad {
  nad_probes : list nat;
  nad_decide : list bool -> bool
}.

(** [nad_run]: execute the non-adaptive decider against a predicate. *)
Definition nad_run (D : NonAdaptiveDecider) (phi : Predicate) : bool :=
  nad_decide D (map phi (nad_probes D)).

(** Correctness: the decider matches the SAT predicate on every input. *)
Definition nad_correct (n : nat) (D : NonAdaptiveDecider) : Prop :=
  forall phi : Predicate, nad_run D phi = is_sat n phi.

(** ** The adversary witness.

    For each candidate satisfying assignment a, we construct a predicate
    phi_a whose unique satisfying point in [0, 2^n) is a (assuming a is
    in range).  These are the formulas the adversary uses to force the
    solver to probe every assignment. *)

Definition phi_singleton (a : nat) : Predicate :=
  fun v => Nat.eqb v a.

Lemma phi_singleton_sat_self : forall a, phi_singleton a a = true.
Proof.
  intros a. unfold phi_singleton. apply Nat.eqb_eq. reflexivity.
Qed.

Lemma phi_singleton_others_false :
  forall a v, v <> a -> phi_singleton a v = false.
Proof.
  intros a v Hne. unfold phi_singleton.
  apply Nat.eqb_neq. exact Hne.
Qed.

Lemma is_sat_phi_singleton :
  forall n a, a < 2 ^ n -> is_sat n (phi_singleton a) = true.
Proof.
  intros n a Hlt. unfold is_sat.
  apply existsb_exists. exists a. split.
  - apply in_seq. lia.
  - apply phi_singleton_sat_self.
Qed.

(** The all-false predicate. *)
Definition phi_zero : Predicate := fun _ => false.

Lemma is_sat_phi_zero : forall n, is_sat n phi_zero = false.
Proof.
  intros n. unfold is_sat, phi_zero.
  induction (seq 0 (2 ^ n)) as [| x rest IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(** ** The lower-bound theorems. *)

(** [non_adaptive_must_probe_every_assignment]: if a non-adaptive decider
    is correct, every assignment in [0, 2^n) must appear in its probe list.

    Proof: suppose some a in range is missing.  Then on the singleton
    predicate phi_a, every probe maps to false (since each probe ≠ a),
    giving the same observation vector as phi_zero.  But phi_a is SAT
    while phi_zero is UNSAT — contradiction. *)
Theorem non_adaptive_must_probe_every_assignment :
  forall (n : nat) (D : NonAdaptiveDecider),
    nad_correct n D ->
    forall a, a < 2 ^ n -> In a (nad_probes D).
Proof.
  intros n D Hcorrect a Hlt.
  destruct (in_dec Nat.eq_dec a (nad_probes D)) as [Hin | Hnotin]; auto.
  exfalso.
  pose proof (Hcorrect (phi_singleton a)) as Heq_sat.
  pose proof (Hcorrect phi_zero)             as Heq_zero.
  rewrite is_sat_phi_singleton in Heq_sat by exact Hlt.
  rewrite is_sat_phi_zero      in Heq_zero.
  unfold nad_run in Heq_sat, Heq_zero.
  assert (Hmaps_eq : map (phi_singleton a) (nad_probes D)
                   = map phi_zero          (nad_probes D)).
  { apply map_ext_in. intros p Hp_in.
    assert (Hpne : p <> a).
    { intros Heq. subst p. contradiction. }
    rewrite phi_singleton_others_false by exact Hpne. reflexivity. }
  rewrite Hmaps_eq in Heq_sat.
  rewrite Heq_sat in Heq_zero.
  discriminate.
Qed.

(** [non_adaptive_sat_lower_bound]: corollary in length form.

    A correct non-adaptive decider on n-bit assignments has a probe list
    of length at least 2^n.  Even with possible duplicates in the probe
    list, the distinct-elements count is bounded below by the size of
    the assignment space. *)
Theorem non_adaptive_sat_lower_bound :
  forall (n : nat) (D : NonAdaptiveDecider),
    nad_correct n D ->
    length (nodup Nat.eq_dec (nad_probes D)) >= 2 ^ n.
Proof.
  intros n D Hcorrect.
  assert (Hincl : forall a : nat,
            In a (seq 0 (2 ^ n)) ->
            In a (nodup Nat.eq_dec (nad_probes D))).
  { intros a Ha.
    apply nodup_In.
    apply in_seq in Ha.
    apply (non_adaptive_must_probe_every_assignment n D Hcorrect a).
    lia. }
  assert (Hincl_l : incl (seq 0 (2 ^ n)) (nodup Nat.eq_dec (nad_probes D))).
  { intros x Hx. apply Hincl. exact Hx. }
  pose proof
    (NoDup_incl_length (seq_NoDup (2 ^ n) 0) Hincl_l) as Hlen.
  rewrite seq_length in Hlen. lia.
Qed.

(** Length of the raw probe list is at least the length of its nodup
    deduplication, so the same lower bound applies to the raw list. *)
Theorem non_adaptive_sat_raw_length_lower_bound :
  forall (n : nat) (D : NonAdaptiveDecider),
    nad_correct n D ->
    length (nad_probes D) >= 2 ^ n.
Proof.
  intros n D Hcorrect.
  apply Nat.le_trans
    with (m := length (nodup Nat.eq_dec (nad_probes D))).
  - apply non_adaptive_sat_lower_bound. exact Hcorrect.
  - induction (nad_probes D) as [| x xs IH]; simpl; auto.
    destruct (in_dec Nat.eq_dec x xs); simpl; lia.
Qed.

(** ** Specialization to factored SAT.

    A factored 2k-bit instance φ = φ₁(x) ∧ φ₂(y) lives over the joint
    assignment space of size 2^(2k) = 4^k.  A non-adaptive decider that
    must work on every Boolean predicate over those 2k bits — including
    the singleton predicates the adversary uses — needs at least 4^k
    probes.

    This is the unconditional version of `blind_sat_steps k = 4^k`. *)
Lemma two_pow_2k_eq_4_pow_k : forall k : nat, 2 ^ (2 * k) = 4 ^ k.
Proof.
  induction k as [| k' IH].
  - reflexivity.
  - replace (2 * S k') with (S (S (2 * k'))) by lia.
    change (2 ^ S (S (2 * k'))) with (2 * (2 * 2 ^ (2 * k'))).
    change (4 ^ S k') with (4 * 4 ^ k').
    rewrite <- IH. lia.
Qed.

Theorem non_adaptive_factored_sat_4_k_lower_bound :
  forall (k : nat) (D : NonAdaptiveDecider),
    nad_correct (2 * k) D ->
    length (nad_probes D) >= 4 ^ k.
Proof.
  intros k D Hcorrect.
  pose proof (non_adaptive_sat_raw_length_lower_bound (2 * k) D Hcorrect) as Hlb.
  rewrite <- two_pow_2k_eq_4_pow_k. exact Hlb.
Qed.

(** ** Bridge to the cost foundation: [blind_sat_steps] from [MuComplexity.v].

    The constant [MuComplexity.blind_sat_steps k = 4^k] declared the cost of
    truth-table enumeration on factored 2k-bit SAT.  Until this file, that
    constant was a chosen cost.  This corollary proves it is in fact the
    worst-case probe-list length any non-adaptive solver must reach — a
    formal lower bound, not a chosen cost.  This closes the M4a half of
    the structural-advantage scope-up gap. *)
Corollary non_adaptive_matches_blind_sat_steps :
  forall (k : nat) (D : NonAdaptiveDecider),
    nad_correct (2 * k) D ->
    length (nad_probes D) >= MuComplexity.blind_sat_steps k.
Proof.
  intros k D Hcorrect.
  unfold MuComplexity.blind_sat_steps.
  apply non_adaptive_factored_sat_4_k_lower_bound. exact Hcorrect.
Qed.

(** Existence of the cost-bearing connection: the result lives inside
    the framework where μ-cost is the resource being counted.  A
    non-adaptive solver's trace length is a lower bound on its total
    cost (each probe is at least one instruction).  Any Thiele VM
    program implementing non-adaptive factored-SAT decision must
    therefore execute at least 4^k = `blind_sat_steps k` instructions
    in the worst case. *)
Theorem non_adaptive_thiele_program_cost_lower_bound :
  forall (k : nat) (D : NonAdaptiveDecider),
    nad_correct (2 * k) D ->
    (* Any one-cost-per-probe pricing of the probe trace gives a
       trace cost at least 4^k. *)
    forall (cost_per_probe : nat),
      cost_per_probe >= 1 ->
      cost_per_probe * length (nad_probes D) >= 4 ^ k.
Proof.
  intros k D Hcorrect cost Hcost.
  pose proof (non_adaptive_factored_sat_4_k_lower_bound k D Hcorrect) as Hlb.
  nia.
Qed.
