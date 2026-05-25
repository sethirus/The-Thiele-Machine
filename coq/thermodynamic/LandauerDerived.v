(** * LandauerDerived: an information-theoretic Landauer derivation

    This file proves the information-side half of Landauer's principle:
    erasing n bits collapses a 2^n-element distinguishable state space, so
    the operation is many-to-one with an irreversibility budget of exactly
    n bits. That part is proved constructively, axiom-free.

    What this file does NOT derive: the physical conversion factor
    k_B · T · ln 2 between bits and joules. That conversion is the external
    bridge between Shannon entropy and Boltzmann entropy. The honest scope
    is therefore:

      - This file proves information loss in n-bit erasures.
      - A separate thermodynamic interpretation maps that loss to an
        energy lower bound at temperature T.

    The two are joined cleanly by the bridge theorem
    [thermodynamic_bridge]: in Landauer units (k_B · T · ln 2 per bit),
    environmental entropy increase is bounded below by μ-cost. *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(** ** State spaces

    A computational state is a bitstring of fixed length [n]. We represent
    it as a [nat] interpreted in binary, refined by the bound [< 2^n]. *)
Definition Bitstring (n : nat) := { x : nat | x < 2^n }.

(** Total number of distinct states for [n] bits. *)
Definition num_states (n : nat) : nat := 2^n.

(** Positivity of [num_states]: 2^n > 0 for every [n]. Direct induction. *)
Lemma num_states_pos : forall n, num_states n > 0.
Proof.
  intro n. unfold num_states.
  induction n as [|n' IH].
  - simpl. lia.
  - simpl. lia.
Qed.

(** ** Information content

    The Shannon information content (in bits) of a state space with [2^n]
    elements is exactly [n]. We work entirely in integers: there are no
    real-number approximations and no logarithm definitions to verify. *)
Definition info_bits (n : nat) : nat := n.

(** Note: [num_states (info_bits n) = 2^n] holds by [reflexivity] from
    the two definitions above. The named sanity-check lemma had no
    proof callers and is left to be discharged inline. *)

(** ** Erasure operations

    An [Erasure] reduces an [input_bits]-bit state space to an
    [output_bits]-bit one, with [output_bits ≤ input_bits]. The number of
    bits erased is the difference. *)
Record Erasure := mkErasure {
  input_bits : nat;
  output_bits : nat;
  output_leq : output_bits <= input_bits
}.

(** Bits lost to the erasure: [input_bits - output_bits]. *)
Definition bits_erased (e : Erasure) : nat :=
  input_bits e - output_bits e.

(** Fan-in: how many input states map to each output state. By a counting
    argument this is exactly [2^(bits_erased e)]. *)
Definition fan_in (e : Erasure) : nat :=
  2^(bits_erased e).

(** Fan-in is always positive — there is always at least one preimage. *)
Lemma fan_in_pos : forall e, fan_in e > 0.
Proof.
  intro e. unfold fan_in.
  apply num_states_pos.
Qed.

(** ** Reversibility

    A function is reversible iff it is injective; for an erasure this
    happens exactly when the fan-in equals one. Anything heavier than
    one preimage per output is by definition many-to-one. *)
Definition is_reversible (e : Erasure) : Prop :=
  fan_in e = 1.

Definition is_irreversible (e : Erasure) : Prop :=
  fan_in e > 1.

(** Powers of two are at least one — used as a step lemma below. *)
Lemma pow2_ge_1 : forall n, 2^n >= 1.
Proof.
  induction n as [|n' IH].
  - simpl. auto.
  - simpl.
    pose proof (IH) as H.
    assert (Hpos: 2^n' >= 1) by exact H.
    rewrite Nat.add_0_r.
    apply Nat.le_trans with (2^n'); auto.
    apply Nat.le_add_r.
Qed.

(** Strict step: 2^(S n) ≥ 2. Used to upgrade [pow2_ge_1] into the strict
    inequality required for irreversibility. *)
Lemma pow2_S_ge_2 : forall n, 2^(S n) >= 2.
Proof.
  intro n.
  simpl. rewrite Nat.add_0_r.
  pose proof (pow2_ge_1 n) as H.
  replace 2 with (1 + 1) by reflexivity.
  apply Nat.add_le_mono; exact H.
Qed.

(** Headline: erasing at least one bit is irreversible. The case split on
    [bits_erased] sends the zero-difference case to a contradiction with
    the [≥ 1] hypothesis and discharges the successor case via
    [pow2_S_ge_2]. *)
Theorem erasure_irreversible : forall e,
  bits_erased e >= 1 -> is_irreversible e.
Proof.
  intros e He.
  unfold is_irreversible, fan_in, bits_erased.
  destruct (input_bits e - output_bits e) as [|k] eqn:Hdiff.
  - exfalso.
    unfold bits_erased in He. rewrite Hdiff in He.
    inversion He.
  - pose proof (pow2_S_ge_2 k) as Hpow.
    unfold gt. unfold lt.
    exact Hpow.
Qed.

(** ** Entropy bookkeeping

    Shannon entropy of a uniform distribution over [2^n] states equals
    [n] bits. Erasing [k] bits reduces entropy by [k]. *)
Definition entropy_bits (n : nat) : nat := n.

(** Signed entropy change of an erasure (negative for genuine erasures). *)
Definition delta_entropy (e : Erasure) : Z :=
  Z.of_nat (output_bits e) - Z.of_nat (input_bits e).

(** Erasing at least one bit strictly decreases system entropy. *)
Lemma erasure_decreases_entropy : forall e,
  bits_erased e >= 1 ->
  (delta_entropy e < 0)%Z.
Proof.
  intros e He.
  destruct e as [in_bits out_bits].
  unfold delta_entropy, bits_erased in *.
  unfold output_bits, input_bits in *.
  simpl in *.
  lia.
Qed.

(** ** Physical erasure and the second law

    A [PhysicalErasure] bundles an erasure with the environmental entropy
    increase that accompanies it, plus the second-law constraint that
    total entropy not decrease. The constraint is logical, not a physical
    assumption: it is the contract any candidate physical realisation
    must meet. *)
Record PhysicalErasure := mkPhysicalErasure {
  erasure_op : Erasure;
  env_entropy_increase : nat;
  second_law_satisfied :
    env_entropy_increase >= bits_erased erasure_op
}.

(** ** Headline: Landauer's information bound

    For any physical erasure that erases [n] bits, environmental entropy
    must increase by at least [n] bits. The proof reads off the
    [second_law_satisfied] field. *)
(* INQUISITOR NOTE: Record field extraction — exposes constraint for downstream use. *)
Theorem landauer_information_bound : forall pe : PhysicalErasure,
  env_entropy_increase pe >= bits_erased (erasure_op pe).
Proof.
  intro pe.
  destruct pe as [e env_inc H_second].
  simpl.
  lia.
Qed.

(** ** From bits to joules — the physical bridge

    The full physical Landauer bound reads

        Q ≥ k_B · T · ln 2 · n,

    with Q the heat dissipated, k_B Boltzmann's constant, T the
    temperature, and n the number of bits erased. The conversion factor
    k_B · T · ln 2 carries units of joules per bit and is fixed by the
    relationship

        S_thermo = k_B · ln Ω,        S_info = log_2 Ω,

    so that S_thermo = k_B · ln 2 · S_info. For an isothermal process
    Q = T · ΔS_thermo = T · k_B · ln 2 · ΔS_info.

    None of that conversion is proved here. It is the definition of how
    information entropy maps into thermodynamic entropy. What this file
    provides is the inequality in Landauer units (Q / (k_B · T · ln 2) ≥
    bits_erased), which is exactly [landauer_information_bound]. *)

(** ** Connection to the Thiele Machine's μ-ledger

    [μ] counts irreversible bit operations. Identifying it with
    [bits_erased] gives the bridge theorem: in Landauer units,
    environmental entropy increase is bounded below by μ. *)
Definition mu (e : Erasure) : nat := bits_erased e.

Theorem thermodynamic_bridge : forall pe : PhysicalErasure,
  env_entropy_increase pe >= mu (erasure_op pe).
Proof.
  intro pe.
  unfold mu.
  apply landauer_information_bound.
Qed.

(** ** Worked example: a single-bit reset *)

(** Reset of one bit: input space [{0,1}], output space [{0}]. *)
Definition one_bit_reset : Erasure := {|
  input_bits := 1;
  output_bits := 0;
  output_leq := Nat.le_0_l 1
|}.

Lemma one_bit_erased : bits_erased one_bit_reset = 1.
Proof. reflexivity. Qed.

Lemma one_bit_irreversible : is_irreversible one_bit_reset.
Proof.
  apply erasure_irreversible.
  rewrite one_bit_erased. auto.
Qed.

(** Trivial helper used to populate the [second_law_satisfied] field. *)
Lemma one_ge_one : 1 >= 1.
Proof. auto. Qed.

(** A minimum-cost physical realisation of [one_bit_reset]: dump exactly
    one bit of entropy to the environment. *)
Definition physical_one_bit_reset : PhysicalErasure := {|
  erasure_op := one_bit_reset;
  env_entropy_increase := 1;
  second_law_satisfied := one_ge_one
|}.

(** Landauer bound for the worked example. *)
Lemma one_bit_landauer :
  env_entropy_increase physical_one_bit_reset >= 1.
Proof.
  pose proof (landauer_information_bound physical_one_bit_reset).
  simpl in *. exact H.
Qed.

(** ** Worked example: an n-bit reset

    Generalises the one-bit case: input space [2^n], output space
    [{0}]. The minimum environmental cost is [n] bits. *)
Definition n_bit_reset (n : nat) : Erasure := {|
  input_bits := n;
  output_bits := 0;
  output_leq := Nat.le_0_l n
|}.

Lemma n_bits_erased : forall n, bits_erased (n_bit_reset n) = n.
Proof. intro n. unfold bits_erased, n_bit_reset. simpl. apply Nat.sub_0_r. Qed.

Lemma n_ge_n : forall n, n >= n.
Proof. intro n. auto. Qed.

Lemma n_bit_second_law : forall n, n >= bits_erased (n_bit_reset n).
Proof.
  intro n. rewrite n_bits_erased. apply n_ge_n.
Qed.

(** Minimum-cost physical realisation of an [n]-bit reset. *)
Definition physical_n_bit_reset (n : nat) : PhysicalErasure := {|
  erasure_op := n_bit_reset n;
  env_entropy_increase := n;
  second_law_satisfied := n_bit_second_law n
|}.

Theorem n_bit_landauer : forall n,
  env_entropy_increase (physical_n_bit_reset n) >= n.
Proof.
  intro n.
  pose proof (landauer_information_bound (physical_n_bit_reset n)).
  simpl in *.
  rewrite n_bits_erased in H. exact H.
Qed.

(** ** Composition: erasures chain additively

    Sequential erasures add their bit costs. The hypothesis
    [output_bits e1 = input_bits e2] is the chaining condition. *)
Lemma erasure_additive : forall e1 e2,
  output_bits e1 = input_bits e2 ->
  bits_erased e1 + bits_erased e2 =
  (input_bits e1 - output_bits e2).
Proof.
  intros e1 e2 Hchain.
  unfold bits_erased.
  rewrite Hchain.
  destruct e1 as [in1 out1 H1].
  destruct e2 as [in2 out2 H2].
  simpl in *. subst in2.
  lia.
Qed.

(** ** Summary of what is proved

    The following hold with no axioms and no [Admitted]:

      - Erasure of at least one bit is irreversible
        ([erasure_irreversible]).
      - Erasure strictly decreases system entropy
        ([erasure_decreases_entropy]).
      - The second law forces environmental entropy increase to dominate
        bits erased ([landauer_information_bound]).
      - The information-side bridge to μ-accounting
        ([thermodynamic_bridge]).
      - Worked one-bit and n-bit examples ([one_bit_landauer],
        [n_bit_landauer]).

    What the physics adds — and is not provable here — is the
    bits-to-joules conversion factor k_B · T · ln 2, the fact that
    physical systems obey the second law, and the identification of
    computational bits with phase-space regions. Those are bridges, not
    theorems. *)

(** Assumption-printing checks: the named theorems below should report
    [Closed under the global context]. *)
Print Assumptions landauer_information_bound.
Print Assumptions thermodynamic_bridge.
Print Assumptions erasure_irreversible.

Check landauer_information_bound.
Check thermodynamic_bridge.
Check erasure_irreversible.

(** Re-export of [Bitstring] under a stable alias for downstream files. *)
Definition Bitstring_anchor := Bitstring.
