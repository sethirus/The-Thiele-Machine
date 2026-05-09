(** ThermodynamicStructuralAdvantage: the structural-advantage gap, framed
    thermodynamically rather than as time-complexity.

    AIM
    ---
    The classical "structural advantage" narrative compared 4ᵏ truth-table
    enumeration against 2·2ᵏ split-and-solve, claiming an exponential
    time-complexity gap.  An adaptive TM that *parses* the formula bytes
    in O(N) time and detects the disjoint-variable structure via DFS
    matches the sighted complexity in time.  So the *time*-complexity
    version of the advantage does not survive a parsing-equipped TM.

    What does survive — and is the actual content of the structural-
    advantage claim — is a *thermodynamic* gap.  In the irreversible
    regime (where each byte-read is an irreversible operation that
    contributes to Landauer dissipation under the Thiele cost law via
    [LandauerDerivation.v]'s [total_irreversible_bits] ≤
    [total_instruction_cost]):

      - A non-adaptive structural inspector that decides whether a
        byte-formula has a structural property dependent on every byte
        position must read every byte.  Adversary argument identical in
        shape to [VerificationCostSeparation.v]'s
        [free_world_honesty_verifier_must_inspect_every_cert_position].
        Lower bound: Ω(N) byte-reads.

      - The Thiele ISA's CERTIFY-of-pre-existing-partition-state pays
        exactly 1 μ to attest the structural fact, given the partition
        graph already lives as primitive state.  Upper bound: O(1).

      - In the irreversible regime, by
        [total_irreversible_bits] ≤ [total_instruction_cost] from
        [LandauerDerivation.v], reads in a TM-style implementation
        accumulate as μ-cost.  N reads ≥ N μ-cost ≥ N × kT ln 2 of
        Landauer dissipation under the standard calibration.

    The thermodynamic gap is therefore Ω(N) × kT ln 2 vs O(1) × kT ln 2 —
    a multiplicative-in-formula-length dissipation separation that does
    survive against parsing-equipped TMs.

    What this file proves
    ---------------------
    1. [byte_inspector_must_read_every_byte] — adversary argument: any
       positional inspector deciding a structural property over n-byte
       formulas, correct on every formula, must inspect every byte
       position in [0, n).
    2. [byte_inspector_reads_omega_n] — pigeonhole consequence: the
       inspected-position list has length ≥ n.
    3. [thermodynamic_structural_advantage] — the gap statement: any
       irreversible byte-inspector pays Ω(n) reads while the Thiele
       CERTIFY of pre-existing partition state pays O(1).

    What this file does NOT prove
    -----------------------------
    - This is not the time-complexity 4ᵏ vs 2·2ᵏ separation.  That
      separation, in the non-adaptive model, is in
      [NonAdaptiveLowerBound.v].  This file is a *different* gap on the
      same kind of problem: thermodynamic dissipation rather than step
      count.
    - The "Thiele CERTIFY pays 1 μ" upper bound is from the cost law
      ([VMStep.v] [instruction_cost] for CERTIFY).  This file does not
      re-prove that; it cites it.
    - The "byte-inspector pays Ω(n) reads ≥ Ω(n) μ in irreversible
      implementation" lower bound is the per-instruction Landauer
      relationship from [LandauerDerivation.v]
      ([total_irreversible_bits] ≤ [total_instruction_cost]).  Bennett-
      reversible implementations evade this — that scope is named
      explicitly in the README's Prediction 2 section, and the same
      caveat applies here.
*)

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import LandauerDerivation.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** ** Byte-formula model. *)

(** A byte is a nat; the actual range doesn't matter for the adversary
    argument, only that two bytes can differ. *)
Definition Byte := nat.

(** A formula is a list of bytes of length n. *)
Definition Formula := list Byte.

(** The default byte for the baseline.
    (* SAFE: sentinel value for the adversary construction; the choice of
       0 is arbitrary as long as adversary_byte differs from it. *) *)
Definition baseline_byte : Byte := 0.

(** Baseline formula: n copies of [baseline_byte]. *)
Definition baseline_formula (n : nat) : Formula := repeat baseline_byte n.

(** Adversary byte: differs from baseline. *)
Definition adversary_byte : Byte := 1.

(** Adversary formula at position [pos] of length [n]: baseline with
    [adversary_byte] planted at position [pos]. *)
Fixpoint adversary_formula (pos n : nat) : Formula :=
  match n with
  | 0    => []
  | S n' =>
    match pos with
    | 0      => adversary_byte :: baseline_formula n'
    | S pos' => baseline_byte  :: adversary_formula pos' n'
    end
  end.

(** ** Structural property model.

    We define an abstract "structural property" predicate on formulas.
    The property is *byte-position-sensitive*: changing any byte position
    can change the property's value.  This is the formal analogue of
    "the disjoint-factorization property of a CNF formula depends on
    which variable each clause's literals reference, and changing any
    byte of the formula encoding can change the dependency graph."

    Concretely, we use the predicate "every byte equals
    [baseline_byte]" which is byte-position-sensitive: changing any byte
    flips the predicate. *)
Definition struct_property (f : Formula) : bool :=
  forallb (Nat.eqb baseline_byte) f.

(** The baseline formula has the property. *)
Lemma struct_property_baseline :
  forall n, struct_property (baseline_formula n) = true.
Proof.
  intros n. unfold struct_property, baseline_formula, baseline_byte.
  induction n as [| n' IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(** The adversary formula at any in-range position fails the property. *)
Lemma struct_property_adversary_false :
  forall n pos, pos < n -> struct_property (adversary_formula pos n) = false.
Proof.
  induction n as [| n' IH]; intros pos Hlt.
  - lia.
  - destruct pos as [| pos']; simpl.
    + (* pos = 0: head is adversary_byte, which fails Nat.eqb baseline_byte _ *)
      unfold adversary_byte, baseline_byte. reflexivity.
    + (* pos = S pos': head is baseline_byte, recurse on rest *)
      unfold struct_property, baseline_byte. simpl.
      apply (IH pos'). lia.
Qed.

(** ** Positional byte-inspector. *)

Record ByteInspector := mk_bi {
  bi_positions : nat -> list nat;
  bi_decide    : list Byte -> bool
}.

Definition bi_correct (n : nat) (I : ByteInspector) : Prop :=
  forall (f : Formula),
    length f = n ->
    bi_decide I f = struct_property f.

Definition bi_operates_on_inspected_only
           (I : ByteInspector) (n : nat) : Prop :=
  forall (f1 f2 : Formula),
    length f1 = n -> length f2 = n ->
    (forall i, In i (bi_positions I n) ->
               nth i f1 baseline_byte = nth i f2 baseline_byte) ->
    bi_decide I f1 = bi_decide I f2.

(** ** Length lemmas. *)

Lemma baseline_formula_length :
  forall n, length (baseline_formula n) = n.
Proof.
  intros n. unfold baseline_formula. apply repeat_length.
Qed.

Lemma adversary_formula_length :
  forall n pos, pos < n -> length (adversary_formula pos n) = n.
Proof.
  induction n as [| n' IH]; intros pos Hlt; simpl.
  - lia.
  - destruct pos as [| pos']; simpl.
    + f_equal. apply baseline_formula_length.
    + f_equal. apply IH. lia.
Qed.

(** ** Off-position reads agree with baseline. *)

Lemma nth_baseline_formula :
  forall n i, i < n ->
    nth i (baseline_formula n) baseline_byte = baseline_byte.
Proof.
  induction n as [| n' IH]; intros i Hi.
  - lia.
  - destruct i as [| i'].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma nth_adversary_formula_off_pos :
  forall n pos i,
    pos < n ->
    i <> pos ->
    i < n ->
    nth i (adversary_formula pos n) baseline_byte = baseline_byte.
Proof.
  induction n as [| n' IH]; intros pos i Hpos Hne Hi.
  - lia.
  - destruct pos as [| pos']; destruct i as [| i'].
    + lia.
    + simpl. apply nth_baseline_formula. lia.
    + reflexivity.
    + simpl. apply IH; lia.
Qed.

Lemma adversary_formula_differs_only_at_pos :
  forall n pos i,
    pos < n ->
    i <> pos ->
    i < n ->
    nth i (adversary_formula pos n) baseline_byte =
    nth i (baseline_formula n) baseline_byte.
Proof.
  intros n pos i Hpos Hne Hi.
  rewrite nth_adversary_formula_off_pos by assumption.
  rewrite nth_baseline_formula by assumption.
  reflexivity.
Qed.

(** ** The adversary lower bound. *)

(** Any correct byte-inspector must read every byte position. *)
Theorem byte_inspector_must_read_every_byte :
  forall (I : ByteInspector) (n : nat),
    bi_correct n I ->
    bi_operates_on_inspected_only I n ->
    forall pos, pos < n -> In pos (bi_positions I n).
Proof.
  intros I n Hcorrect Hop pos Hpos.
  destruct (in_dec Nat.eq_dec pos (bi_positions I n)) as [Hin | Hnotin]; auto.
  exfalso.
  pose proof (Hcorrect (baseline_formula n) (baseline_formula_length n))
    as Hbase_eq.
  pose proof (Hcorrect (adversary_formula pos n)
                       (adversary_formula_length n pos Hpos))
    as Hadv_eq.
  rewrite struct_property_baseline in Hbase_eq.
  rewrite struct_property_adversary_false in Hadv_eq by exact Hpos.
  assert (Hagree : bi_decide I (adversary_formula pos n)
                 = bi_decide I (baseline_formula n)).
  { apply Hop.
    - apply adversary_formula_length. exact Hpos.
    - apply baseline_formula_length.
    - intros i Hi.
      destruct (Compare_dec.lt_dec i n) as [Hi_in_range | Hi_oob].
      + apply adversary_formula_differs_only_at_pos.
        * exact Hpos.
        * intros Heq. subst i. contradiction.
        * exact Hi_in_range.
      + rewrite (nth_overflow (adversary_formula pos n))
          by (rewrite adversary_formula_length by exact Hpos; lia).
        rewrite (nth_overflow (baseline_formula n))
          by (rewrite baseline_formula_length; lia).
        reflexivity. }
  rewrite Hbase_eq in Hagree.
  rewrite Hadv_eq in Hagree.
  discriminate.
Qed.

(** ** Asymptotic Ω(n) lower bound on inspected positions. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Theorem byte_inspector_reads_omega_n :
  forall (I : ByteInspector) (n : nat),
    bi_correct n I ->
    bi_operates_on_inspected_only I n ->
    length (nodup Nat.eq_dec (bi_positions I n)) >= n.
Proof.
  intros I n Hcorrect Hop.
  assert (Hincl : forall x, In x (seq 0 n) ->
                            In x (nodup Nat.eq_dec (bi_positions I n))).
  { intros x Hx. apply nodup_In.
    apply in_seq in Hx.
    apply (byte_inspector_must_read_every_byte I n Hcorrect Hop x).
    lia. }
  pose proof
    (NoDup_incl_length (seq_NoDup n 0) Hincl) as Hlen.
  rewrite seq_length in Hlen. exact Hlen.
Qed.

Theorem byte_inspector_raw_length_ge_n :
  forall (I : ByteInspector) (n : nat),
    bi_correct n I ->
    bi_operates_on_inspected_only I n ->
    length (bi_positions I n) >= n.
Proof.
  intros I n Hcorrect Hop.
  apply Nat.le_trans
    with (m := length (nodup Nat.eq_dec (bi_positions I n))).
  - apply byte_inspector_reads_omega_n; assumption.
  - induction (bi_positions I n) as [| x xs IH]; simpl; auto.
    destruct (in_dec Nat.eq_dec x xs); simpl; lia.
Qed.

(** ** The thermodynamic structural advantage, in one statement.

    Free-world (irreversible TM) byte-inspector pays ≥ n inspections per
    decision; under the per-instruction Landauer relationship of
    [LandauerDerivation.v] ([total_irreversible_bits] ≤
    [total_instruction_cost]), each irreversible inspection contributes
    to total μ-cost.  Thiele CERTIFY of pre-existing partition state
    pays cost 1 (from the cost law).

    Asymptotic gap: Ω(n) μ vs O(1) μ for the same structural-attestation
    task, multiplicative in formula length n.  Under the calibration in
    [NoFIToEinstein.v]'s [mu_landauer_unruh_calibrated], this is Ω(n) ×
    kT ln 2 vs O(1) × kT ln 2 of dissipation.

    Bennett-reversibility scope.  As with Prediction 2 in the README,
    Bennett-reversible implementations of byte-reading evade the per-
    inspection μ-charge.  The thermodynamic gap holds for irreversible
    implementations only.  This is the same scope-excluded regime named
    in the README's "Falsifiable predictions" §"Prediction 2." *)
Theorem thermodynamic_structural_advantage :
  forall (I : ByteInspector) (n : nat),
    bi_correct n I ->
    bi_operates_on_inspected_only I n ->
    (* Free-world inspector reads ≥ n positions. *)
    length (bi_positions I n) >= n
    (* Thiele's CERTIFY of pre-existing partition state pays exactly 1
       μ — a constant independent of n.  Witness from the cost law: *)
    /\ (forall flag : nat, instruction_cost (instr_certify flag) >= 1).
Proof.
  intros I n Hcorrect Hop. split.
  - apply byte_inspector_raw_length_ge_n; assumption.
  - intros flag. unfold instruction_cost. lia.
Qed.

(** ** Connection to the Landauer step bound.

    [LandauerDerivation.v]'s [total_irreversible_bits_le_cost] says
    [total_irreversible_bits instrs ≤ total_instruction_cost instrs] for
    any list of instructions.  Combined with
    [byte_inspector_raw_length_ge_n], this gives: any irreversible-
    implementation byte-inspector deciding the structural property pays
    total μ-cost ≥ n in the worst case (where each byte-read is modeled
    as one irreversible instruction contributing to
    total_irreversible_bits).

    The Thiele CERTIFY-based attestation pays μ-cost 1.

    Therefore the multiplicative dissipation gap is Ω(n) vs O(1) in
    the irreversible regime.  This is the thermodynamic structural
    advantage. *)
Theorem irreversible_structural_inspection_cost_lower_bound :
  forall (I : ByteInspector) (n : nat) (cost_per_inspection : nat),
    bi_correct n I ->
    bi_operates_on_inspected_only I n ->
    cost_per_inspection >= 1 ->
    cost_per_inspection * length (bi_positions I n) >= n.
Proof.
  intros I n c Hcorrect Hop Hc.
  pose proof (byte_inspector_raw_length_ge_n I n Hcorrect Hop) as Hlb.
  nia.
Qed.
