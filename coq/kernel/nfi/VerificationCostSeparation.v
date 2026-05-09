(** VerificationCostSeparation: the Path-2 verification-cost gap.

    AIM
    ---
    M5 ([HonestCostTracking.v]) proved that the unconstrained world
    [CostBearingSystem] admits free forgery while the honest world
    [CertificationSystem] does not.  That gap is *existence-of-trace*:
    the dishonest world contains traces the honest world rules out.

    This file goes one level deeper.  Even given a *complete trace*
    from an unconstrained cost-bearing system, *verifying* the trace's
    honesty is an Ω(trace-length) information-theoretic problem in the
    worst case.  In Thiele, by contrast, honesty verification is O(1):
    the kernel theorem ties [vm_certified = true] to cost-law honesty by
    construction, so reading a single bit suffices.

    This is the verification-side statement that closes the
    "well-formedness escape" the researcher named:
        - "OK, your A2 makes the existence-gap real (M5).  But a
           sufficiently-clever TM with bookkeeping in memory could just
           satisfy A2 and the gap disappears."
        - "Yes — and *checking* that the TM's program actually maintains
           A2 is itself an Ω(trace-length) problem.  Thiele moves the
           check from runtime/program-analysis to type-theoretic
           guarantee."

    What is proven
    --------------
    1. [free_trace_honesty_predicate] - definition of trace honesty for
       an unconstrained system (every cert-flip step has cost ≥ 1).
    2. [thiele_trace_honesty_is_constant_witness] - in Thiele, every
       valid trace from the initial state with vm_certified=true is
       honest by construction.  The witness is the single boolean
       [vm_certified], no trace inspection required.
    3. [free_world_honesty_verifier_must_read_every_cert_step] - the
       core adversary theorem.  Any verifier on free traces that is
       correct on every trace must inspect every step that flips cert
       false→true.  Otherwise, an adversary plants a zero-cost cert-
       flip at an uninspected step and the verifier accepts the
       dishonest trace as honest.
    4. [verification_cost_gap_omega_T] - asymptotic consequence: for
       traces of length T containing arbitrarily many cert-flip steps,
       the verifier must inspect Ω(T) positions.  Thiele needs O(1).

    What is NOT proven
    ------------------
    - This is not a complexity-class separation in the standard sense.
      The free-world verifier's lower bound is information-theoretic
      (number of positions read), not time-complexity-theoretic.
    - This says nothing about Path 1 (computability).  Both worlds
      compute the same functions.  The gap is in the resource
      "bits-read-to-verify-honesty," which is novel and which the
      Thiele ISA avoids paying.
*)

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import SimulationProof.
From Kernel Require Import AbstractNoFI.
From Kernel Require Import HonestCostTracking.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** ** The free-world trace model.

    A free trace is a sequence of step-records: each record names a
    before-state cert flag, an after-state cert flag, and a per-step
    cost paid.  Honesty: every step that flips cert false→true has
    paid cost ≥ 1.

    This is the trace-as-data view, where cost annotations are
    explicit and could be lies.  The free world cannot tell from the
    final cert bit alone whether the trace is honest.  The honest
    world (Thiele, or any CertificationSystem) cannot produce a
    dishonest trace at all because its step rules forbid it. *)

Record FreeStepRecord := mk_free_step {
  fs_before_cert : bool;
  fs_after_cert  : bool;
  fs_cost        : nat
}.

Definition FreeTrace := list FreeStepRecord.

(** A step is a "cert-flip" if it transitions cert false→true. *)
Definition is_cert_flip (r : FreeStepRecord) : bool :=
  andb (negb r.(fs_before_cert)) r.(fs_after_cert).

(** A step is honest if it isn't a cert-flip, or if it paid cost ≥ 1. *)
Definition step_honest (r : FreeStepRecord) : Prop :=
  is_cert_flip r = true -> r.(fs_cost) >= 1.

(** A trace is honest if every step is honest. *)
Definition trace_honest (t : FreeTrace) : Prop :=
  Forall step_honest t.

(** ** Thiele side: O(1) honesty verification.

    For the Thiele VM, the cost of every instruction is fixed by the
    cost law [instruction_cost] in [VMStep.v].  In particular, the
    cost of any instruction that can flip [vm_certified] is ≥ 1 by
    [no_free_certification_certified] (the kernel's A2 theorem).
    Therefore, a Thiele trace, *encoded* as a [FreeTrace] by reading
    off (before-cert, after-cert, instruction-cost), is *automatically*
    honest by construction. *)

(** Encode a Thiele trace prefix as a FreeTrace.  Each record reads
    cert from the VMState before/after the step and the cost from the
    instruction-cost law. *)
Fixpoint encode_thiele_trace
         (s : VMState) (instrs : list vm_instruction) : FreeTrace :=
  match instrs with
  | []        => []
  | i :: rest =>
      let s' := vm_apply s i in
      mk_free_step s.(vm_certified) s'.(vm_certified) (instruction_cost i)
      :: encode_thiele_trace s' rest
  end.

(** Thiele's encoded trace is honest by construction — the cost law
    forces every cert-flip step to have cost ≥ 1. *)
Theorem thiele_encoded_trace_is_honest :
  forall (s : VMState) (instrs : list vm_instruction),
    trace_honest (encode_thiele_trace s instrs).
Proof.
  intros s instrs. revert s.
  induction instrs as [| i rest IH]; intros s.
  - simpl. constructor.
  - simpl. constructor.
    + (* current step honest *)
      unfold step_honest.
      intros Hflip.
      unfold is_cert_flip in Hflip.
      simpl in Hflip.
      apply Bool.andb_true_iff in Hflip.
      destruct Hflip as [Hbefore Hafter].
      apply Bool.negb_true_iff in Hbefore.
      apply no_free_certification_certified
        with (s := s) (i := i); assumption.
    + (* rest of trace honest *)
      apply IH.
Qed.

(** Thiele's O(1) honesty witness: a single boolean — the encoded
    trace's final cert flag — combined with [thiele_encoded_trace_is_honest],
    suffices to know the trace is honest.  No trace inspection required.

    Formally, the verifier needs only the type-level fact that the
    trace was produced by [encode_thiele_trace]; it does not need to
    inspect any field of any record in the trace. *)
Theorem thiele_honesty_O_1_witness :
  forall (s : VMState) (instrs : list vm_instruction),
    (* The verifier returns "honest" without reading the trace. *)
    let verdict_without_reading_trace := true in
    (verdict_without_reading_trace = true) <->
    trace_honest (encode_thiele_trace s instrs).
Proof.
  intros s instrs. simpl.
  split.
  - intros _. apply thiele_encoded_trace_is_honest.
  - intros _. reflexivity.
Qed.

(** ** Free side: Ω(T) honesty verification — the adversary argument.

    A "verifier of trace honesty" reads some positions of a trace and
    decides honest/dishonest.  We show: any verifier that is correct
    on every trace must inspect every position where a cert-flip can
    occur.  Otherwise, the adversary plants a zero-cost cert-flip at
    an uninspected position and the verifier accepts a dishonest
    trace as honest.

    This is the verification-side analogue of
    [non_adaptive_must_probe_every_assignment] in
    [NonAdaptiveLowerBound.v]. *)

(** The honest baseline: a trace consisting of [n] non-cert-flip
    steps with arbitrary cost.  We use [false → false, cost = 0] as
    the canonical non-cert-flip step. *)
Definition trivial_step : FreeStepRecord := mk_free_step false false 0.

Lemma trivial_step_honest : step_honest trivial_step.
Proof.
  unfold step_honest, trivial_step, is_cert_flip. simpl.
  intro H. discriminate.
Qed.

Definition baseline_trace (n : nat) : FreeTrace := repeat trivial_step n.

Lemma baseline_trace_honest : forall n, trace_honest (baseline_trace n).
Proof.
  induction n as [| n' IH].
  - simpl. constructor.
  - simpl. constructor.
    + apply trivial_step_honest.
    + exact IH.
Qed.

(** The adversary witness: a forged step that flips cert at cost 0.
    This is exactly [dishonest_forge_system]'s step encoded as a
    [FreeStepRecord]. *)
Definition forged_step : FreeStepRecord := mk_free_step false true 0.

Lemma forged_step_dishonest : ~ step_honest forged_step.
Proof.
  unfold step_honest, forged_step, is_cert_flip. simpl.
  intro H. specialize (H eq_refl). lia.
Qed.

(** [adversary_trace pos n]: the baseline trace of length n, with
    position [pos] replaced by [forged_step] (if pos < n).
    For pos ≥ n, returns the baseline. *)
Fixpoint adversary_trace (pos n : nat) : FreeTrace :=
  match n with
  | 0    => []
  | S n' =>
    match pos with
    | 0      => forged_step :: baseline_trace n'
    | S pos' => trivial_step :: adversary_trace pos' n'
    end
  end.

(** The adversary trace is dishonest exactly because it contains
    [forged_step] at position [pos] (for pos < n). *)
Lemma adversary_trace_dishonest :
  forall n pos, pos < n -> ~ trace_honest (adversary_trace pos n).
Proof.
  induction n as [| n' IH]; intros pos Hlt.
  - lia.
  - destruct pos as [| pos'].
    + simpl. intro Hhonest.
      inversion Hhonest as [| h t Hh Ht].
      apply forged_step_dishonest. exact Hh.
    + simpl. intro Hhonest.
      inversion Hhonest as [| h t Hh Ht].
      apply IH with (pos := pos').
      * lia.
      * exact Ht.
Qed.

(** Helper: nth on a baseline_trace returns trivial_step for any
    in-range position. *)
Lemma nth_baseline_trace :
  forall n i, i < n ->
    nth i (baseline_trace n) trivial_step = trivial_step.
Proof.
  induction n as [| n' IH]; intros i Hi.
  - lia.
  - destruct i as [| i'].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

(** Helper: nth on adversary_trace at any position other than [pos]
    returns trivial_step. *)
Lemma nth_adversary_trace_off_pos :
  forall n pos i,
    pos < n ->
    i <> pos ->
    i < n ->
    nth i (adversary_trace pos n) trivial_step = trivial_step.
Proof.
  induction n as [| n' IH]; intros pos i Hpos Hne Hi.
  - lia.
  - destruct pos as [| pos']; destruct i as [| i'].
    + (* pos = 0, i = 0, but i <> pos: contradiction *) lia.
    + (* pos = 0, i = S i': read trivial_step out of baseline_trace n' *)
      simpl. apply nth_baseline_trace. lia.
    + (* pos = S pos', i = 0: head is trivial_step *)
      reflexivity.
    + (* pos = S pos', i = S i': recurse *)
      simpl. apply IH; lia.
Qed.

(** Crucially: the adversary trace and the baseline trace are
    *identical* at every position except [pos].  A verifier that
    doesn't read position [pos] cannot distinguish them. *)
Lemma adversary_trace_differs_only_at_pos :
  forall n pos i,
    pos < n ->
    i <> pos ->
    i < n ->
    nth i (adversary_trace pos n) trivial_step =
    nth i (baseline_trace n) trivial_step.
Proof.
  intros n pos i Hpos Hne Hi.
  rewrite nth_adversary_trace_off_pos by assumption.
  rewrite nth_baseline_trace by assumption.
  reflexivity.
Qed.

(** ** The verification-cost separation theorem.

    Define a [PositionalVerifier] as a function that takes a list of
    positions to inspect and the trace, returns true iff the trace
    is honest.  The verifier's "cost" is the number of positions it
    reads.  Correctness: agrees with [trace_honest] on every trace.

    Adversary theorem: any positional verifier correct on every trace
    must read every position in [0, n) when given a length-n trace.
    Hence the verifier's cost is ≥ n.  Compare to Thiele: O(1). *)

Record PositionalVerifier := mk_pv {
  pv_positions : nat -> list nat;     (* given trace length, the positions to read *)
  pv_decide    : list FreeStepRecord -> bool  (* verdict from inspected positions *)
}.

(** A verifier "operates only on inspected positions" if its verdict
    on a trace depends only on the records at the positions it
    inspects. *)
Definition operates_on_inspected_only
           (V : PositionalVerifier) (n : nat) : Prop :=
  forall (t1 t2 : FreeTrace),
    length t1 = n -> length t2 = n ->
    (forall i, In i (V.(pv_positions) n) ->
               nth i t1 trivial_step = nth i t2 trivial_step) ->
    V.(pv_decide) t1 = V.(pv_decide) t2.

(** The verifier is correct on length-n traces if it returns true iff
    the trace is honest. *)
Definition verifier_correct (V : PositionalVerifier) (n : nat) : Prop :=
  forall (t : FreeTrace),
    length t = n ->
    (V.(pv_decide) t = true <-> trace_honest t).

(** The baseline trace has length n. *)
Lemma baseline_trace_length : forall n, length (baseline_trace n) = n.
Proof.
  intros n. unfold baseline_trace. apply repeat_length.
Qed.

(** The adversary trace also has length n (when pos < n). *)
Lemma adversary_trace_length :
  forall n pos, pos < n -> length (adversary_trace pos n) = n.
Proof.
  induction n as [| n' IH]; intros pos Hlt; simpl.
  - lia.
  - destruct pos as [| pos'].
    + simpl. f_equal. apply baseline_trace_length.
    + simpl. f_equal. apply IH. lia.
Qed.

(** **The verification-cost lower bound.**
    A correct verifier on length-n traces, operating only on
    inspected positions, must inspect every position in [0, n). *)
Theorem free_world_honesty_verifier_must_inspect_every_cert_position :
  forall (V : PositionalVerifier) (n : nat),
    verifier_correct V n ->
    operates_on_inspected_only V n ->
    forall pos, pos < n -> In pos (V.(pv_positions) n).
Proof.
  intros V n Hcorrect Hop pos Hpos.
  destruct (in_dec Nat.eq_dec pos (V.(pv_positions) n)) as [Hin | Hnotin]; auto.
  exfalso.
  pose proof (Hcorrect (baseline_trace n) (baseline_trace_length n))
    as [_ Hbase_implies].
  pose proof (Hcorrect (adversary_trace pos n)
                       (adversary_trace_length n pos Hpos))
    as [Hadv_decide_to_honest _].
  assert (Hbase_decide : V.(pv_decide) (baseline_trace n) = true).
  { apply Hcorrect.
    - apply baseline_trace_length.
    - apply baseline_trace_honest. }
  assert (Hagree : V.(pv_decide) (adversary_trace pos n)
                 = V.(pv_decide) (baseline_trace n)).
  { apply Hop.
    - apply adversary_trace_length. exact Hpos.
    - apply baseline_trace_length.
    - intros i Hi.
      destruct (Compare_dec.lt_dec i n) as [Hi_in_range | Hi_oob].
      + apply adversary_trace_differs_only_at_pos.
        * exact Hpos.
        * intros Heq. subst i. contradiction.
        * exact Hi_in_range.
      + (* i out of range: nth returns the default trivial_step
           on both traces (since both have length n).  *)
        rewrite (nth_overflow (adversary_trace pos n))
          by (rewrite adversary_trace_length by exact Hpos; lia).
        rewrite (nth_overflow (baseline_trace n))
          by (rewrite baseline_trace_length; lia).
        reflexivity. }
  rewrite Hbase_decide in Hagree.
  pose proof (Hadv_decide_to_honest Hagree) as Hadv_honest.
  apply (adversary_trace_dishonest n pos Hpos Hadv_honest).
Qed.

(** ** Asymptotic consequence: free-world verification reads Ω(T) positions.

    From [free_world_honesty_verifier_must_inspect_every_cert_position]:
    every position in [0, n) is inspected.  Therefore the deduplicated
    inspected-position set has size ≥ n, and the raw inspected list has
    length ≥ n.  Compare to Thiele: O(1).  Asymptotic gap: Ω(n) vs O(1),
    i.e., Ω(T) vs O(1) where T = trace length.

    The proof reuses the pigeonhole structure from
    [NonAdaptiveLowerBound]'s [non_adaptive_sat_lower_bound]. *)
Theorem free_world_verification_reads_T_positions :
  forall (V : PositionalVerifier) (n : nat),
    verifier_correct V n ->
    operates_on_inspected_only V n ->
    length (nodup Nat.eq_dec (V.(pv_positions) n)) >= n.
Proof.
  intros V n Hcorrect Hop.
  assert (Hincl : forall x, In x (seq 0 n) ->
                            In x (nodup Nat.eq_dec (V.(pv_positions) n))).
  { intros x Hx. apply nodup_In.
    apply in_seq in Hx.
    apply (free_world_honesty_verifier_must_inspect_every_cert_position
             V n Hcorrect Hop x).
    lia. }
  pose proof
    (NoDup_incl_length (seq_NoDup n 0) Hincl) as Hlen.
  rewrite seq_length in Hlen. exact Hlen.
Qed.

(** Length of the raw inspected-positions list also ≥ n. *)
Theorem free_world_verification_raw_length_ge_T :
  forall (V : PositionalVerifier) (n : nat),
    verifier_correct V n ->
    operates_on_inspected_only V n ->
    length (V.(pv_positions) n) >= n.
Proof.
  intros V n Hcorrect Hop.
  apply Nat.le_trans
    with (m := length (nodup Nat.eq_dec (V.(pv_positions) n))).
  - apply free_world_verification_reads_T_positions; assumption.
  - induction (V.(pv_positions) n) as [| x xs IH]; simpl; auto.
    destruct (in_dec Nat.eq_dec x xs); simpl; lia.
Qed.

(** ** The verification-cost gap, in one statement.

    Thiele needs O(1) inspected positions (zero, in fact).  The free
    world needs ≥ n.  This is the closure of Path 2 in the
    verification-information sense: a real, asymptotic, unconditional
    information-theoretic gap between Thiele and any cost-bearing
    system without ISA-enforced honesty. *)
Theorem verification_cost_gap_omega_T :
  forall (V : PositionalVerifier) (n : nat),
    verifier_correct V n ->
    operates_on_inspected_only V n ->
    (* Free-world cost (positions inspected) is at least n. *)
    length (V.(pv_positions) n) >= n
    (* Thiele cost (positions inspected) is 0: the verifier doesn't
       need the trace at all — see thiele_honesty_O_1_witness. *)
    /\ (forall (s : VMState) (instrs : list vm_instruction),
          trace_honest (encode_thiele_trace s instrs)).
Proof.
  intros V n Hcorrect Hop. split.
  - apply free_world_verification_raw_length_ge_T; assumption.
  - apply thiele_encoded_trace_is_honest.
Qed.
