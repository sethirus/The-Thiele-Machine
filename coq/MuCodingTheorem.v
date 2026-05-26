(** * MuCodingTheorem.v — certification-coding theorem (Chaitin-style).

    A two-sided tight bound on the minimum [MuChaitin.cert_payload_size]
    required to certify a decidable claim, with an in-VM achiever for
    the upper bound.

    Wrinkle worth flagging: [MuShannonBridge] explicitly disclaims any
    Shannon DPI form of the lower bound (file lines 330–356 there) under
    the kernel's deterministic VM semantics. Two cleanly available paths
    around it: restrict to tree-structured traces and use
    [MuShannonQuantitative.conditional_shannon_bound], or stay Chaitin-
    style and use [MuChaitin.cert_payload_size] as the intrinsic measure.
    This file takes the Chaitin route. The intrinsic measure is a
    syntactic per-instruction quantity; the lower bound is conditioned on
    the [cert_priced_eq] pricing policy (a stricter version of
    [MuChaitin.cert_priced] that asserts [instruction_cost = S
    (cert_payload_size)] rather than mere domination).
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import MuChaitin.
From Kernel Require Import MuNoFreeInsightQuantitative.

(* -------------------------------------------------------------------- *)
(** ** The CertifiableClaim record.

    A claim is a decidable predicate on VMState. The decidability is
    the honest restriction: the Coq formalization can only quantify
    over the Bool-valued claims; truly higher-order claims (e.g.,
    those involving second-order properties of executions) are outside
    the formal model.
*)

Record CertifiableClaim : Type := mk_ccl {
  ccl_pred : VMState -> bool
}.

Definition holds_at (P : CertifiableClaim) (s : VMState) : Prop :=
  ccl_pred P s = true.

(** A *certifier* for [P] is a cert-setter instruction whose
    application produces a state satisfying [P]. *)
Definition certifies_claim
    (P : CertifiableClaim) (s_init : VMState) (instr : vm_instruction) : Prop :=
  is_cert_setterb instr = true /\
  holds_at P (vm_apply s_init instr).

(* -------------------------------------------------------------------- *)
(** ** Predicate-style intrinsic cert-payload bounds.

    Coq's type theory does not directly express "minimum [MuChaitin.cert_payload_size]
    over an infinite set of instructions." We use a predicate pair
    instead: [P] is intrinsically certifiable *at least* [k] iff every
    certifier has payload ≥ k; [P] is intrinsically certifiable *at most*
    [k] iff some certifier has payload ≤ k. Tightness is the case
    where both hold for the same k.
*)

Definition intrinsic_payload_at_least
    (P : CertifiableClaim) (k : nat) : Prop :=
  forall (s_init : VMState) (instr : vm_instruction),
    certifies_claim P s_init instr ->
    MuChaitin.cert_payload_size instr >= k.

Definition intrinsic_payload_at_most
    (P : CertifiableClaim) (k : nat) : Prop :=
  exists (s_init : VMState) (instr : vm_instruction),
    certifies_claim P s_init instr /\
    MuChaitin.cert_payload_size instr <= k.

Definition intrinsic_payload_tight
    (P : CertifiableClaim) (k : nat) : Prop :=
  intrinsic_payload_at_least P k /\
  intrinsic_payload_at_most P k.

(* -------------------------------------------------------------------- *)
(** ** The canonical claim family: "vm_mu = k". *)

Definition mu_eq_k_pred (k : nat) (s : VMState) : bool :=
  Nat.eqb s.(vm_mu) k.

Definition mu_eq_k_claim (k : nat) : CertifiableClaim :=
  mk_ccl (mu_eq_k_pred k).

Lemma holds_mu_eq_k :
  forall k s, holds_at (mu_eq_k_claim k) s <-> s.(vm_mu) = k.
Proof.
  intros. unfold holds_at, mu_eq_k_claim, ccl_pred, mu_eq_k_pred.
  split.
  - apply Nat.eqb_eq.
  - intro H. apply Nat.eqb_eq. exact H.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Certifier-instruction cost facts. *)

Lemma certify_instruction_cost_payload_eq :
  forall delta, MuChaitin.cert_payload_size (instr_certify delta) = delta.
Proof. intros. reflexivity. Qed.

Lemma vm_apply_certify_mu_from_init :
  forall delta,
    (vm_apply init_state (instr_certify delta)).(vm_mu) = S delta.
Proof.
  intros delta.
  rewrite vm_apply_mu.
  unfold instruction_cost.
  rewrite init_state_mu_zero.
  simpl. lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Upper bound: the canonical certifier for [mu_eq_k_claim k]. *)

Theorem mu_eq_k_upper_bound :
  forall k, k >= 1 ->
    intrinsic_payload_at_most (mu_eq_k_claim k) (k - 1).
Proof.
  intros k Hk.
  exists init_state, (instr_certify (k - 1)).
  split.
  - split.
    + reflexivity.
    + apply holds_mu_eq_k.
      rewrite vm_apply_certify_mu_from_init. lia.
  - rewrite certify_instruction_cost_payload_eq. lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Lower bound: under cert_priced, certifying [mu_eq_k_claim k]
    from init_state with a single cert-setter requires MuChaitin.cert_payload_size
    at least [k - 1].

    The strategy is direct: [vm_apply init_state instr] has μ equal to
    [instruction_cost instr] (since [init_state.vm_mu = 0]). If the
    result satisfies "μ = k", then [instruction_cost instr = k]. Under
    cert_priced, [MuChaitin.cert_payload_size instr ≤ instruction_cost instr =
    k], which gives an upper bound, not a lower one. The lower bound
    needs more: it requires that no cert-setter with smaller payload
    *could* establish the claim. For the canonical claim family
    [mu_eq_k] this is true because the cost equals [k], and any
    cert-setter with payload < k - 1 must have cost ≤ k - 1 (under
    cert_priced is *equality* for the standard pricing where cost =
    S(payload)) — wait, that's not what cert_priced says in general.

    To get a clean lower bound matching the upper, we add the
    *Chaitin-equality* pricing assumption [cert_priced_eq]: for
    cert-setters, [instruction_cost = S(MuChaitin.cert_payload_size)]. Under
    this stricter policy, the bound is tight.
*)

Definition cert_priced_eq (instr : vm_instruction) : Prop :=
  is_cert_setterb instr = true ->
  instruction_cost instr = S (MuChaitin.cert_payload_size instr).

(** The standard kernel pricing satisfies cert_priced_eq for
    [instr_certify]. We do not require it for all cert-setters; only
    instances of the claim family that route through [instr_certify]. *)
Lemma instr_certify_priced_eq :
  forall delta, cert_priced_eq (instr_certify delta).
Proof.
  intros delta _. simpl. reflexivity.
Qed.

Theorem mu_eq_k_lower_bound :
  forall k, k >= 1 ->
    forall (instr : vm_instruction),
      cert_priced_eq instr ->
      certifies_claim (mu_eq_k_claim k) init_state instr ->
      MuChaitin.cert_payload_size instr >= k - 1.
Proof.
  intros k Hk instr Hpriced [Hsetter Hholds].
  apply holds_mu_eq_k in Hholds.
  rewrite vm_apply_mu in Hholds.
  rewrite init_state_mu_zero in Hholds.
  simpl in Hholds.
  (* Hholds: instruction_cost instr = k *)
  pose proof (Hpriced Hsetter) as Hcost.
  (* Hcost: instruction_cost instr = S (MuChaitin.cert_payload_size instr) *)
  rewrite Hcost in Hholds.
  (* Hholds: S (MuChaitin.cert_payload_size instr) = k *)
  lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Restricted intrinsic predicates over instructions satisfying
    [cert_priced_eq]. *)

Definition intrinsic_payload_at_least_priced
    (P : CertifiableClaim) (k : nat) : Prop :=
  forall (s_init : VMState) (instr : vm_instruction),
    cert_priced_eq instr ->
    s_init = init_state ->
    certifies_claim P s_init instr ->
    MuChaitin.cert_payload_size instr >= k.

(* -------------------------------------------------------------------- *)
(** ** The Phase 2 coding theorem.

    For each k ≥ 1, the canonical claim "vm_mu = k" has a tight
    intrinsic cert-payload size of [k - 1], measured among cert_priced_eq
    certifiers starting at init_state. The witness for the upper bound
    is the canonical certifier [instr_certify (k - 1)].
*)

Theorem mu_coding_theorem :
  forall k, k >= 1 ->
    (** Upper bound: [instr_certify (k-1)] is a cert_priced_eq certifier
        achieving MuChaitin.cert_payload_size = k - 1. *)
    (exists instr,
       cert_priced_eq instr /\
       certifies_claim (mu_eq_k_claim k) init_state instr /\
       MuChaitin.cert_payload_size instr = k - 1) /\
    (** Lower bound: every cert_priced_eq certifier of "vm_mu = k"
        starting from init_state has MuChaitin.cert_payload_size ≥ k - 1. *)
    (forall instr,
       cert_priced_eq instr ->
       certifies_claim (mu_eq_k_claim k) init_state instr ->
       MuChaitin.cert_payload_size instr >= k - 1).
Proof.
  intros k Hk.
  split.
  - exists (instr_certify (k - 1)). split; [|split].
    + apply instr_certify_priced_eq.
    + split.
      * reflexivity.
      * apply holds_mu_eq_k. rewrite vm_apply_certify_mu_from_init. lia.
    + reflexivity.
  - intros instr Hpriced Hcert.
    apply (mu_eq_k_lower_bound k Hk instr Hpriced Hcert).
Qed.

Print Assumptions mu_coding_theorem.
