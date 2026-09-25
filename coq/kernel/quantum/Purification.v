(** Purification: Bloch-ball mixed states admit the expected two-point decomposition

  This file works in the single-qubit Bloch-ball model and proves the basic
  purification-style decomposition facts used later. Mixed states live in the
  ball, pure states on the sphere, and the relevant purity arithmetic is made
  explicit.

  The scope is that small geometric model. The file is not trying to rebuild
  all of decoherence theory; it proves the decomposition and deficit facts it
  actually needs.
*)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** [bloch_mixed] is the radius-at-most-one predicate on three real coordinates. *)
Definition bloch_mixed (x y z : R) : Prop := x*x + y*y + z*z <= 1.

(** [bloch_pure] is the radius-one predicate on three real coordinates. *)
Definition bloch_pure (x y z : R) : Prop := x*x + y*y + z*z = 1.

(** The inclusion [bloch_pure -> bloch_mixed] holds by lra after unfolding
    both definitions; no caller in the development needs it as a
    standalone lemma, so it is not exported. *)

(** [purity] is the squared-radius expression used by this file. *)
Definition purity (x y z : R) : R := x*x + y*y + z*z.

(** Non-negativity of purity is sum-of-squares >= 0, dispatched by nra
    after unfolding. No caller imports it, so no standalone lemma is
    exported. *)

(** [purification_deficit] is one minus the formal squared-radius expression. *)
Definition purification_deficit (x y z : R) : R := 1 - purity x y z.

(** [mixed_has_deficit] derives the nonnegative deficit bound from [bloch_mixed]. *)
Lemma mixed_has_deficit : forall x y z : R,
  bloch_mixed x y z ->
  purity x y z <= 1 /\ purification_deficit x y z >= 0.
Proof.
  intros x y z Hmixed.
  unfold bloch_mixed, purity, purification_deficit in *.
  split.
  - exact Hmixed.
  - (* 1 - sum >= 0 follows from sum <= 1 *)
    apply Rge_minus. apply Rle_ge. exact Hmixed.
Qed.

(** [sq_nonneg] records the nonnegativity of a real square for later arithmetic. *)
Lemma sq_nonneg : forall x : R, x * x >= 0.
Proof. intro x. nra. Qed.

(** [purification_principle] supplies two real numbers for every [bloch_mixed] triple. *)

(** The witnesses lie in [0,1], sum to one, and have squared difference equal to [purity x y z]. *)

(** The proof uses the explicit square-root construction and real arithmetic. *)

(** It does not establish a decomposition of density matrices or a physical purification protocol. *)
Theorem purification_principle :
  forall x y z : R,
    bloch_mixed x y z ->
    exists (lambda1 lambda2 : R),
      0 <= lambda1 <= 1 /\
      0 <= lambda2 <= 1 /\
      lambda1 + lambda2 = 1 /\
      (lambda1 - lambda2) * (lambda1 - lambda2) = purity x y z.
Proof.
  intros x y z Hmixed.
  set (r2 := purity x y z).
  (* First establish bounds on r² *)
  assert (Hr2_bound: 0 <= r2 <= 1).
  { unfold r2, purity, bloch_mixed in *.
    split.
    - pose proof (sq_nonneg x). pose proof (sq_nonneg y). pose proof (sq_nonneg z). lra.
    - exact Hmixed. }
  (* Construct the purification *)
  exists ((1 + sqrt r2) / 2), ((1 - sqrt r2) / 2).
  (* Bound on √r² *)
  assert (Hsqrt_bound: 0 <= sqrt r2 <= 1).
  { split.
    - apply sqrt_pos.
    - rewrite <- sqrt_1. apply sqrt_le_1; lra. }
  assert (H2ne0: 2 <> 0) by lra.
  assert (Hinv2: /2 <> 0) by (apply Rinv_neq_0_compat; lra).
  split; [| split; [| split]].
  - (* λ₁ ∈ [0,1]: 0 ≤ (1 + √r²)/2 ≤ 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* λ₂ ∈ [0,1]: 0 ≤ (1 - √r²)/2 ≤ 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* λ₁ + λ₂ = 1: (1 + √r²)/2 + (1 - √r²)/2 = 1 *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 + (1 - sqrt r2) * /2)
      with ((1 + sqrt r2 + 1 - sqrt r2) * /2) by ring.
    replace (1 + sqrt r2 + 1 - sqrt r2) with 2 by ring.
    apply Rinv_r. lra.
  - (* (λ₁ - λ₂)² = r²: ((1+√r²)/2 - (1-√r²)/2)² = r² *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 - (1 - sqrt r2) * /2)
      with ((sqrt r2 + sqrt r2) * /2) by ring.
    assert (Heq: (sqrt r2 + sqrt r2) * /2 = sqrt r2).
    { replace ((sqrt r2 + sqrt r2) * / 2) with (sqrt r2 * (2 * / 2)).
      - assert (Htmp: 2 * / 2 = 1) by (apply Rinv_r; lra).
        rewrite Htmp. ring.
      - ring. }
    rewrite Heq.
    rewrite sqrt_sqrt; [reflexivity | destruct Hr2_bound; lra].
Qed.

(** [pure_needs_no_reference] is the arithmetic consequence of [bloch_pure] and [purification_deficit]. *)
Corollary pure_needs_no_reference : forall x y z : R,
  bloch_pure x y z ->
  purification_deficit x y z = 0.
Proof.
  intros x y z Hpure.
  unfold purification_deficit, purity, bloch_pure in *.
  lra.
Qed.

(** The numerical fact that purification_deficit 0 0 0 = 1 is a direct
    ring computation after unfolding. No caller in the development
    references it, so no standalone lemma is exported. *)
