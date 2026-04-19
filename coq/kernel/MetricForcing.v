(** MetricForcing: metric structure in the isotropic two-vertex pipeline.

  This file is narrower than the name makes it sound. I am not proving that
  every tensor everywhere in the VM must already be a spacetime metric. I am
  proving that in the isotropic two-vertex setup, if you want to read the
  pipeline geometrically, the usual Levi-Civita-style structure is forced.

  The argument breaks into the basic pieces you would expect: the determinant
  has to stay away from zero, the Christoffel expression is torsion-free when
  the metric is symmetric, the lowered identity holds, and under those same
  hypotheses the connection is unique in the Levi-Civita sense.

  So the claim is conditional but sharp. If someone wants to deny the metric
  reading in this setup, they need to produce a different interpretation that
  still satisfies the same downstream tensor identities. *)

(* INQUISITOR NOTE: proof-connectivity - closes the isotropic two-vertex gap
   between module_mu_tensor and the metric-style interpretation. *)

From Coq Require Import Reals List Arith.PeanoNat Lia Lra.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import MuCostModel.
From Kernel Require Import VMState.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MatrixAlgebra4.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import RiemannTensor4D.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import MuGravity.
From Kernel Require Import CurvedTensorPipeline.


(** For isotropic metric g = a·I₄, determinant is a⁴. *)
Theorem metric_det_isotropic : forall s v a,
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  metric_det_at_vertex s v = a * a * a * a.
Proof.
  intros s v a Hiso.
  unfold metric_det_at_vertex, metric_mat4_at_vertex.
  unfold mat4_det, det3, minor3, skip_idx, full_metric_at_vertex. simpl.
  repeat match goal with
  | |- context [INR (module_tensor_entry s v ?p ?q)] =>
    change (INR (module_tensor_entry s v p q)) with (full_metric_at_vertex s v p q);
    rewrite (Hiso p q ltac:(lia) ltac:(lia)); simpl Nat.eqb
  end.
  ring.
Qed.

(** When a > 0, metric determinant a^4 is strictly positive, so the isotropic
    metric is non-degenerate. *)
Corollary metric_det_isotropic_positive : forall s v a,
  a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  metric_det_at_vertex s v > 0.
Proof.
  intros s v a Ha Hiso.
  rewrite (metric_det_isotropic s v a Hiso).
  apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]|]; lra.
Qed.

(** When a = 0, determinant vanishes, so the geometric nondegeneracy premise
    fails for the isotropic metric. *)
Theorem degenerate_metric_det_zero : forall s v,
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = 0) ->
  metric_det_at_vertex s v = 0.
Proof.
  intros s v Hzero.
  assert (Hiso: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then 0 else 0).
  { intros i j Hi Hj. rewrite Hzero by assumption.
    destruct (i =? j)%nat; reflexivity. }
  rewrite (metric_det_isotropic s v 0 Hiso).
  ring.
Qed.

(** When det = 0, the Cramer-rule inverse used in Christoffel expressions
    reaches 0/0 on the diagonal. Coq totalizes real division, so this theorem
    records failure of the geometric nondegeneracy premise rather than runtime
    undefinedness. *)
Theorem degenerate_christoffel_undefined : forall s v,
  metric_det_at_vertex s v = 0 ->
  forall i, (i < 4)%nat ->
    inverse_metric_at_vertex s v i i = 0 / 0.
Proof.
  intros s v Hdet i Hi.
  unfold inverse_metric_at_vertex, mat4_inverse.
  unfold metric_det_at_vertex in Hdet.
  rewrite Hdet. unfold Rdiv. rewrite Rinv_0. ring.
Qed.


(** The curved_christoffel formula is:
    Γ^ρ_{μν}(v) = Σ_σ g^{ρσ}(v) · (∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν}) / 2

    Swapping μ↔ν gives:
    Γ^ρ_{νμ}(v) = Σ_σ g^{ρσ}(v) · (∂_ν g_{μσ} + ∂_μ g_{νσ} - ∂_σ g_{νμ}) / 2

    These are equal when g_{μν} = g_{νμ} (metric symmetry), because:
    - ∂_μ g_{νσ} + ∂_ν g_{μσ} is symmetric under μ↔ν (just reordering)
    - ∂_σ g_{μν} = ∂_σ g_{νμ} by metric symmetry *)

Theorem christoffel_torsion_free : forall s v w ρ μ ν,
  (v <> w)%nat ->
  (** Metric symmetry at all vertices *)
  (forall u i j, full_metric_at_vertex s u i j = full_metric_at_vertex s u j i) ->
  curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
  curved_christoffel s (two_vertex_sc v w) ρ ν μ v.
Proof.
  intros s v w ρ μ ν Hvw Hsym.
  unfold curved_christoffel, sum_4, sum_n.
  repeat rewrite (dd_at_v s v w _ _ Hvw).
  cbv beta.
  rewrite (Hsym w μ ν), (Hsym v μ ν).
  lra.
Qed.

(** Isotropic metrics are automatically symmetric. *)
Lemma isotropic_metric_symmetric : forall s v a,
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = full_metric_at_vertex s v j i.
Proof.
  intros s v a Hiso i j Hi Hj.
  rewrite (Hiso i j Hi Hj), (Hiso j i Hj Hi).
  destruct (i =? j)%nat eqn:Eij.
  - apply Nat.eqb_eq in Eij. subst. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in Eij.
    destruct (j =? i)%nat eqn:Eji.
    + apply Nat.eqb_eq in Eji. lia.
    + reflexivity.
Qed.


(** The lowered Christoffel symbol (contracted with metric):
    Γ_{σ,μν}(v) := Σ_τ g_{στ}(v) · Γ^τ_{μν}(v)

    For the Levi-Civita connection, this equals:
    (∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν}) / 2

    This is metric compatibility. We prove it for the isotropic 2-vertex case,
    where g = a·I and g^{-1} = (1/a)·I, making the contraction explicit. *)

Definition lowered_christoffel (s : VMState) (sc : SimplicialComplex4D)
    (σ μ ν : nat) (v : ModuleID) : R :=
  sum_4 (fun τ => full_metric_at_vertex s v σ τ *
                   curved_christoffel s sc τ μ ν v).

(** The "half-sum of derivatives", the right-hand side of the lowered identity. *)
Definition metric_derivative_halfsum (s : VMState) (sc : SimplicialComplex4D)
    (σ μ ν : nat) (v : ModuleID) : R :=
  (discrete_derivative s sc (fun w => full_metric_at_vertex s w ν σ) μ v +
   discrete_derivative s sc (fun w => full_metric_at_vertex s w μ σ) ν v -
   discrete_derivative s sc (fun w => full_metric_at_vertex s w μ ν) σ v) / 2.

(** METRIC COMPATIBILITY for isotropic 2-vertex:
    g_{στ} Γ^τ_{μν} = ½(∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν})

    Proof strategy: For g = a·I, the contraction g_{στ} Γ^τ = a · Γ^σ.
    The Christoffel has a factor g^{-1} = (1/a)·I, which cancels the a.
    So g_{στ}Γ^τ_{μν} = a · (1/a) · ½(∂g+∂g-∂g) = ½(∂g+∂g-∂g). *)
(* INQUISITOR NOTE: Metric compatibility - lowered Christoffel identity *)
Theorem christoffel_lowered_identity : forall s v w σ μ ν a,
  (v <> w)%nat -> a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then
      full_metric_at_vertex s w 0%nat 0%nat else 0) ->
  (σ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
  lowered_christoffel s (two_vertex_sc v w) σ μ ν v =
  metric_derivative_halfsum s (two_vertex_sc v w) σ μ ν v.
Proof.
  intros s v w σ μ ν a Hvw Ha Hiso_v Hiso_w Hσ Hμ Hν.
  unfold lowered_christoffel, metric_derivative_halfsum.
  (* Key algebraic identity:
     Σ_τ g(σ,τ) · Γ^τ_{μν}
     = Σ_τ g(σ,τ) · Σ_ξ g^{τξ} · (half_sum ξ)    [Christoffel definition]
     = Σ_ξ (Σ_τ g(σ,τ) · g^{τξ}) · (half_sum ξ)   [swap sums]
     = Σ_ξ δ(σ,ξ) · (half_sum ξ)                    [g·g^{-1} = I]
     = half_sum σ

     We prove this by direct computation: unfold Christoffel, swap sums,
     and use the metric identity g(σ,τ)·g^{τξ} = δ(σ,ξ). *)
  unfold curved_christoffel.
  (* Now left side is: Σ_τ g(σ,τ) * Σ_ξ g^{τξ} * half(ξ) *)
  unfold sum_4, sum_n.
  repeat rewrite (dd_at_v s v w _ _ Hvw).
  cbv beta.
  (* Rewrite all metric terms to isotropic form *)
  assert (Hginv: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then / a else 0).
  { apply inverse_metric_isotropic; assumption. }
  (* Rewrite inverse metric *)
  repeat match goal with
  | |- context [inverse_metric_at_vertex s v ?p ?q] =>
    rewrite (Hginv p q ltac:(lia) ltac:(lia))
  end.
  (* Rewrite forward metric on left side *)
  repeat match goal with
  | |- context [full_metric_at_vertex s v ?p ?q] =>
    rewrite (Hiso_v p q ltac:(lia) ltac:(lia))
  end.
  (* Rewrite w-metric *)
  set (b := full_metric_at_vertex s w 0%nat 0%nat).
  (* NOTE: We cannot use repeat match here because Hiso_w rewrites
     full_metric_at_vertex s w i j into a form containing
     full_metric_at_vertex s w 0 0, which re-matches the pattern.
     Instead, fold b after each rewrite to block the re-match. *)
  repeat match goal with
  | |- context [full_metric_at_vertex s w ?p ?q] =>
    first [
      (* Skip the (0,0) case which is already b *)
      constr_eq p 0%nat; constr_eq q 0%nat; fail 1
    | rewrite (Hiso_w p q ltac:(lia) ltac:(lia)); fold b
    ]
  end.
  simpl Nat.eqb.
  (* Destruct all indices to eliminate if-then-else, producing 64 concrete goals *)
  destruct σ as [|[|[|[|?]]]]; try lia;
  destruct μ as [|[|[|[|?]]]]; try lia;
  destruct ν as [|[|[|[|?]]]]; try lia;
  simpl; field; lra.
Qed.


(** Levi-Civita-style uniqueness in the isotropic two-vertex case:

    If Γ' is ANY connection (nat → nat → nat → R) that satisfies:
    (a) Torsion-freedom: Γ'(ρ,μ,ν) = Γ'(ρ,ν,μ)
    (b) Lowered identity: Σ_τ g(σ,τ)·Γ'(τ,μ,ν) = ½(∂_μ g_{νσ}+∂_ν g_{μσ}−∂_σ g_{μν})

    Then Γ' = curved_christoffel (the pipeline's connection).

    Proof sketch:
    From (b), multiplying both sides by g^{σρ} and summing over σ:
    Σ_σ g^{σρ} · Σ_τ g(σ,τ) · Γ'(τ,μ,ν) = Σ_σ g^{σρ} · RHS_σ
    LHS = Σ_τ (Σ_σ g^{σρ}·g(σ,τ)) · Γ'(τ,μ,ν) = Σ_τ δ^ρ_τ · Γ'(τ,μ,ν) = Γ'(ρ,μ,ν)
    RHS = Σ_σ g^{σρ} · ½(∂g+∂g-∂g)_σ = curved_christoffel ρ μ ν  *)

(** Helper: isotropic g·g^{-1} = identity *)
Lemma isotropic_metric_inverse_identity : forall s v a,
  a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  forall σ τ, (σ < 4)%nat -> (τ < 4)%nat ->
    sum_4 (fun ρ => inverse_metric_at_vertex s v σ ρ *
                     full_metric_at_vertex s v ρ τ) =
    (if (σ =? τ)%nat then 1 else 0).
Proof.
  intros s v a Ha Hiso σ τ Hσ Hτ.
  assert (Hginv: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then / a else 0).
  { apply inverse_metric_isotropic; assumption. }
  unfold sum_4, sum_n.
  rewrite (Hginv σ 0%nat Hσ ltac:(lia)),
          (Hginv σ 1%nat Hσ ltac:(lia)),
          (Hginv σ 2%nat Hσ ltac:(lia)),
          (Hginv σ 3%nat Hσ ltac:(lia)).
  rewrite (Hiso 0%nat τ ltac:(lia) Hτ),
          (Hiso 1%nat τ ltac:(lia) Hτ),
          (Hiso 2%nat τ ltac:(lia) Hτ),
          (Hiso 3%nat τ ltac:(lia) Hτ).
  destruct σ as [|[|[|[|?]]]]; try lia;
  destruct τ as [|[|[|[|?]]]]; try lia;
  simpl; field; lra.
Qed.

(** Symmetric helper: g·g^{-1} = identity (in the other order) *)
Lemma isotropic_metric_identity_other : forall s v a,
  a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  forall σ τ, (σ < 4)%nat -> (τ < 4)%nat ->
    sum_4 (fun ρ => full_metric_at_vertex s v σ ρ *
                     inverse_metric_at_vertex s v ρ τ) =
    (if (σ =? τ)%nat then 1 else 0).
Proof.
  intros s v a Ha Hiso σ τ Hσ Hτ.
  assert (Hginv: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then / a else 0).
  { apply inverse_metric_isotropic; assumption. }
  unfold sum_4, sum_n.
  rewrite (Hiso σ 0%nat Hσ ltac:(lia)),
          (Hiso σ 1%nat Hσ ltac:(lia)),
          (Hiso σ 2%nat Hσ ltac:(lia)),
          (Hiso σ 3%nat Hσ ltac:(lia)).
  rewrite (Hginv 0%nat τ ltac:(lia) Hτ),
          (Hginv 1%nat τ ltac:(lia) Hτ),
          (Hginv 2%nat τ ltac:(lia) Hτ),
          (Hginv 3%nat τ ltac:(lia) Hτ).
  destruct σ as [|[|[|[|?]]]]; try lia;
  destruct τ as [|[|[|[|?]]]]; try lia;
  simpl; field; lra.
Qed.

(** LEVI-CIVITA-STYLE UNIQUENESS: Any connection satisfying torsion-freedom
    and the lowered identity equals the pipeline's Christoffel. *)
(* INQUISITOR NOTE: Levi-Civita uniqueness - isotropic two-vertex theorem *)
Theorem levi_civita_uniqueness : forall s v w a,
  (v <> w)%nat -> a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then
      full_metric_at_vertex s w 0%nat 0%nat else 0) ->
  forall (Gamma' : nat -> nat -> nat -> R),
  (** Γ' is torsion-free *)
  (forall ρ μ ν, Gamma' ρ μ ν = Gamma' ρ ν μ) ->
  (** Γ' satisfies the lowered identity *)
  (forall σ μ ν, (σ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    sum_4 (fun τ => full_metric_at_vertex s v σ τ * Gamma' τ μ ν) =
    metric_derivative_halfsum s (two_vertex_sc v w) σ μ ν v) ->
  (** Then Γ' equals the pipeline's Christoffel *)
  forall ρ μ ν, (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    Gamma' ρ μ ν = curved_christoffel s (two_vertex_sc v w) ρ μ ν v.
Proof.
  intros s v w a Hvw Ha Hiso_v Hiso_w Gamma' Htorsion Hlowered ρ μ ν Hρ Hμ Hν.
  set (b := full_metric_at_vertex s w 0%nat 0%nat).
  assert (Hiso_w': forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0).
  { intros. apply Hiso_w; assumption. }
  (* Key step: contract the lowered identity with g^{-1} to recover Γ' *)
  assert (Hginv: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s v i j = if (i =? j)%nat then / a else 0).
  { apply inverse_metric_isotropic; assumption. }
  (* The proof goes via the intermediate form:
     Gamma'(ρ,μ,ν) = Σ_σ g⁻¹(ρ,σ) · metric_derivative_halfsum(σ,μ,ν)
                    = curved_christoffel(ρ,μ,ν)  [by definition]

     For the first equality, from Hlowered:
       Σ_τ g(σ,τ)·Gamma'(τ,μ,ν) = metric_derivative_halfsum(σ,μ,ν)
     For isotropic g = a·I, this gives a·Gamma'(σ,μ,ν) = md_hs(σ,μ,ν).
     So Gamma'(σ,μ,ν) = (1/a)·md_hs(σ,μ,ν).
     And curved_christoffel(ρ,μ,ν) = Σ_σ g⁻¹(ρ,σ)·md_hs(σ,μ,ν)
       = (1/a)·md_hs(ρ,μ,ν)  [isotropic g⁻¹].
     These are equal. *)

  (* Step A: extract Gamma' = (1/a) · md_hs from Hlowered *)
  assert (HGamma_eq: forall k, (k < 4)%nat ->
    Gamma' k μ ν = / a * metric_derivative_halfsum s (two_vertex_sc v w) k μ ν v).
  { intros k Hk.
    assert (Hlow := Hlowered k μ ν Hk Hμ Hν).
    unfold sum_4, sum_n in Hlow.
    rewrite (Hiso_v k 0%nat Hk ltac:(lia)),
            (Hiso_v k 1%nat Hk ltac:(lia)),
            (Hiso_v k 2%nat Hk ltac:(lia)),
            (Hiso_v k 3%nat Hk ltac:(lia)) in Hlow.
    (* Now Hlow: (if k=?0 then a else 0)*Gamma'(0,...) + ... = md_hs *)
    (* After destruct k and simpl, this becomes a*Gamma'(k,...) = md_hs *)
    destruct k as [|[|[|[|?]]]]; try lia;
    simpl Nat.eqb in Hlow; simpl in Hlow;
    (* Goal: Gamma' k μ ν = /a * md_hs; Hlow: a * Gamma' k μ ν = md_hs *)
    rewrite <- Hlow; field; lra. }

  (* Step B: curved_christoffel = (1/a) · md_hs at isotropic ρ *)
  rewrite (HGamma_eq ρ Hρ).
  (* Express curved_christoffel as sum of g⁻¹ · md_hs (definitional equality) *)
  change (curved_christoffel s (two_vertex_sc v w) ρ μ ν v) with
    (sum_4 (fun σ => inverse_metric_at_vertex s v ρ σ *
      metric_derivative_halfsum s (two_vertex_sc v w) σ μ ν v)).
  (* Unfold only the sum structure *)
  unfold sum_4, sum_n.
  (* Rewrite g⁻¹ to isotropic form *)
  rewrite (Hginv ρ 0%nat Hρ ltac:(lia)),
          (Hginv ρ 1%nat Hρ ltac:(lia)),
          (Hginv ρ 2%nat Hρ ltac:(lia)),
          (Hginv ρ 3%nat Hρ ltac:(lia)).
  destruct ρ as [|[|[|[|?]]]]; try lia; simpl Nat.eqb;
  (* Reduce if true/false *)
  repeat match goal with
  | |- context C [if true then ?x else ?y] =>
    change (if true then x else y) with x
  | |- context C [if false then ?x else ?y] =>
    change (if false then x else y) with y
  end;
  ring.
Qed.

(** The torsion-freedom proof for the 2-vertex complex does not need the
    global metric symmetry hypothesis; it follows directly from the
    isotropic structure at v and w (the only vertices that matter). *)
Theorem christoffel_torsion_free_isotropic : forall s v w a b ρ μ ν,
  (v <> w)%nat -> a > 0 ->
  (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0) ->
  curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
  curved_christoffel s (two_vertex_sc v w) ρ ν μ v.
Proof.
  intros s v w a b ρ μ ν Hvw Ha Hρ Hμ Hν Hiso_v Hiso_w.
  rewrite (curved_christoffel_isotropic_2v s v w a b ρ μ ν Hvw Ha Hiso_v Hiso_w Hρ Hμ Hν).
  rewrite (curved_christoffel_isotropic_2v s v w a b ρ ν μ Hvw Ha Hiso_v Hiso_w Hρ Hν Hμ).
  rewrite (Nat.eqb_sym ν μ). ring.
Qed.

(**
    MAIN THEOREM (COMPLETE, NO ADMITS)
    *)

(** metric_structure_forced: Full proof without admits.
    For any isotropic 2-vertex complex, the pipeline forces:
    (1) non-degeneracy, (2) torsion-freedom, (3) metric compatibility,
    (4) Levi-Civita uniqueness. *)
(* INQUISITOR NOTE: Main forcing theorem for the isotropic two-vertex forcing
  result proved in this file. *)
Theorem metric_structure_forced : forall s v w a b,
  (v <> w)%nat -> a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0) ->

  (** 1. Non-degeneracy *)
  metric_det_at_vertex s v > 0

  /\

  (** 2. Torsion-freedom *)
  (forall ρ μ ν, (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
    curved_christoffel s (two_vertex_sc v w) ρ ν μ v)

  /\

  (** 3. Metric compatibility *)
  (forall σ μ ν, (σ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
    lowered_christoffel s (two_vertex_sc v w) σ μ ν v =
    metric_derivative_halfsum s (two_vertex_sc v w) σ μ ν v)

  /\

  (** 4. Levi-Civita uniqueness *)
  (forall Gamma' : nat -> nat -> nat -> R,
    (forall ρ μ ν, Gamma' ρ μ ν = Gamma' ρ ν μ) ->
    (forall σ μ ν, (σ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
      sum_4 (fun τ => full_metric_at_vertex s v σ τ * Gamma' τ μ ν) =
      metric_derivative_halfsum s (two_vertex_sc v w) σ μ ν v) ->
    forall ρ μ ν, (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
      Gamma' ρ μ ν = curved_christoffel s (two_vertex_sc v w) ρ μ ν v).
Proof.
  intros s v w a b Hvw Ha Hiso_v Hiso_w.
  assert (Hiso_w_compat: forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then
      full_metric_at_vertex s w 0%nat 0%nat else 0).
  { intros i j Hi Hj. rewrite (Hiso_w i j Hi Hj).
    destruct (i =? j)%nat eqn:E.
    - rewrite (Hiso_w 0%nat 0%nat ltac:(lia) ltac:(lia)). simpl. reflexivity.
    - reflexivity. }
  repeat split.
  (* 1. Non-degeneracy *)
  - exact (metric_det_isotropic_positive s v a Ha Hiso_v).
  (* 2. Torsion-freedom *)
  - intros ρ μ ν Hρ Hμ Hν.
    exact (christoffel_torsion_free_isotropic s v w a b ρ μ ν Hvw Ha Hρ Hμ Hν Hiso_v Hiso_w).
  (* 3. Metric compatibility *)
  - intros σ μ ν Hσ Hμ Hν.
    exact (christoffel_lowered_identity s v w σ μ ν a Hvw Ha Hiso_v Hiso_w_compat Hσ Hμ Hν).
  (* 4. Uniqueness *)
  - intros Gamma' Htorsion Hlowered ρ μ ν Hρ Hμ Hν.
    exact (levi_civita_uniqueness s v w a Hvw Ha Hiso_v Hiso_w_compat
             Gamma' Htorsion Hlowered ρ μ ν Hρ Hμ Hν).
Qed.

(**
    COROLLARY: Connecting to the Einstein equation chain
    *)

(** The forcing theorem can be paired with the diagonal Einstein equation chain:
    metric_structure_forced supplies the isotropic two-vertex geometric
    conditions, and einstein_equation_from_mass supplies the diagonal
    G = κ·T statement. This is not a full metric-forcing theorem for arbitrary
    tensors. *)
(* INQUISITOR NOTE: Connects metric forcing to Einstein equation chain *)
Corollary forcing_implies_einstein : forall s v w,
  (v <> w)%nat ->
  isotropic_mass_metric s v ->
  isotropic_mass_metric s w ->
  (module_structural_mass s v > 0)%nat ->
  (** The geometry is forced AND the Einstein equation holds *)
  metric_det_at_vertex s v > 0 /\
  exists κ : R,
    forall d, (d < 4)%nat ->
      curved_einstein s (two_vertex_sc v w) d d v =
      κ * mass_stress_energy s d d v.
Proof.
  intros s v w Hvw Hphys_v Hphys_w Hmass.
  set (a := INR (module_structural_mass s v)).
  assert (Ha: a > 0) by (unfold a; apply lt_0_INR; lia).
  split.
  - (* Non-degeneracy from forcing *)
    assert (Hiso: forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0).
    { intros. apply isotropic_mass_metric_diag; auto. }
    exact (metric_det_isotropic_positive s v a Ha Hiso).
  - (* Einstein equation from CurvedTensorPipeline *)
    exact (einstein_equation_from_mass s v w Hvw Hphys_v Hphys_w Hmass).
Qed.

(** Independence witness: this file's theorems use ONLY:
    - per-module tensor data (module_mu_tensor → full_metric_at_vertex)
    - pipeline definitions (curved_christoffel from CurvedTensorPipeline)
    - matrix algebra (inverse_metric_at_vertex from MatrixAlgebra4)
    No additional axioms or hypotheses about spacetime. *)
Definition metric_forcing_independence_witness :=
  (metric_structure_forced, levi_civita_uniqueness,
   christoffel_lowered_identity, christoffel_torsion_free_isotropic).
