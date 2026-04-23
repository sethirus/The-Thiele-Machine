From Coq Require Import Reals Lra Lia List Bool Field FunctionalExtensionality.
Import ListNotations.

From Kernel Require Import VMState FourDSimplicialComplex.
From Kernel Require Import EinsteinEquations4D.
From Kernel Require Import MatrixAlgebra4 MetricFromMuCosts CurvedTensorPipeline.
From Kernel Require Import MuGravity.
From Kernel Require Import DiscreteSimplicialGeometry.

Open Scope R_scope.

(** SymmetricDerivative4D.v

    Draft redesign scaffold for the discrete derivative used by the curvature
    pipeline. The active pipeline in [RiemannTensor4D.v] uses first-neighbor
    semantics: scan the filtered vertex list, take the first matching witness,
    and return [f(w) - f(v)].

    This file does not replace that operator. It defines an alternative local
    derivative that:

    - excludes self-neighbors,
    - aggregates over all matching adjacent vertices, and
    - averages their directional differences.

    The goal is not to claim that this operator is correct physics. The goal is
    to make the redesign surface explicit and machine-check the first exact
    formulas that such a redesign would need on the same witness complexes the
    current proofs already use.

    ZERO PROJECT-LOCAL AXIOMS. NO SHORTCUTS.
*)

Definition matching_neighbors_except_self
  (sc : SimplicialComplex4D) (μ v : ModuleID) : list ModuleID :=
  filter (fun w =>
    negb (w =? v) &&
    existsb (fun e =>
      let verts := e1d_vertices e in
      let dir_ok := match e1d_direction e with
                    | None => true
                    | Some d => (d =? μ)%bool
                    end in
      dir_ok && nat_list_mem v verts && nat_list_mem w verts
    ) (sc4d_edges sc)
  ) (sc4d_vertices sc).

Definition rsum (xs : list R) : R :=
  fold_right Rplus 0 xs.

Definition symmetric_discrete_derivative
  (s : VMState) (sc : SimplicialComplex4D)
  (f : ModuleID -> R) (μ v : ModuleID) : R :=
  let neighbors := matching_neighbors_except_self sc μ v in
  match neighbors with
  | [] => 0
  | _ => rsum (map (fun w => f w - f v) neighbors) / INR (length neighbors)
  end.

Lemma matching_neighbors_two_vertex_at_v : forall v w μ,
  v <> w ->
  matching_neighbors_except_self (two_vertex_sc v w) μ v = [w].
Proof.
  intros v w μ Hvw.
  unfold matching_neighbors_except_self, two_vertex_sc.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (w =? v) eqn:Ewv.
  { apply Nat.eqb_eq in Ewv. exfalso. apply Hvw. symmetry. exact Ewv. }
  destruct (v =? v) eqn:Evv.
  2: { rewrite Nat.eqb_refl in Evv. discriminate. }
  destruct (w =? w) eqn:Eww.
  2: { rewrite Nat.eqb_refl in Eww. discriminate. }
  destruct (v =? w) eqn:Evw.
  { apply Nat.eqb_eq in Evw. exfalso. apply Hvw. exact Evw. }
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_two_vertex_at_w : forall v w μ,
  v <> w ->
  matching_neighbors_except_self (two_vertex_sc v w) μ w = [v].
Proof.
  intros v w μ Hvw.
  unfold matching_neighbors_except_self, two_vertex_sc.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (w =? w) eqn:Eww.
  2: { rewrite Nat.eqb_refl in Eww. discriminate. }
  destruct (v =? w) eqn:Evw.
  { apply Nat.eqb_eq in Evw. exfalso. apply Hvw. exact Evw. }
  destruct (w =? v) eqn:Ewv.
  { apply Nat.eqb_eq in Ewv. exfalso. apply Hvw. symmetry. exact Ewv. }
  destruct (v =? v) eqn:Evv.
  2: { rewrite Nat.eqb_refl in Evv. discriminate. }
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_three_at_u : forall u v w μ,
  u <> v -> u <> w -> v <> w ->
  matching_neighbors_except_self (three_vertex_chain_sc u v w) μ u = [v].
Proof.
  intros u v w μ Huv Huw Hvw.
  unfold matching_neighbors_except_self, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_three_at_v : forall u v w μ,
  u <> v -> u <> w -> v <> w ->
  matching_neighbors_except_self (three_vertex_chain_sc u v w) μ v = [w; u].
Proof.
  intros u v w μ Huv Huw Hvw.
  unfold matching_neighbors_except_self, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_three_at_w : forall u v w μ,
  u <> v -> u <> w -> v <> w ->
  matching_neighbors_except_self (three_vertex_chain_sc u v w) μ w = [v].
Proof.
  intros u v w μ Huv Huw Hvw.
  unfold matching_neighbors_except_self, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. reflexivity.
Qed.

Lemma symmetric_dd_two_vertex_at_v : forall s v w f μ,
  v <> w ->
  symmetric_discrete_derivative s (two_vertex_sc v w) f μ v = (f w - f v)%R.
Proof.
  intros s v w f μ Hvw.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_two_vertex_at_v by assumption.
  simpl. field.
Qed.

Lemma symmetric_dd_two_vertex_at_w : forall s v w f μ,
  v <> w ->
  symmetric_discrete_derivative s (two_vertex_sc v w) f μ w = (f v - f w)%R.
Proof.
  intros s v w f μ Hvw.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_two_vertex_at_w by assumption.
  simpl. field.
Qed.

Lemma symmetric_dd_two_vertex_balanced : forall s v w f μ,
  v <> w ->
  (symmetric_discrete_derivative s (two_vertex_sc v w) f μ v +
   symmetric_discrete_derivative s (two_vertex_sc v w) f μ w)%R = 0%R.
Proof.
  intros s v w f μ Hvw.
  rewrite symmetric_dd_two_vertex_at_v by assumption.
  rewrite symmetric_dd_two_vertex_at_w by assumption.
  ring.
Qed.

Lemma symmetric_dd_three_vertex_at_u : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  symmetric_discrete_derivative s (three_vertex_chain_sc u v w) f μ u =
  (f v - f u)%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_three_at_u by assumption.
  simpl. field.
Qed.

Lemma symmetric_dd_three_vertex_at_v : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  symmetric_discrete_derivative s (three_vertex_chain_sc u v w) f μ v =
  (((f w - f v) + (f u - f v)) / 2)%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_three_at_v by assumption.
  simpl. field.
Qed.

Lemma symmetric_dd_three_vertex_at_w : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  symmetric_discrete_derivative s (three_vertex_chain_sc u v w) f μ w =
  (f v - f w)%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_three_at_w by assumption.
  simpl. field.
Qed.

Lemma symmetric_dd_three_vertex_middle_uses_both_sides : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  (2 * symmetric_discrete_derivative s (three_vertex_chain_sc u v w) f μ v)%R =
  ((f w - f v) + (f u - f v))%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  rewrite symmetric_dd_three_vertex_at_v by assumption.
  field.
Qed.

Definition symmetric_metric_derivative_halfsum
  (s : VMState) (sc : SimplicialComplex4D)
  (σ μ ν : nat) (v : ModuleID) : R :=
  (symmetric_discrete_derivative s sc (fun w => full_metric_at_vertex s w ν σ) μ v +
   symmetric_discrete_derivative s sc (fun w => full_metric_at_vertex s w μ σ) ν v -
   symmetric_discrete_derivative s sc (fun w => full_metric_at_vertex s w μ ν) σ v) / 2.

Definition symmetric_curved_christoffel
  (s : VMState) (sc : SimplicialComplex4D)
  (ρ μ ν : nat) (v : ModuleID) : R :=
  let g_inv := inverse_metric_at_vertex s v in
  sum_4 (fun σ =>
    g_inv ρ σ * symmetric_metric_derivative_halfsum s sc σ μ ν v).

Theorem symmetric_curved_christoffel_two_vertex_at_v_eq_curved : forall s v w ρ μ ν,
  (v <> w)%nat ->
  symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
  curved_christoffel s (two_vertex_sc v w) ρ μ ν v.
Proof.
  intros s v w ρ μ ν Hvw.
  unfold symmetric_curved_christoffel, curved_christoffel,
         symmetric_metric_derivative_halfsum.
  unfold sum_4, sum_n.
  repeat rewrite symmetric_dd_two_vertex_at_v by assumption.
  repeat rewrite dd_at_v by assumption.
  ring.
Qed.

Theorem symmetric_curved_christoffel_isotropic_2v : forall s v w a b (ρ μ ν : nat),
  (v <> w)%nat -> a > 0 ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
  (forall i j, (i < 4)%nat -> (j < 4)%nat ->
    full_metric_at_vertex s w i j = if (i =? j)%nat then b else 0) ->
  (ρ < 4)%nat -> (μ < 4)%nat -> (ν < 4)%nat ->
  symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ ν v =
    ((b - a) / (2 * a)) *
    ((if (ν =? ρ)%nat then 1 else 0) +
     (if (μ =? ρ)%nat then 1 else 0) -
     (if (μ =? ν)%nat then 1 else 0)).
Proof.
  intros s v w a b ρ μ ν Hvw Ha Hiso_v Hiso_w Hρ Hμ Hν.
  rewrite symmetric_curved_christoffel_two_vertex_at_v_eq_curved by assumption.
  apply (curved_christoffel_isotropic_2v s v w a b ρ μ ν);
    assumption.
Qed.

Theorem symmetric_metric_derivative_halfsum_three_at_v_uses_both_sides :
  forall s u v w σ μ ν,
  u <> v -> u <> w -> v <> w ->
  (4 * symmetric_metric_derivative_halfsum s (three_vertex_chain_sc u v w) σ μ ν v)%R =
  ((full_metric_at_vertex s w ν σ - full_metric_at_vertex s v ν σ) +
   (full_metric_at_vertex s u ν σ - full_metric_at_vertex s v ν σ) +
   (full_metric_at_vertex s w μ σ - full_metric_at_vertex s v μ σ) +
   (full_metric_at_vertex s u μ σ - full_metric_at_vertex s v μ σ) -
   (full_metric_at_vertex s w μ ν - full_metric_at_vertex s v μ ν) -
   (full_metric_at_vertex s u μ ν - full_metric_at_vertex s v μ ν))%R.
Proof.
  intros s u v w σ μ ν Huv Huw Hvw.
  unfold symmetric_metric_derivative_halfsum.
  repeat rewrite symmetric_dd_three_vertex_at_v by assumption.
  field.
Qed.

Definition symmetric_curved_riemann
  (s : VMState) (sc : SimplicialComplex4D)
  (ρ σ μ ν : nat) (v : ModuleID) : R :=
  symmetric_discrete_derivative s sc
    (fun w => symmetric_curved_christoffel s sc ρ ν σ w) μ v -
  symmetric_discrete_derivative s sc
    (fun w => symmetric_curved_christoffel s sc ρ μ σ w) ν v +
  sum_4 (fun λ =>
    symmetric_curved_christoffel s sc ρ μ λ v *
    symmetric_curved_christoffel s sc λ ν σ v) -
  sum_4 (fun λ =>
    symmetric_curved_christoffel s sc ρ ν λ v *
    symmetric_curved_christoffel s sc λ μ σ v).

Definition symmetric_curved_ricci
  (s : VMState) (sc : SimplicialComplex4D)
  (μ ν : nat) (v : ModuleID) : R :=
  sum_4 (fun ρ => symmetric_curved_riemann s sc ρ μ ρ ν v).

Definition symmetric_curved_ricci_scalar
  (s : VMState) (sc : SimplicialComplex4D)
  (v : ModuleID) : R :=
  let g_inv := inverse_metric_at_vertex s v in
  sum_4 (fun μ => sum_4 (fun ν => g_inv μ ν * symmetric_curved_ricci s sc μ ν v)).

Definition symmetric_curved_einstein
  (s : VMState) (sc : SimplicialComplex4D)
  (μ ν : nat) (v : ModuleID) : R :=
  symmetric_curved_ricci s sc μ ν v -
  (1 / 2) * full_metric_at_vertex s v μ ν * symmetric_curved_ricci_scalar s sc v.

Lemma symmetric_dd_constant : forall s sc c μ v,
  symmetric_discrete_derivative s sc (fun _ => c) μ v = 0%R.
Proof.
  intros s sc c μ v.
  unfold symmetric_discrete_derivative.
  destruct (matching_neighbors_except_self sc μ v) as [|w neighbors] eqn:Hneighbors.
  - reflexivity.
  - assert (Hsum : rsum (map (fun w0 : ModuleID => (fun _ => c) w0 - (fun _ => c) v)
                             (w :: neighbors)) = 0%R).
    { replace (map (fun w0 : ModuleID => (fun _ => c) w0 - (fun _ => c) v) (w :: neighbors))
        with (map (fun _ : ModuleID => 0%R) (w :: neighbors)).
      2:{ f_equal. apply functional_extensionality. intro w0. ring. }
      assert (Hzero_map : forall ys : list ModuleID,
        rsum (map (fun _ : ModuleID => 0%R) ys) = 0%R).
      { intro ys. induction ys as [|x xs IH]; simpl.
        - reflexivity.
        - rewrite IH. ring. }
      exact (Hzero_map (w :: neighbors)). }
    rewrite Hsum.
    field.
    apply not_0_INR. discriminate.
Qed.

Lemma symmetric_dd_two_vertex_position_independent : forall s v w f μ x,
  (v <> w)%nat ->
  (x = v \/ x = w) ->
  f v = f w ->
  symmetric_discrete_derivative s (two_vertex_sc v w) f μ x = 0%R.
Proof.
  intros s v w f μ x Hvw Hx Hconst.
  destruct Hx as [-> | ->].
  - rewrite symmetric_dd_two_vertex_at_v by assumption.
    rewrite Hconst. ring.
  - rewrite symmetric_dd_two_vertex_at_w by assumption.
    rewrite Hconst. ring.
Qed.

Theorem symmetric_curved_christoffel_uniform_zero_two_vertex_at_v : forall s v w ρ μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ ν v = 0%R.
Proof.
  intros s v w ρ μ ν Hvw Huniform.
  unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
  assert (Hd1 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 0%nat) μ v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd2 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 0%nat) ν v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd3 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 0%nat v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd4 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 1%nat) μ v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd5 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 1%nat) ν v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd6 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 1%nat v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd7 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 2%nat) μ v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd8 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 2%nat) ν v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd9 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 2%nat v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd10 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 3%nat) μ v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd11 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 3%nat) ν v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  assert (Hd12 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 3%nat v = 0%R).
  { rewrite symmetric_dd_two_vertex_at_v by assumption. rewrite Huniform. ring. }
  unfold sum_4, sum_n.
  rewrite Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7, Hd8, Hd9, Hd10, Hd11, Hd12.
  field_simplify. lra.
Qed.

Theorem symmetric_curved_christoffel_uniform_zero_two_vertex_at_w : forall s v w ρ μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ ν w = 0%R.
Proof.
  intros s v w ρ μ ν Hvw Huniform.
  unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
  assert (Hd1 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 0%nat) μ w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd2 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 0%nat) ν w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd3 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 0%nat w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd4 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 1%nat) μ w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd5 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 1%nat) ν w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd6 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 1%nat w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd7 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 2%nat) μ w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd8 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 2%nat) ν w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd9 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 2%nat w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd10 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x ν 3%nat) μ w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd11 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ 3%nat) ν w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  assert (Hd12 : symmetric_discrete_derivative s (two_vertex_sc v w)
      (fun x => full_metric_at_vertex s x μ ν) 3%nat w = 0%R).
  { rewrite symmetric_dd_two_vertex_at_w by assumption. rewrite Huniform. ring. }
  unfold sum_4, sum_n.
  rewrite Hd1, Hd2, Hd3, Hd4, Hd5, Hd6, Hd7, Hd8, Hd9, Hd10, Hd11, Hd12.
  field_simplify. lra.
Qed.

Theorem symmetric_curved_riemann_uniform_zero_two_vertex_at_v : forall s v w ρ σ μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_riemann s (two_vertex_sc v w) ρ σ μ ν v = 0%R.
Proof.
  intros s v w ρ σ μ ν Hvw Huniform.
  unfold symmetric_curved_riemann.
  set (dmu_gamma := symmetric_discrete_derivative s (two_vertex_sc v w)
    (fun x => symmetric_curved_christoffel s (two_vertex_sc v w) ρ ν σ x) μ v).
  set (dnu_gamma := symmetric_discrete_derivative s (two_vertex_sc v w)
    (fun x => symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ σ x) ν v).
  assert (Hdmu : dmu_gamma = 0%R).
  { unfold dmu_gamma.
    apply (symmetric_dd_two_vertex_position_independent s v w
             (fun x => symmetric_curved_christoffel s (two_vertex_sc v w) ρ ν σ x)
             μ v Hvw (or_introl eq_refl)).
    rewrite symmetric_curved_christoffel_uniform_zero_two_vertex_at_v by assumption.
    rewrite symmetric_curved_christoffel_uniform_zero_two_vertex_at_w by assumption.
    reflexivity. }
  assert (Hdnu : dnu_gamma = 0%R).
  { unfold dnu_gamma.
    apply (symmetric_dd_two_vertex_position_independent s v w
             (fun x => symmetric_curved_christoffel s (two_vertex_sc v w) ρ μ σ x)
             ν v Hvw (or_introl eq_refl)).
    rewrite symmetric_curved_christoffel_uniform_zero_two_vertex_at_v by assumption.
    rewrite symmetric_curved_christoffel_uniform_zero_two_vertex_at_w by assumption.
    reflexivity. }
  rewrite Hdmu, Hdnu.
  unfold sum_4, sum_n.
  repeat rewrite symmetric_curved_christoffel_uniform_zero_two_vertex_at_v by assumption.
  ring.
Qed.

Theorem symmetric_curved_ricci_uniform_zero_two_vertex_at_v : forall s v w μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_ricci s (two_vertex_sc v w) μ ν v = 0%R.
Proof.
  intros s v w μ ν Hvw Huniform.
  unfold symmetric_curved_ricci, sum_4, sum_n.
  repeat rewrite symmetric_curved_riemann_uniform_zero_two_vertex_at_v by assumption.
  ring.
Qed.

Theorem symmetric_curved_ricci_scalar_uniform_zero_two_vertex_at_v : forall s v w,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_ricci_scalar s (two_vertex_sc v w) v = 0%R.
Proof.
  intros s v w Hvw Huniform.
  unfold symmetric_curved_ricci_scalar, sum_4, sum_n.
  repeat rewrite symmetric_curved_ricci_uniform_zero_two_vertex_at_v by assumption.
  nra.
Qed.

Theorem symmetric_curved_einstein_uniform_zero_two_vertex_at_v : forall s v w μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_einstein s (two_vertex_sc v w) μ ν v = 0%R.
Proof.
  intros s v w μ ν Hvw Huniform.
  unfold symmetric_curved_einstein.
  rewrite symmetric_curved_ricci_uniform_zero_two_vertex_at_v by assumption.
  rewrite symmetric_curved_ricci_scalar_uniform_zero_two_vertex_at_v by assumption.
  nra.
Qed.

Theorem symmetric_full_efe_uniform_two_vertex : forall s v w μ ν,
  (v <> w)%nat ->
  (forall i j, full_metric_at_vertex s v i j = full_metric_at_vertex s w i j) ->
  symmetric_curved_einstein s (two_vertex_sc v w) μ ν v =
  (0 * mass_stress_energy s μ ν v)%R.
Proof.
  intros s v w μ ν Hvw Huniform.
  rewrite symmetric_curved_einstein_uniform_zero_two_vertex_at_v by assumption.
  nra.
Qed.

Lemma matching_neighbors_boundary_4simplex_at_1 : forall μ,
  matching_neighbors_except_self boundary_4simplex μ 1%nat = [0%nat; 2%nat; 3%nat; 4%nat].
Proof.
  intro μ.
  unfold matching_neighbors_except_self, boundary_4simplex.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (0 =? 1) eqn:E01; [apply Nat.eqb_eq in E01; lia|].
  destruct (1 =? 0) eqn:E10; [apply Nat.eqb_eq in E10; lia|].
  destruct (2 =? 1) eqn:E21; [apply Nat.eqb_eq in E21; lia|].
  destruct (1 =? 1) eqn:E11; [|rewrite Nat.eqb_refl in E11; discriminate].
  destruct (3 =? 1) eqn:E31; [apply Nat.eqb_eq in E31; lia|].
  destruct (4 =? 1) eqn:E41; [apply Nat.eqb_eq in E41; lia|].
  simpl. reflexivity.
Qed.

Lemma symmetric_dd_boundary_4simplex_at_1 : forall s f μ,
  symmetric_discrete_derivative s boundary_4simplex f μ 1%nat =
  (((f 0%nat - f 1%nat) + (f 2%nat - f 1%nat) +
    (f 3%nat - f 1%nat) + (f 4%nat - f 1%nat)) / 4)%R.
Proof.
  intros s f μ.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_boundary_4simplex_at_1.
  simpl.
  field.
Qed.

Lemma matching_neighbors_boundary_4simplex_at_0 : forall μ,
  matching_neighbors_except_self boundary_4simplex μ 0%nat = [1%nat; 2%nat; 3%nat; 4%nat].
Proof.
  intro μ.
  unfold matching_neighbors_except_self, boundary_4simplex.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (0 =? 0) eqn:E00; [|rewrite Nat.eqb_refl in E00; discriminate].
  destruct (1 =? 0) eqn:E10; [apply Nat.eqb_eq in E10; lia|].
  destruct (2 =? 0) eqn:E20; [apply Nat.eqb_eq in E20; lia|].
  destruct (3 =? 0) eqn:E30; [apply Nat.eqb_eq in E30; lia|].
  destruct (4 =? 0) eqn:E40; [apply Nat.eqb_eq in E40; lia|].
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_boundary_4simplex_at_2 : forall μ,
  matching_neighbors_except_self boundary_4simplex μ 2%nat = [0%nat; 1%nat; 3%nat; 4%nat].
Proof.
  intro μ.
  unfold matching_neighbors_except_self, boundary_4simplex.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (0 =? 2) eqn:E02; [apply Nat.eqb_eq in E02; lia|].
  destruct (2 =? 0) eqn:E20; [apply Nat.eqb_eq in E20; lia|].
  destruct (1 =? 2) eqn:E12; [apply Nat.eqb_eq in E12; lia|].
  destruct (2 =? 1) eqn:E21; [apply Nat.eqb_eq in E21; lia|].
  destruct (2 =? 2) eqn:E22; [|rewrite Nat.eqb_refl in E22; discriminate].
  destruct (3 =? 2) eqn:E32; [apply Nat.eqb_eq in E32; lia|].
  destruct (4 =? 2) eqn:E42; [apply Nat.eqb_eq in E42; lia|].
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_boundary_4simplex_at_3 : forall μ,
  matching_neighbors_except_self boundary_4simplex μ 3%nat = [0%nat; 1%nat; 2%nat; 4%nat].
Proof.
  intro μ.
  unfold matching_neighbors_except_self, boundary_4simplex.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (0 =? 3) eqn:E03; [apply Nat.eqb_eq in E03; lia|].
  destruct (3 =? 0) eqn:E30; [apply Nat.eqb_eq in E30; lia|].
  destruct (1 =? 3) eqn:E13; [apply Nat.eqb_eq in E13; lia|].
  destruct (3 =? 1) eqn:E31; [apply Nat.eqb_eq in E31; lia|].
  destruct (2 =? 3) eqn:E23; [apply Nat.eqb_eq in E23; lia|].
  destruct (3 =? 2) eqn:E32; [apply Nat.eqb_eq in E32; lia|].
  destruct (3 =? 3) eqn:E33; [|rewrite Nat.eqb_refl in E33; discriminate].
  destruct (4 =? 3) eqn:E43; [apply Nat.eqb_eq in E43; lia|].
  simpl. reflexivity.
Qed.

Lemma matching_neighbors_boundary_4simplex_at_4 : forall μ,
  matching_neighbors_except_self boundary_4simplex μ 4%nat = [0%nat; 1%nat; 2%nat; 3%nat].
Proof.
  intro μ.
  unfold matching_neighbors_except_self, boundary_4simplex.
  cbn [sc4d_vertices sc4d_edges e1d_direction e1d_vertices].
  unfold existsb, nat_list_mem. simpl.
  destruct (0 =? 4) eqn:E04; [apply Nat.eqb_eq in E04; lia|].
  destruct (4 =? 0) eqn:E40; [apply Nat.eqb_eq in E40; lia|].
  destruct (1 =? 4) eqn:E14; [apply Nat.eqb_eq in E14; lia|].
  destruct (4 =? 1) eqn:E41; [apply Nat.eqb_eq in E41; lia|].
  destruct (2 =? 4) eqn:E24; [apply Nat.eqb_eq in E24; lia|].
  destruct (4 =? 2) eqn:E42; [apply Nat.eqb_eq in E42; lia|].
  destruct (3 =? 4) eqn:E34; [apply Nat.eqb_eq in E34; lia|].
  destruct (4 =? 3) eqn:E43; [apply Nat.eqb_eq in E43; lia|].
  destruct (4 =? 4) eqn:E44; [|rewrite Nat.eqb_refl in E44; discriminate].
  simpl. reflexivity.
Qed.

Lemma symmetric_dd_boundary_4simplex_at_0 : forall s f μ,
  symmetric_discrete_derivative s boundary_4simplex f μ 0%nat =
  (((f 1%nat - f 0%nat) + (f 2%nat - f 0%nat) +
    (f 3%nat - f 0%nat) + (f 4%nat - f 0%nat)) / 4)%R.
Proof.
  intros s f μ.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_boundary_4simplex_at_0.
  simpl.
  field.
Qed.

Lemma symmetric_dd_boundary_4simplex_at_2 : forall s f μ,
  symmetric_discrete_derivative s boundary_4simplex f μ 2%nat =
  (((f 0%nat - f 2%nat) + (f 1%nat - f 2%nat) +
    (f 3%nat - f 2%nat) + (f 4%nat - f 2%nat)) / 4)%R.
Proof.
  intros s f μ.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_boundary_4simplex_at_2.
  simpl.
  field.
Qed.

Lemma symmetric_dd_boundary_4simplex_at_3 : forall s f μ,
  symmetric_discrete_derivative s boundary_4simplex f μ 3%nat =
  (((f 0%nat - f 3%nat) + (f 1%nat - f 3%nat) +
    (f 2%nat - f 3%nat) + (f 4%nat - f 3%nat)) / 4)%R.
Proof.
  intros s f μ.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_boundary_4simplex_at_3.
  simpl.
  field.
Qed.

Lemma symmetric_dd_boundary_4simplex_at_4 : forall s f μ,
  symmetric_discrete_derivative s boundary_4simplex f μ 4%nat =
  (((f 0%nat - f 4%nat) + (f 1%nat - f 4%nat) +
    (f 2%nat - f 4%nat) + (f 3%nat - f 4%nat)) / 4)%R.
Proof.
  intros s f μ.
  unfold symmetric_discrete_derivative.
  rewrite matching_neighbors_boundary_4simplex_at_4.
  simpl.
  field.
Qed.

Definition symmetric_combinatorially_orthogonal
  (sc : SimplicialComplex4D) (s : VMState) (v : ModuleID) : Prop :=
  forall mu nu : nat,
    (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
    symmetric_curved_ricci s sc mu nu v = 0%R.

Theorem symmetric_boundary_4simplex_curved_ricci_01_nonuniform_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    symmetric_curved_ricci s boundary_4simplex 0%nat 1%nat 1%nat = (-5 / 8)%R.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4.
  set (c1 := (-1 / 4)%R).
  set (co := (1 / 8)%R).
  set (d := (3 / 8)%R).
  assert (HGamma1 : forall rho mu nu,
    (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu nu 1%nat =
      gamma_iso c1 rho mu nu).
  {
    intros rho mu nu Hrho Hmu Hnu.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu nu 1%nat =
      symmetric_curved_christoffel s (two_vertex_sc 1%nat 0%nat) rho mu nu 1%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_1.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 1%nat 0%nat 2%R 1%R rho mu nu ltac:(lia) ltac:(lra) Hiso1 Hiso0 Hrho Hmu Hnu).
    unfold c1, gamma_iso, delta.
    field.
  }
  assert (HGamma0 : forall rho mu nu,
    (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu nu 0%nat =
      gamma_iso co rho mu nu).
  {
    intros rho mu nu Hrho Hmu Hnu.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu nu 0%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 0%nat 1%nat) rho mu nu 0%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_0.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 0%nat 1%nat 1%R 2%R rho mu nu ltac:(lia) ltac:(lra) Hiso0 Hiso1 Hrho Hmu Hnu).
    unfold co, gamma_iso, delta.
    field.
  }
  assert (HGamma2 : forall rho mu nu,
    (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu nu 2%nat =
      gamma_iso co rho mu nu).
  {
    intros rho mu nu Hrho Hmu Hnu.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu nu 2%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 2%nat 1%nat) rho mu nu 2%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_2.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 2%nat 1%nat 1%R 2%R rho mu nu ltac:(lia) ltac:(lra) Hiso2 Hiso1 Hrho Hmu Hnu).
    unfold co, gamma_iso, delta.
    field.
  }
  assert (HGamma3 : forall rho mu nu,
    (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu nu 3%nat =
      gamma_iso co rho mu nu).
  {
    intros rho mu nu Hrho Hmu Hnu.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu nu 3%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 3%nat 1%nat) rho mu nu 3%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_3.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 3%nat 1%nat 1%R 2%R rho mu nu ltac:(lia) ltac:(lra) Hiso3 Hiso1 Hrho Hmu Hnu).
    unfold co, gamma_iso, delta.
    field.
  }
  assert (HGamma4 : forall rho mu nu,
    (rho < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu nu 4%nat =
      gamma_iso co rho mu nu).
  {
    intros rho mu nu Hrho Hmu Hnu.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu nu 4%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 4%nat 1%nat) rho mu nu 4%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_4.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 4%nat 1%nat 1%R 2%R rho mu nu ltac:(lia) ltac:(lra) Hiso4 Hiso1 Hrho Hmu Hnu).
    unfold co, gamma_iso, delta.
    field.
  }
  assert (HRiem : forall rho sigma mu nu,
    (rho < 4)%nat -> (sigma < 4)%nat -> (mu < 4)%nat -> (nu < 4)%nat ->
    symmetric_curved_riemann s boundary_4simplex rho sigma mu nu 1%nat =
      ((gamma_iso d rho nu sigma - gamma_iso d rho mu sigma) +
       sum_4 (fun lambda =>
         (gamma_iso c1 rho mu lambda * gamma_iso c1 lambda nu sigma)%R) -
       sum_4 (fun lambda =>
         (gamma_iso c1 rho nu lambda * gamma_iso c1 lambda mu sigma)%R))%R).
  {
    intros rho sigma mu nu Hrho Hsigma Hmu Hnu.
    unfold symmetric_curved_riemann.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite (HGamma0 rho nu sigma Hrho Hnu Hsigma).
    rewrite (HGamma2 rho nu sigma Hrho Hnu Hsigma).
    rewrite (HGamma3 rho nu sigma Hrho Hnu Hsigma).
    rewrite (HGamma4 rho nu sigma Hrho Hnu Hsigma).
    rewrite (HGamma1 rho nu sigma Hrho Hnu Hsigma).
    rewrite (HGamma0 rho mu sigma Hrho Hmu Hsigma).
    rewrite (HGamma2 rho mu sigma Hrho Hmu Hsigma).
    rewrite (HGamma3 rho mu sigma Hrho Hmu Hsigma).
    rewrite (HGamma4 rho mu sigma Hrho Hmu Hsigma).
    rewrite (HGamma1 rho mu sigma Hrho Hmu Hsigma).
    unfold sum_4, sum_n.
    rewrite (HGamma1 rho mu 0%nat Hrho Hmu ltac:(lia)),
            (HGamma1 0%nat nu sigma ltac:(lia) Hnu Hsigma),
            (HGamma1 rho mu 1%nat Hrho Hmu ltac:(lia)),
            (HGamma1 1%nat nu sigma ltac:(lia) Hnu Hsigma),
            (HGamma1 rho mu 2%nat Hrho Hmu ltac:(lia)),
            (HGamma1 2%nat nu sigma ltac:(lia) Hnu Hsigma),
            (HGamma1 rho mu 3%nat Hrho Hmu ltac:(lia)),
            (HGamma1 3%nat nu sigma ltac:(lia) Hnu Hsigma).
    rewrite (HGamma1 rho nu 0%nat Hrho Hnu ltac:(lia)),
            (HGamma1 0%nat mu sigma ltac:(lia) Hmu Hsigma),
            (HGamma1 rho nu 1%nat Hrho Hnu ltac:(lia)),
            (HGamma1 1%nat mu sigma ltac:(lia) Hmu Hsigma),
            (HGamma1 rho nu 2%nat Hrho Hnu ltac:(lia)),
            (HGamma1 2%nat mu sigma ltac:(lia) Hmu Hsigma),
            (HGamma1 rho nu 3%nat Hrho Hnu ltac:(lia)),
            (HGamma1 3%nat mu sigma ltac:(lia) Hmu Hsigma).
    unfold c1, d, gamma_iso, delta.
    destruct rho as [|[|[|[|rho]]]]; try lia;
    destruct sigma as [|[|[|[|sigma]]]]; try lia;
    destruct mu as [|[|[|[|mu]]]]; try lia;
    destruct nu as [|[|[|[|nu]]]]; try lia;
    simpl;
    vm_compute;
    lra.
  }
  unfold symmetric_curved_ricci, sum_4, sum_n.
  rewrite (HRiem 0%nat 0%nat 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (HRiem 1%nat 0%nat 1%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (HRiem 2%nat 0%nat 2%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (HRiem 3%nat 0%nat 3%nat 1%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  unfold c1, d, gamma_iso, delta.
  vm_compute.
  lra.
Qed.

Corollary symmetric_boundary_4simplex_nonuniform_diagonal_refuted_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    ~ symmetric_combinatorially_orthogonal boundary_4simplex s 1%nat.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 Horth.
  specialize (Horth 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (symmetric_boundary_4simplex_curved_ricci_01_nonuniform_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4) in Horth.
  lra.
Qed.

Lemma boundary_shell_gamma_ricci_01_formula :
  forall c1 co,
    sum_4 (fun rho =>
      ((gamma_iso (co - c1) rho 1%nat 0%nat -
        gamma_iso (co - c1) rho rho 0%nat) +
       sum_4 (fun lambda =>
         (gamma_iso c1 rho rho lambda * gamma_iso c1 lambda 1%nat 0%nat)%R) -
       sum_4 (fun lambda =>
         (gamma_iso c1 rho 1%nat lambda * gamma_iso c1 lambda rho 0%nat)%R))%R) =
    (2 * (c1 * c1 + c1 - co))%R.
Proof.
  intros c1 co.
  cbv [sum_4 sum_n gamma_iso delta].
  vm_compute.
  ring.
Qed.

Corollary boundary_shell_weight_family_ricci_01 :
  forall alpha,
    sum_4 (fun rho =>
      ((gamma_iso ((alpha / 2) - (-1 / 4)) rho 1%nat 0%nat -
        gamma_iso ((alpha / 2) - (-1 / 4)) rho rho 0%nat) +
       sum_4 (fun lambda =>
         (gamma_iso (-1 / 4) rho rho lambda * gamma_iso (-1 / 4) lambda 1%nat 0%nat)%R) -
       sum_4 (fun lambda =>
         (gamma_iso (-1 / 4) rho 1%nat lambda * gamma_iso (-1 / 4) lambda rho 0%nat)%R))%R) =
    ((-3 / 8) - alpha)%R.
Proof.
  intro alpha.
  rewrite boundary_shell_gamma_ricci_01_formula.
  field.
Qed.

Corollary boundary_shell_weight_family_refuted :
  forall alpha,
    (0 <= alpha)%R ->
    sum_4 (fun rho =>
      ((gamma_iso ((alpha / 2) - (-1 / 4)) rho 1%nat 0%nat -
        gamma_iso ((alpha / 2) - (-1 / 4)) rho rho 0%nat) +
       sum_4 (fun lambda =>
         (gamma_iso (-1 / 4) rho rho lambda * gamma_iso (-1 / 4) lambda 1%nat 0%nat)%R) -
       sum_4 (fun lambda =>
         (gamma_iso (-1 / 4) rho 1%nat lambda * gamma_iso (-1 / 4) lambda rho 0%nat)%R))%R) <> 0%R.
Proof.
  intros alpha Halpha.
  rewrite boundary_shell_weight_family_ricci_01.
  lra.
Qed.

Definition affine_metric_symmetric_factor (s : VMState) (v : ModuleID) : R :=
  (8 - 5 * full_metric_at_vertex s v 0%nat 0%nat)%R.

Definition affine_metric_symmetric_discrete_derivative
  (s : VMState) (sc : SimplicialComplex4D)
  (f : ModuleID -> R) (μ v : ModuleID) : R :=
  (affine_metric_symmetric_factor s v *
   symmetric_discrete_derivative s sc f μ v)%R.

Definition affine_metric_symmetric_metric_derivative_halfsum
  (s : VMState) (sc : SimplicialComplex4D)
  (σ μ ν : nat) (v : ModuleID) : R :=
  (affine_metric_symmetric_discrete_derivative s sc
      (fun w => full_metric_at_vertex s w ν σ) μ v +
   affine_metric_symmetric_discrete_derivative s sc
      (fun w => full_metric_at_vertex s w μ σ) ν v -
   affine_metric_symmetric_discrete_derivative s sc
      (fun w => full_metric_at_vertex s w μ ν) σ v) / 2.

Definition affine_metric_symmetric_curved_christoffel
  (s : VMState) (sc : SimplicialComplex4D)
  (ρ μ ν : nat) (v : ModuleID) : R :=
  let g_inv := inverse_metric_at_vertex s v in
  sum_4 (fun σ =>
    g_inv ρ σ * affine_metric_symmetric_metric_derivative_halfsum s sc σ μ ν v).

Definition affine_metric_symmetric_curved_riemann
  (s : VMState) (sc : SimplicialComplex4D)
  (ρ σ μ ν : nat) (v : ModuleID) : R :=
  affine_metric_symmetric_discrete_derivative s sc
    (fun w => affine_metric_symmetric_curved_christoffel s sc ρ ν σ w) μ v -
  affine_metric_symmetric_discrete_derivative s sc
    (fun w => affine_metric_symmetric_curved_christoffel s sc ρ μ σ w) ν v +
  sum_4 (fun λ =>
    affine_metric_symmetric_curved_christoffel s sc ρ μ λ v *
    affine_metric_symmetric_curved_christoffel s sc λ ν σ v) -
  sum_4 (fun λ =>
    affine_metric_symmetric_curved_christoffel s sc ρ ν λ v *
    affine_metric_symmetric_curved_christoffel s sc λ μ σ v).

Definition affine_metric_symmetric_curved_ricci
  (s : VMState) (sc : SimplicialComplex4D)
  (μ ν : nat) (v : ModuleID) : R :=
  sum_4 (fun ρ => affine_metric_symmetric_curved_riemann s sc ρ μ ρ ν v).

Definition affine_metric_symmetric_curved_ricci_scalar
  (s : VMState) (sc : SimplicialComplex4D)
  (v : ModuleID) : R :=
  let g_inv := inverse_metric_at_vertex s v in
  sum_4 (fun μ => sum_4 (fun ν => g_inv μ ν * affine_metric_symmetric_curved_ricci s sc μ ν v)).

Definition affine_metric_symmetric_curved_einstein
  (s : VMState) (sc : SimplicialComplex4D)
  (μ ν : nat) (v : ModuleID) : R :=
  affine_metric_symmetric_curved_ricci s sc μ ν v -
  (1 / 2) * full_metric_at_vertex s v μ ν * affine_metric_symmetric_curved_ricci_scalar s sc v.

Definition affine_metric_symmetric_combinatorially_orthogonal
  (sc : SimplicialComplex4D) (s : VMState) (v : ModuleID) : Prop :=
  forall mu nu : nat,
    (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
    affine_metric_symmetric_curved_ricci s sc mu nu v = 0%R.

Lemma affine_metric_symmetric_metric_derivative_halfsum_eq_factor :
  forall s sc σ μ ν v,
    affine_metric_symmetric_metric_derivative_halfsum s sc σ μ ν v =
    (affine_metric_symmetric_factor s v *
     symmetric_metric_derivative_halfsum s sc σ μ ν v)%R.
Proof.
  intros s sc σ μ ν v.
  unfold affine_metric_symmetric_metric_derivative_halfsum,
         affine_metric_symmetric_discrete_derivative,
         symmetric_metric_derivative_halfsum,
         affine_metric_symmetric_factor.
  field.
Qed.

Lemma affine_metric_symmetric_curved_christoffel_eq_factor :
  forall s sc ρ μ ν v,
    affine_metric_symmetric_curved_christoffel s sc ρ μ ν v =
    (affine_metric_symmetric_factor s v *
     symmetric_curved_christoffel s sc ρ μ ν v)%R.
Proof.
  intros s sc ρ μ ν v.
  unfold affine_metric_symmetric_curved_christoffel,
         symmetric_curved_christoffel.
  unfold sum_4, sum_n.
  repeat rewrite affine_metric_symmetric_metric_derivative_halfsum_eq_factor.
  unfold affine_metric_symmetric_factor.
  ring.
Qed.

Lemma boundary_shell_gamma_ricci_offdiag_scaled_formula :
  forall c1 co k mu nu,
    (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
    sum_4 (fun rho =>
      ((gamma_iso (k * (co - c1)) rho nu mu -
        gamma_iso (k * (co - c1)) rho rho mu) +
       sum_4 (fun lambda =>
         (gamma_iso c1 rho rho lambda * gamma_iso c1 lambda nu mu)%R) -
       sum_4 (fun lambda =>
         (gamma_iso c1 rho nu lambda * gamma_iso c1 lambda rho mu)%R))%R) =
    (2 * (c1 * c1 + k * c1 - k * co))%R.
Proof.
  intros c1 co k mu nu Hmu Hnu Hneq.
  destruct mu as [|[|[|[|mu]]]]; try lia;
  destruct nu as [|[|[|[|nu]]]]; try lia;
  try contradiction;
  cbv [sum_4 sum_n gamma_iso delta];
  vm_compute;
  ring.
Qed.

Lemma boundary_shell_gamma_ricci_diag_scaled_formula :
  forall c1 co k mu,
    (mu < 4)%nat ->
    sum_4 (fun rho =>
      ((gamma_iso (k * (co - c1)) rho mu mu -
        gamma_iso (k * (co - c1)) rho rho mu) +
       sum_4 (fun lambda =>
         (gamma_iso c1 rho rho lambda * gamma_iso c1 lambda mu mu)%R) -
       sum_4 (fun lambda =>
         (gamma_iso c1 rho mu lambda * gamma_iso c1 lambda rho mu)%R))%R) =
    (-6 * (c1 * c1 - k * c1 + k * co))%R.
Proof.
  intros c1 co k mu Hmu.
  destruct mu as [|[|[|[|mu]]]]; try lia;
  cbv [sum_4 sum_n gamma_iso delta];
  vm_compute;
  ring.
Qed.

Theorem affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    forall mu nu,
      (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
      affine_metric_symmetric_curved_ricci s boundary_4simplex mu nu 1%nat = 0%R.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 mu nu Hmu Hnu Hneq.
  assert (HSGamma1 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      gamma_iso (-1 / 4) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      symmetric_curved_christoffel s (two_vertex_sc 1%nat 0%nat) rho mu0 nu0 1%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_1.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 1%nat 0%nat 2%R 1%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso1 Hiso0 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma0 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 0%nat 1%nat) rho mu0 nu0 0%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_0.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 0%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso0 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma2 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 2%nat 1%nat) rho mu0 nu0 2%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_2.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 2%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso2 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma3 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 3%nat 1%nat) rho mu0 nu0 3%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_3.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 3%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso3 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma4 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 4%nat 1%nat) rho mu0 nu0 4%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_4.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 4%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso4 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (Hfactor1 : affine_metric_symmetric_factor s 1%nat = (-2)%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso1 by lia.
    simpl.
    ring.
  }
  assert (Hfactor0 : affine_metric_symmetric_factor s 0%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso0 by lia.
    simpl.
    ring.
  }
  assert (Hfactor2 : affine_metric_symmetric_factor s 2%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso2 by lia.
    simpl.
    ring.
  }
  assert (Hfactor3 : affine_metric_symmetric_factor s 3%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso3 by lia.
    simpl.
    ring.
  }
  assert (Hfactor4 : affine_metric_symmetric_factor s 4%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso4 by lia.
    simpl.
    ring.
  }
  assert (HAGamma1 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      gamma_iso (1 / 2) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor1.
    rewrite HSGamma1 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma0 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor0.
    rewrite HSGamma0 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma2 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor2.
    rewrite HSGamma2 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma3 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor3.
    rewrite HSGamma3 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma4 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor4.
    rewrite HSGamma4 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HRiem : forall rho sigma mu0 nu0,
    (rho < 4)%nat -> (sigma < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_riemann s boundary_4simplex rho sigma mu0 nu0 1%nat =
      ((gamma_iso (1 / 4) rho nu0 sigma - gamma_iso (1 / 4) rho mu0 sigma) +
       sum_4 (fun lambda =>
         (gamma_iso (1 / 2) rho mu0 lambda * gamma_iso (1 / 2) lambda nu0 sigma)%R) -
       sum_4 (fun lambda =>
         (gamma_iso (1 / 2) rho nu0 lambda * gamma_iso (1 / 2) lambda mu0 sigma)%R))%R).
  {
    intros rho sigma mu0 nu0 Hrho Hsigma Hmu0 Hnu0.
    unfold affine_metric_symmetric_curved_riemann,
           affine_metric_symmetric_discrete_derivative.
    rewrite Hfactor1.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite (HAGamma0 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma2 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma3 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma4 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma1 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma0 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma2 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma3 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma4 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma1 rho mu0 sigma Hrho Hmu0 Hsigma).
    unfold sum_4, sum_n.
    rewrite (HAGamma1 rho mu0 0%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 0%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 1%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 1%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 2%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 2%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 3%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 3%nat nu0 sigma ltac:(lia) Hnu0 Hsigma).
    rewrite (HAGamma1 rho nu0 0%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 0%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 1%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 1%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 2%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 2%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 3%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 3%nat mu0 sigma ltac:(lia) Hmu0 Hsigma).
    unfold gamma_iso, delta.
    field.
  }
  destruct mu as [|[|[|[|mu]]]]; try lia;
  destruct nu as [|[|[|[|nu]]]]; try lia;
  try contradiction;
    unfold affine_metric_symmetric_curved_ricci, sum_4, sum_n;
    repeat match goal with
    | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 0 ?m 0 ?n 1%nat] =>
      rewrite (HRiem 0%nat m 0%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 1 ?m 1 ?n 1%nat] =>
      rewrite (HRiem 1%nat m 1%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 2 ?m 2 ?n 1%nat] =>
      rewrite (HRiem 2%nat m 2%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 3 ?m 3 ?n 1%nat] =>
      rewrite (HRiem 3%nat m 3%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    end;
  unfold gamma_iso, delta;
    vm_compute;
  field.
Qed.

Corollary affine_metric_symmetric_boundary_4simplex_nonuniform_diagonal_orthogonal_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    affine_metric_symmetric_combinatorially_orthogonal boundary_4simplex s 1%nat.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4.
  unfold affine_metric_symmetric_combinatorially_orthogonal.
  intros mu nu Hmu Hnu Hneq.
  apply (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 mu nu Hmu Hnu Hneq).
Qed.

Theorem affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    forall mu,
      (mu < 4)%nat ->
      affine_metric_symmetric_curved_ricci s boundary_4simplex mu mu 1%nat = (-3)%R.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 mu Hmu.
  assert (HSGamma1 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      gamma_iso (-1 / 4) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      symmetric_curved_christoffel s (two_vertex_sc 1%nat 0%nat) rho mu0 nu0 1%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_1.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 1%nat 0%nat 2%R 1%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso1 Hiso0 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma0 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 0%nat 1%nat) rho mu0 nu0 0%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_0.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 0%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso0 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma2 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 2%nat 1%nat) rho mu0 nu0 2%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_2.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 2%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso2 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma3 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 3%nat 1%nat) rho mu0 nu0 3%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_3.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 3%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso3 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (HSGamma4 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      gamma_iso (1 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    assert (Htransport :
      symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      (1 / 4) * symmetric_curved_christoffel s (two_vertex_sc 4%nat 1%nat) rho mu0 nu0 4%nat).
    {
      unfold symmetric_curved_christoffel, symmetric_metric_derivative_halfsum.
      unfold sum_4, sum_n.
      repeat rewrite symmetric_dd_boundary_4simplex_at_4.
      repeat rewrite symmetric_dd_two_vertex_at_v by lia.
      repeat rewrite Hiso1 by lia.
      repeat rewrite Hiso0 by lia.
      repeat rewrite Hiso2 by lia.
      repeat rewrite Hiso3 by lia.
      repeat rewrite Hiso4 by lia.
      field.
    }
    rewrite Htransport.
    rewrite (symmetric_curved_christoffel_isotropic_2v s 4%nat 1%nat 1%R 2%R rho mu0 nu0 ltac:(lia) ltac:(lra) Hiso4 Hiso1 Hrho Hmu0 Hnu0).
    unfold gamma_iso, delta.
    field.
  }
  assert (Hfactor1 : affine_metric_symmetric_factor s 1%nat = (-2)%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso1 by lia.
    simpl.
    ring.
  }
  assert (Hfactor0 : affine_metric_symmetric_factor s 0%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso0 by lia.
    simpl.
    ring.
  }
  assert (Hfactor2 : affine_metric_symmetric_factor s 2%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso2 by lia.
    simpl.
    ring.
  }
  assert (Hfactor3 : affine_metric_symmetric_factor s 3%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso3 by lia.
    simpl.
    ring.
  }
  assert (Hfactor4 : affine_metric_symmetric_factor s 4%nat = 3%R).
  {
    unfold affine_metric_symmetric_factor.
    rewrite Hiso4 by lia.
    simpl.
    ring.
  }
  assert (HAGamma1 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 1%nat =
      gamma_iso (1 / 2) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor1.
    rewrite HSGamma1 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma0 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 0%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor0.
    rewrite HSGamma0 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma2 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 2%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor2.
    rewrite HSGamma2 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma3 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 3%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor3.
    rewrite HSGamma3 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HAGamma4 : forall rho mu0 nu0,
    (rho < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_christoffel s boundary_4simplex rho mu0 nu0 4%nat =
      gamma_iso (3 / 8) rho mu0 nu0).
  {
    intros rho mu0 nu0 Hrho Hmu0 Hnu0.
    rewrite affine_metric_symmetric_curved_christoffel_eq_factor.
    rewrite Hfactor4.
    rewrite HSGamma4 by assumption.
    unfold gamma_iso, delta.
    field.
  }
  assert (HRiem : forall rho sigma mu0 nu0,
    (rho < 4)%nat -> (sigma < 4)%nat -> (mu0 < 4)%nat -> (nu0 < 4)%nat ->
    affine_metric_symmetric_curved_riemann s boundary_4simplex rho sigma mu0 nu0 1%nat =
      ((gamma_iso (1 / 4) rho nu0 sigma - gamma_iso (1 / 4) rho mu0 sigma) +
       sum_4 (fun lambda =>
         (gamma_iso (1 / 2) rho mu0 lambda * gamma_iso (1 / 2) lambda nu0 sigma)%R) -
       sum_4 (fun lambda =>
         (gamma_iso (1 / 2) rho nu0 lambda * gamma_iso (1 / 2) lambda mu0 sigma)%R))%R).
  {
    intros rho sigma mu0 nu0 Hrho Hsigma Hmu0 Hnu0.
    unfold affine_metric_symmetric_curved_riemann,
           affine_metric_symmetric_discrete_derivative.
    rewrite Hfactor1.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite symmetric_dd_boundary_4simplex_at_1.
    rewrite (HAGamma0 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma2 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma3 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma4 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma1 rho nu0 sigma Hrho Hnu0 Hsigma).
    rewrite (HAGamma0 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma2 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma3 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma4 rho mu0 sigma Hrho Hmu0 Hsigma).
    rewrite (HAGamma1 rho mu0 sigma Hrho Hmu0 Hsigma).
    unfold sum_4, sum_n.
    rewrite (HAGamma1 rho mu0 0%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 0%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 1%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 1%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 2%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 2%nat nu0 sigma ltac:(lia) Hnu0 Hsigma),
            (HAGamma1 rho mu0 3%nat Hrho Hmu0 ltac:(lia)),
            (HAGamma1 3%nat nu0 sigma ltac:(lia) Hnu0 Hsigma).
    rewrite (HAGamma1 rho nu0 0%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 0%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 1%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 1%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 2%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 2%nat mu0 sigma ltac:(lia) Hmu0 Hsigma),
            (HAGamma1 rho nu0 3%nat Hrho Hnu0 ltac:(lia)),
            (HAGamma1 3%nat mu0 sigma ltac:(lia) Hmu0 Hsigma).
    unfold gamma_iso, delta.
    field.
  }
  destruct mu as [|[|[|[|mu]]]]; try lia;
  unfold affine_metric_symmetric_curved_ricci, sum_4, sum_n;
  repeat match goal with
  | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 0 ?m 0 ?n 1%nat] =>
      rewrite (HRiem 0%nat m 0%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 1 ?m 1 ?n 1%nat] =>
      rewrite (HRiem 1%nat m 1%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 2 ?m 2 ?n 1%nat] =>
      rewrite (HRiem 2%nat m 2%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | |- context [affine_metric_symmetric_curved_riemann s boundary_4simplex 3 ?m 3 ?n 1%nat] =>
      rewrite (HRiem 3%nat m 3%nat n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  end;
  unfold gamma_iso, delta;
  vm_compute;
  field.
Qed.

Theorem affine_metric_symmetric_boundary_4simplex_curved_ricci_scalar_at_1 :
  forall s,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    affine_metric_symmetric_curved_ricci_scalar s boundary_4simplex 1%nat = (-6)%R.
Proof.
  intros s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4.
  assert (Hginv : forall i j, (i < 4)%nat -> (j < 4)%nat ->
    inverse_metric_at_vertex s 1%nat i j = if (i =? j)%nat then / 2%R else 0%R).
  {
    apply inverse_metric_isotropic.
    - lra.
    - exact Hiso1.
  }
  unfold affine_metric_symmetric_curved_ricci_scalar, sum_4, sum_n.
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 0%nat ltac:(lia)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 1%nat ltac:(lia)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 2%nat ltac:(lia)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 3%nat ltac:(lia)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 0%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 0%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 0%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 1%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 1%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 1%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 2%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 2%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 2%nat 3%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 3%nat 0%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 3%nat 1%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 3%nat 2%nat ltac:(lia) ltac:(lia) ltac:(discriminate)).
  rewrite (Hginv 0%nat 0%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 0%nat 1%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 0%nat 2%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 0%nat 3%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 1%nat 0%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 1%nat 1%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 1%nat 2%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 1%nat 3%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 2%nat 0%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 2%nat 1%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 2%nat 2%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 2%nat 3%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 3%nat 0%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 3%nat 1%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 3%nat 2%nat ltac:(lia) ltac:(lia)).
  rewrite (Hginv 3%nat 3%nat ltac:(lia) ltac:(lia)).
  simpl Nat.eqb.
  lra.
Qed.

Theorem affine_metric_symmetric_boundary_4simplex_curved_einstein_at_1 :
  forall s mu nu,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (mu < 4)%nat -> (nu < 4)%nat ->
    affine_metric_symmetric_curved_einstein s boundary_4simplex mu nu 1%nat =
      (if (mu =? nu)%nat then 3%R else 0%R).
Proof.
  intros s mu nu Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 Hmu Hnu.
  unfold affine_metric_symmetric_curved_einstein.
  destruct (Nat.eq_dec mu nu) as [Heq | Hneq].
  - subst nu.
    rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_diag_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 mu Hmu).
    rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_scalar_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4).
    rewrite Hiso1 by lia.
    rewrite Nat.eqb_refl.
    field.
  - rewrite (affine_metric_symmetric_boundary_4simplex_curved_ricci_offdiag_zero_at_1 s Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 mu nu Hmu Hnu Hneq).
    rewrite Hiso1 by lia.
    apply Nat.eqb_neq in Hneq.
    rewrite Hneq.
    field.
Qed.

Theorem affine_metric_symmetric_boundary_4simplex_full_tensor_efe_at_1 :
  forall s mu nu,
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 1%nat i j = if (i =? j)%nat then 2%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 0%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 2%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 3%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s 4%nat i j = if (i =? j)%nat then 1%R else 0%R) ->
    module_structural_mass s 1%nat = 1%nat ->
    (mu < 4)%nat -> (nu < 4)%nat ->
    affine_metric_symmetric_curved_einstein s boundary_4simplex mu nu 1%nat =
      (3 * mass_stress_energy s mu nu 1%nat)%R.
Proof.
  intros s mu nu Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 Hmass Hmu Hnu.
  rewrite (affine_metric_symmetric_boundary_4simplex_curved_einstein_at_1 s mu nu Hiso1 Hiso0 Hiso2 Hiso3 Hiso4 Hmu Hnu).
  unfold mass_stress_energy.
  rewrite !Nat.mod_small by lia.
  rewrite Hmass.
  destruct (mu =? nu)%nat eqn:Heq.
  - vm_compute. lra.
  - vm_compute. lra.
Qed.

