(** F3_MuLaplacianSum: the sum-zero lemma for the discrete μ-Laplacian.

    The cumulative μ-Laplacian over the modules of a partition graph
    vanishes identically. This is a purely structural fact: it follows
    from the symmetry of [modules_adjacent_by_region] (the underlying
    [nat_list_disjoint] is symmetric) and the antisymmetry of
    [mu_gradient]. No calibration, no geometry, no topology.

    Proof shape. For each ordered pair (m, n) of module IDs, the
    contribution to [mu_laplacian s m] is [edge_weight s m n * (density n -
    density m)]; the contribution of the swapped pair (n, m) to
    [mu_laplacian s n] is [edge_weight s n m * (density m - density n)].
    [edge_weight] is symmetric, [mu_gradient] is antisymmetric, so the
    pair contributions cancel. Summing over all ordered pairs in a
    fixed list gives zero by Fubini swap.

    The lemma in this file is not specialized to any
    well-formedness of the partition graph: it holds for every VM state
    and every partition graph the kernel can construct.
*)

From Coq Require Import List Arith.PeanoNat Lia Reals Lra.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import MuGravity.

(** ** Symmetry of [nat_list_disjoint] and the induced adjacency. *)

Lemma nat_list_mem_existsb : forall x xs,
  nat_list_mem x xs = existsb (Nat.eqb x) xs.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl; auto.
  destruct (Nat.eqb x y); simpl; auto.
Qed.

Lemma nat_list_mem_In : forall x xs,
  nat_list_mem x xs = true <-> In x xs.
Proof.
  intros x xs. induction xs as [|y ys IH]; simpl.
  - split; [discriminate|intros []].
  - destruct (Nat.eqb_spec x y) as [Heq|Hneq]; simpl.
    + subst. split; [intros _; left; reflexivity|intros _; reflexivity].
    + rewrite IH. split.
      * intros H. right; assumption.
      * intros [Heq|Hin]; [exfalso; apply Hneq; symmetry; exact Heq|assumption].
Qed.

Lemma nat_list_disjoint_sym : forall xs ys,
  nat_list_disjoint xs ys = nat_list_disjoint ys xs.
Proof.
  intros xs ys.
  unfold nat_list_disjoint.
  destruct (forallb (fun x => negb (nat_list_mem x ys)) xs) eqn:H1;
  destruct (forallb (fun y => negb (nat_list_mem y xs)) ys) eqn:H2;
  try reflexivity.
  - (* H1 = true, H2 = false: contradiction. *)
    rewrite forallb_forall in H1.
    rewrite <- Bool.not_true_iff_false in H2.
    exfalso. apply H2.
    apply forallb_forall.
    intros y Hy.
    destruct (nat_list_mem y xs) eqn:Hyxs; [|reflexivity].
    apply nat_list_mem_In in Hyxs.
    specialize (H1 y Hyxs).
    apply Bool.negb_true_iff in H1.
    rewrite <- Bool.not_true_iff_false in H1.
    exfalso. apply H1. apply nat_list_mem_In. assumption.
  - (* H1 = false, H2 = true: contradiction. *)
    rewrite forallb_forall in H2.
    rewrite <- Bool.not_true_iff_false in H1.
    exfalso. apply H1.
    apply forallb_forall.
    intros x Hx.
    destruct (nat_list_mem x ys) eqn:Hxys; [|reflexivity].
    apply nat_list_mem_In in Hxys.
    specialize (H2 x Hxys).
    apply Bool.negb_true_iff in H2.
    rewrite <- Bool.not_true_iff_false in H2.
    exfalso. apply H2. apply nat_list_mem_In. assumption.
Qed.

Lemma modules_adjacent_by_region_sym : forall s m n,
  modules_adjacent_by_region s m n = modules_adjacent_by_region s n m.
Proof.
  intros s m n.
  unfold modules_adjacent_by_region.
  destruct (graph_lookup (vm_graph s) m) as [ms1|];
  destruct (graph_lookup (vm_graph s) n) as [ms2|]; try reflexivity.
  rewrite (nat_list_disjoint_sym (module_region ms1) (module_region ms2)).
  reflexivity.
Qed.

Lemma edge_weight_sym : forall s m n,
  edge_weight s m n = edge_weight s n m.
Proof.
  intros s m n. unfold edge_weight.
  rewrite (modules_adjacent_by_region_sym s m n). reflexivity.
Qed.

Lemma mu_gradient_antisym : forall s m n,
  mu_gradient s m n = (- mu_gradient s n m)%R.
Proof.
  intros s m n. unfold mu_gradient. lra.
Qed.

(** ** Pair contribution and its antisymmetry. *)

Definition pair_contribution (s : VMState) (m n : ModuleID) : R :=
  (edge_weight s m n * mu_gradient s m n)%R.

Lemma pair_contribution_swap : forall s m n,
  pair_contribution s m n = (- pair_contribution s n m)%R.
Proof.
  intros s m n.
  unfold pair_contribution.
  rewrite edge_weight_sym, mu_gradient_antisym. lra.
Qed.

Lemma pair_contribution_self : forall s m,
  pair_contribution s m m = 0%R.
Proof.
  intros s m.
  unfold pair_contribution, mu_gradient.
  replace (mu_cost_density s m - mu_cost_density s m)%R with 0%R by lra.
  lra.
Qed.

(** ** Inner sum over a list. *)

Definition sum_pair_inner (s : VMState) (m : ModuleID) (ns : list ModuleID) : R :=
  fold_right Rplus 0%R (map (pair_contribution s m) ns).

Lemma sum_pair_inner_nil : forall s m,
  sum_pair_inner s m [] = 0%R.
Proof. reflexivity. Qed.

Lemma sum_pair_inner_cons : forall s m n ns,
  sum_pair_inner s m (n :: ns) = (pair_contribution s m n + sum_pair_inner s m ns)%R.
Proof. reflexivity. Qed.

(** ** Filter-out lemma: contributions for non-neighbors are zero. *)

Lemma pair_contribution_zero_when_not_adjacent : forall s m n,
  modules_adjacent_by_region s m n = false ->
  pair_contribution s m n = 0%R.
Proof.
  intros s m n Hadj.
  unfold pair_contribution, edge_weight.
  rewrite Hadj. lra.
Qed.

Lemma pair_contribution_when_self : forall s m,
  pair_contribution s m m = 0%R.
Proof. apply pair_contribution_self. Qed.

(** Filter a module list keeping only n with: n ≠ m AND adjacent(m, n). *)
Lemma sum_pair_inner_filter_neighbors : forall s m ns,
  sum_pair_inner s m ns =
  sum_pair_inner s m
    (filter (fun n => andb (negb (m =? n)%nat) (modules_adjacent_by_region s m n)) ns).
Proof.
  intros s m ns. induction ns as [|n rest IH].
  - reflexivity.
  - simpl filter.
    destruct (Nat.eqb_spec m n) as [Heq|Hneq].
    + (* m = n case: kept out by the filter; pair_contribution s m n = 0. *)
      subst n. simpl andb.
      rewrite sum_pair_inner_cons.
      rewrite (pair_contribution_self s m).
      rewrite IH. lra.
    + simpl andb.
      destruct (modules_adjacent_by_region s m n) eqn:Hadj.
      * rewrite !sum_pair_inner_cons. rewrite IH. reflexivity.
      * rewrite sum_pair_inner_cons.
        rewrite (pair_contribution_zero_when_not_adjacent s m n Hadj).
        rewrite IH. lra.
Qed.

(** ** Convert mu_laplacian (fold_left form) to the fold_right form on neighbors. *)

Lemma fold_left_pair_contribution_to_fold_right :
  forall s m ns acc,
    fold_left (fun a n => (a + edge_weight s m n * mu_gradient s m n)%R) ns acc
    = (acc + fold_right Rplus 0%R (map (pair_contribution s m) ns))%R.
Proof.
  intros s m ns. induction ns as [|n rest IH]; intros acc; simpl.
  - lra.
  - rewrite IH. unfold pair_contribution. lra.
Qed.

Lemma mu_laplacian_as_sum_pair_inner : forall s m,
  mu_laplacian s m = sum_pair_inner s m (module_neighbors s m).
Proof.
  intros s m.
  unfold mu_laplacian, mu_laplacian_w, sum_pair_inner.
  rewrite fold_left_pair_contribution_to_fold_right.
  lra.
Qed.

(** mu_laplacian s m equals the sum over ALL module IDs of pair_contribution. *)
Lemma mu_laplacian_as_sum_pair_inner_all : forall s m,
  mu_laplacian s m = sum_pair_inner s m (map fst (pg_modules (vm_graph s))).
Proof.
  intros s m.
  rewrite mu_laplacian_as_sum_pair_inner.
  unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent.
  rewrite <- (sum_pair_inner_filter_neighbors s m
    (map fst (pg_modules (vm_graph s)))).
  reflexivity.
Qed.

(** ** Double-sum (Fubini-style). *)

Definition sum_pair_outer (s : VMState) (ms ns : list ModuleID) : R :=
  fold_right Rplus 0%R (map (fun m => sum_pair_inner s m ns) ms).

Lemma sum_pair_outer_nil_l : forall s ns,
  sum_pair_outer s [] ns = 0%R.
Proof. intros. reflexivity. Qed.

Lemma sum_pair_outer_cons_l : forall s m ms ns,
  sum_pair_outer s (m :: ms) ns =
  (sum_pair_inner s m ns + sum_pair_outer s ms ns)%R.
Proof. intros. reflexivity. Qed.

(** sum_pair_inner is left-distributive over a list-cons in the inner var. *)
Lemma sum_pair_inner_app : forall s m xs ys,
  sum_pair_inner s m (xs ++ ys) = (sum_pair_inner s m xs + sum_pair_inner s m ys)%R.
Proof.
  intros s m xs ys.
  unfold sum_pair_inner.
  rewrite map_app.
  rewrite fold_right_app.
  induction (map (pair_contribution s m) xs) as [|x rest IH]; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(** Helper: addition under fold_right is commutative-permutation-friendly. *)
Lemma fold_right_Rplus_app : forall xs ys,
  fold_right Rplus 0%R (xs ++ ys) =
  (fold_right Rplus 0%R xs + fold_right Rplus 0%R ys)%R.
Proof.
  intros xs ys.
  induction xs as [|x xs IH]; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(** Fubini swap: sum over ms of (sum over ns of f(m,n)) equals sum over
    ns of (sum over ms of f(m,n)). Standard for finite sums of reals. *)
Lemma sum_pair_outer_swap : forall s ms ns,
  sum_pair_outer s ms ns =
  fold_right Rplus 0%R
    (map (fun n => fold_right Rplus 0%R
                     (map (fun m => pair_contribution s m n) ms)) ns).
Proof.
  intros s ms ns. revert ms.
  induction ns as [|n rest IH]; intros ms; simpl.
  - (* ns = [] *)
    unfold sum_pair_outer, sum_pair_inner. simpl.
    induction ms as [|m ms' IHm]; simpl; auto.
    rewrite IHm. lra.
  - (* ns = n :: rest *)
    (* RHS = (sum over m of cont(m, n)) + (recursive RHS for rest). *)
    (* LHS = sum_pair_outer s ms (n :: rest) =
            sum over m in ms of [cont(m, n) + inner(m, rest)]. *)
    rewrite <- IH.
    unfold sum_pair_outer.
    induction ms as [|m ms' IHm]; simpl.
    + lra.
    + rewrite sum_pair_inner_cons.
      rewrite IHm. lra.
Qed.

(** The crucial swap: total over (ms, ms) of pair_contribution m n equals
    total over (ms, ms) of pair_contribution n m. *)
Lemma sum_pair_outer_self_swap : forall s ms,
  sum_pair_outer s ms ms =
  fold_right Rplus 0%R
    (map (fun m => fold_right Rplus 0%R
                     (map (fun n => pair_contribution s n m) ms)) ms).
Proof.
  intros s ms.
  rewrite sum_pair_outer_swap.
  reflexivity.
Qed.

(** Antisymmetry of pair_contribution lifted to inner sums. *)
Lemma sum_pair_inner_antisym_var : forall s m ns,
  fold_right Rplus 0%R (map (fun n => pair_contribution s n m) ns) =
  (- fold_right Rplus 0%R (map (fun n => pair_contribution s m n) ns))%R.
Proof.
  intros s m ns. induction ns as [|n rest IH]; simpl.
  - lra.
  - rewrite IH. rewrite (pair_contribution_swap s m n). lra.
Qed.

(** ** The main bookkeeping result: total over the same list is zero. *)

(** Generalized antisymmetry helper over distinct outer and full lists. *)
Lemma sum_pair_outer_swap_neg : forall s outer_list full,
  fold_right Rplus 0%R
    (map (fun m =>
            fold_right Rplus 0%R (map (fun n => pair_contribution s n m) full))
         outer_list)
  = (- fold_right Rplus 0%R
        (map (fun m =>
                fold_right Rplus 0%R (map (fun n => pair_contribution s m n) full))
             outer_list))%R.
Proof.
  intros s outer_list full.
  induction outer_list as [|m rest IH]; simpl.
  - lra.
  - rewrite IH.
    rewrite (sum_pair_inner_antisym_var s m full).
    lra.
Qed.

Theorem sum_pair_outer_self_zero : forall s ms,
  sum_pair_outer s ms ms = 0%R.
Proof.
  intros s ms.
  (* outer s ms ms equals the swap-form by Fubini. The swap-form equals
     minus the original outer (with cont(m,n)) by pair_contribution_swap.
     So outer = -outer = 0. *)
  pose proof (sum_pair_outer_self_swap s ms) as Hswap.
  pose proof (sum_pair_outer_swap_neg s ms ms) as Hanti.
  enough (Hself : sum_pair_outer s ms ms = (- sum_pair_outer s ms ms)%R) by lra.
  rewrite Hswap at 1.
  rewrite Hanti.
  unfold sum_pair_outer, sum_pair_inner.
  reflexivity.
Qed.

(** ** Cumulative μ-Laplacian is zero *)

Theorem total_mu_laplacian_zero : forall s,
  fold_right Rplus 0%R
    (map (mu_laplacian s) (map fst (pg_modules (vm_graph s)))) = 0%R.
Proof.
  intros s.
  set (ms := map fst (pg_modules (vm_graph s))).
  (* Rewrite each mu_laplacian as sum_pair_inner s m ms. *)
  assert (Heq : map (mu_laplacian s) ms = map (fun m => sum_pair_inner s m ms) ms).
  {
    unfold ms. apply map_ext.
    intros m. apply mu_laplacian_as_sum_pair_inner_all.
  }
  rewrite Heq.
  fold (sum_pair_outer s ms ms).
  apply sum_pair_outer_self_zero.
Qed.
