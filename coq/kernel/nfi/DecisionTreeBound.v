(** DecisionTreeBound: a binary decision tree has at most two to the depth
    leaves.

    A binary decision tree reads one yes/no distinction at each internal
    node and ends in a leaf, one leaf per outcome class it can tell apart.
    The tree has no machine in it. The facts here are the counting the
    structural-entitlement argument uses: a tree of depth [d] has at most
    [2^d] leaves, so telling [n] outcomes apart takes depth at least
    [log2_up n], and a complete tree of depth [d] reaches [2^d] leaves, so
    the bound is tight. *)

From Coq Require Import Arith.PeanoNat Lia.

Inductive DecisionTree : Type :=
| dt_leaf
| dt_branch (left_tree right_tree : DecisionTree).

Fixpoint decision_tree_depth (tree : DecisionTree) : nat :=
  match tree with
  | dt_leaf => 0
  | dt_branch left_tree right_tree =>
      S (Nat.max (decision_tree_depth left_tree) (decision_tree_depth right_tree))
  end.

Fixpoint decision_tree_leaf_count (tree : DecisionTree) : nat :=
  match tree with
  | dt_leaf => 1
  | dt_branch left_tree right_tree =>
      decision_tree_leaf_count left_tree + decision_tree_leaf_count right_tree
  end.

Lemma decision_tree_leaves_le_pow2_depth :
  forall tree,
    decision_tree_leaf_count tree <= 2 ^ decision_tree_depth tree.
Proof.
  induction tree as [|left IHleft right IHright]; simpl.
  - reflexivity.
  - set (depth_bound := Nat.max (decision_tree_depth left) (decision_tree_depth right)).
    eapply Nat.le_trans.
    + apply Nat.add_le_mono.
      * eapply Nat.le_trans.
        { exact IHleft. }
        apply Nat.pow_le_mono_r.
        { lia. }
        unfold depth_bound.
        apply Nat.le_max_l.
      * eapply Nat.le_trans.
        { exact IHright. }
        apply Nat.pow_le_mono_r.
        { lia. }
        unfold depth_bound.
        apply Nat.le_max_r.
    + unfold depth_bound.
      replace (2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right) +
               2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right))
        with (2 * 2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right)) by lia.
      rewrite <- Nat.pow_succ_r' by lia.
      reflexivity.
Qed.

Lemma decision_tree_log2_leaf_bound :
  forall tree,
    Nat.log2 (decision_tree_leaf_count tree) <= decision_tree_depth tree.
Proof.
  intro tree.
  eapply Nat.le_trans.
  - apply Nat.log2_le_mono.
    apply decision_tree_leaves_le_pow2_depth.
  - rewrite Nat.log2_pow2 by lia.
    reflexivity.
Qed.

Lemma decision_tree_leaf_count_positive :
  forall tree,
    decision_tree_leaf_count tree > 0.
Proof.
  induction tree; simpl; lia.
Qed.

Lemma decision_tree_log2_up_leaf_bound :
  forall tree,
    Nat.log2_up (decision_tree_leaf_count tree) <= decision_tree_depth tree.
Proof.
  intro tree.
  apply (proj1 (Nat.log2_up_le_pow2
    (decision_tree_leaf_count tree)
    (decision_tree_depth tree)
    (decision_tree_leaf_count_positive tree))).
  apply decision_tree_leaves_le_pow2_depth.
Qed.

(** A complete binary tree of depth [d] has [2^d] leaves, so the bound
    above is reached. *)
Fixpoint complete_tree (d : nat) : DecisionTree :=
  match d with
  | 0 => dt_leaf
  | S d' => dt_branch (complete_tree d') (complete_tree d')
  end.

Lemma complete_tree_leaf_count : forall d,
  decision_tree_leaf_count (complete_tree d) = 2 ^ d.
Proof.
  induction d as [|d IH]. reflexivity.
  simpl. rewrite IH. lia.
Qed.

Lemma complete_tree_depth : forall d,
  decision_tree_depth (complete_tree d) = d.
Proof.
  induction d as [|d IH]. reflexivity.
  simpl. rewrite IH, Nat.max_id. reflexivity.
Qed.
