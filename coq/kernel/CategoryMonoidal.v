(** * CategoryMonoidal: Monoidal structure for the Thiele morphism category

    WHY THIS FILE EXISTS:
    The Thiele Machine's morphism category supports a tensor product (MORPH_TENSOR)
    that combines disjoint morphisms in parallel: (f : A→B) ⊗ (g : C→D) gives
    (f⊗g : A∪C → B∪D). This file proves that this tensor is bifunctorial —
    the categorical coherence property for symmetric monoidal categories.

    BIFUNCTORIALITY (the interchange law):
      (f⊗g) ; (f'⊗g') = (f;f') ⊗ (g;g')
    when cross-terms f;g' and g;f' are empty (disjoint domains/codomains).

    PROOF CONNECTIVITY:
    CategoryLaws → CategoryBridge → VMState → VMStep → MuCostModel → NoFreeInsight
*)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import CategoryLaws CategoryBridge.
From Kernel Require Import VMState VMStep MuCostModel NoFreeInsight.

(** ** Tensor of Couplings *)

(** The tensor (parallel composition) of two couplings is their disjoint union. *)
Definition coupling_tensor (r1 r2 : list (nat * nat)) : list (nat * nat) := r1 ++ r2.

(** ** Composition distributes over coupling union (both sides) *)

(** relational_compose distributes over union on the LEFT:
    (r1 ++ r2) ; s ≡ (r1 ; s) ++ (r2 ; s) *)
Lemma relational_compose_union_left :
  forall r1 r2 s,
    CategoryLaws.relational_compose (r1 ++ r2) s ≡
    CategoryLaws.relational_compose r1 s ++
    CategoryLaws.relational_compose r2 s.
Proof.
  intros r1 r2 s a c.
  rewrite CategoryLaws.relational_compose_spec.
  rewrite in_app_iff.
  split.
  - intros [b [Hab Hbc]].
    rewrite in_app_iff in Hab.
    destruct Hab as [H1 | H2].
    + left. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
    + right. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
  - intros [H | H].
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split; [apply in_app_iff; left | ]; assumption.
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split; [apply in_app_iff; right | ]; assumption.
Qed.

(** relational_compose distributes over union on the RIGHT:
    r ; (s1 ++ s2) ≡ (r ; s1) ++ (r ; s2) *)
Lemma relational_compose_union_right :
  forall r s1 s2,
    CategoryLaws.relational_compose r (s1 ++ s2) ≡
    CategoryLaws.relational_compose r s1 ++
    CategoryLaws.relational_compose r s2.
Proof.
  intros r s1 s2 a c.
  rewrite CategoryLaws.relational_compose_spec.
  rewrite in_app_iff.
  split.
  - intros [b [Hab Hbc]].
    rewrite in_app_iff in Hbc.
    destruct Hbc as [H1 | H2].
    + left. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
    + right. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
  - intros [H | H].
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split; [exact Hab | apply in_app_iff; left; exact Hbc].
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split; [exact Hab | apply in_app_iff; right; exact Hbc].
Qed.

(** ** Tensor Bifunctor: Interchange Law *)

(** The key monoidal coherence property:
    (f⊗g) ; (f'⊗g') ≡ (f;f') ⊗ (g;g')
    when f;g' ≡ [] and g;f' ≡ [] (cross terms are empty).

    This models the situation where f and g act on disjoint sets of objects:
    f acts on A→B, g acts on C→D (disjoint from A,B), and similarly for f',g'.
    Then f cannot compose with g' (their intermediate objects are disjoint)
    and g cannot compose with f'. *)
Theorem tensor_bifunctor :
  forall (pf pg pf' pg' : list (nat * nat)),
    CategoryLaws.relational_compose pf pg' ≡ [] ->
    CategoryLaws.relational_compose pg pf' ≡ [] ->
    CategoryLaws.relational_compose
      (pf ++ pg)
      (pf' ++ pg')
    ≡
    (CategoryLaws.relational_compose pf pf') ++
    (CategoryLaws.relational_compose pg pg').
Proof.
  intros pf pg pf' pg' Hcross_fg' Hcross_gf' a c.
  rewrite CategoryLaws.relational_compose_spec.
  rewrite in_app_iff.
  split.
  - (* Forward: ∃b, (a,b)∈(pf++pg) ∧ (b,c)∈(pf'++pg') → in RHS *)
    intros [b [Hab Hbc]].
    rewrite in_app_iff in Hab.
    rewrite in_app_iff in Hbc.
    destruct Hab as [Hf | Hg], Hbc as [Hf' | Hg'].
    + (* case 1: (a,b)∈pf, (b,c)∈pf' → pf;pf' *)
      left. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
    + (* case 2: (a,b)∈pf, (b,c)∈pg' → pf;pg' — must be empty *)
      exfalso.
      assert (Hin : In (a, c) (CategoryLaws.relational_compose pf pg')).
      { apply CategoryLaws.relational_compose_spec. exists b. split; assumption. }
      apply (Hcross_fg' a c) in Hin. simpl in Hin. exact Hin.
    + (* case 3: (a,b)∈pg, (b,c)∈pf' → pg;pf' — must be empty *)
      exfalso.
      assert (Hin : In (a, c) (CategoryLaws.relational_compose pg pf')).
      { apply CategoryLaws.relational_compose_spec. exists b. split; assumption. }
      apply (Hcross_gf' a c) in Hin. simpl in Hin. exact Hin.
    + (* case 4: (a,b)∈pg, (b,c)∈pg' → pg;pg' *)
      right. apply CategoryLaws.relational_compose_spec. exists b. split; assumption.
  - (* Backward: in RHS → ∃b, (a,b)∈(pf++pg) ∧ (b,c)∈(pf'++pg') *)
    intros [H | H].
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split.
      * apply in_app_iff. left. exact Hab.
      * apply in_app_iff. left. exact Hbc.
    + apply CategoryLaws.relational_compose_spec in H.
      destruct H as [b [Hab Hbc]].
      exists b. split.
      * apply in_app_iff. right. exact Hab.
      * apply in_app_iff. right. exact Hbc.
Qed.

(** ** MORPH_TENSOR is a non-cert-setter *)

Lemma instr_morph_tensor_non_cert :
  forall dst f g cost,
    is_cert_setterb (instr_morph_tensor dst f g cost) = false.
Proof. intros. exact (instr_morph_tensor_not_cert_setter dst f g cost). Qed.

(** MORPH_TENSOR cost is exactly mu_delta *)
Lemma morph_tensor_cost_eq : forall dst f g cost,
  instruction_cost (instr_morph_tensor dst f g cost) = cost.
Proof. intros. reflexivity. Qed.

(** ** Structural Identity of Tensor Unit *)

Lemma coupling_tensor_unit_left : forall r,
  coupling_tensor [] r = r.
Proof. reflexivity. Qed.

Lemma coupling_tensor_unit_right : forall r,
  coupling_tensor r [] = r.
Proof. intros. unfold coupling_tensor. apply app_nil_r. Qed.

Lemma coupling_tensor_assoc : forall r1 r2 r3,
  coupling_tensor (coupling_tensor r1 r2) r3 =
  coupling_tensor r1 (coupling_tensor r2 r3).
Proof. intros. unfold coupling_tensor. symmetry. apply app_assoc. Qed.

(** ** Summary: Monoidal coherence *)

(** The coupling_tensor operation (list append) gives a strict symmetric monoidal
    structure at the coupling level:
    - Associativity: (r1⊗r2)⊗r3 = r1⊗(r2⊗r3)
    - Left unit:  []⊗r = r
    - Right unit: r⊗[] = r
    - Bifunctoriality: (f⊗g);(f'⊗g') ≡ (f;f')⊗(g;g') when cross-terms vanish

    MORPH_TENSOR in the VM implements this by appending coupling pair lists.
    The tensor is non-cert-setting (no knowledge creation), consistent with
    the NoFreeInsight principle that only certified assertions cost mu. *)
Theorem monoidal_coherence :
  forall r1 r2 r3,
    coupling_tensor (coupling_tensor r1 r2) r3 =
    coupling_tensor r1 (coupling_tensor r2 r3) /\
    coupling_tensor [] r1 = r1 /\
    coupling_tensor r1 [] = r1.
Proof.
  intros. split; [| split].
  - apply coupling_tensor_assoc.
  - apply coupling_tensor_unit_left.
  - apply coupling_tensor_unit_right.
Qed.
