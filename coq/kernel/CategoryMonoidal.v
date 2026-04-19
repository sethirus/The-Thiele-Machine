(** CategoryMonoidal: what MORPH_TENSOR is allowed to mean

    MORPH_TENSOR is supposed to combine two disjoint morphisms in parallel.
    At the coupling level that means list append: put the two coupling lists
    next to each other and keep going.

    The theorem that matters is the interchange law:

      (f⊗g) ; (f'⊗g') = (f;f') ⊗ (g;g')

    when the cross terms vanish. If that law failed, MORPH_TENSOR would be a
    convenient opcode name with no coherent categorical meaning behind it.
*)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import CategoryLaws CategoryBridge.
From Kernel Require Import VMState VMStep MuCostModel NoFreeInsight.

(** Tensor of couplings. *)

(** The tensor (parallel composition) of two couplings is their disjoint union. *)
Definition coupling_tensor (r1 r2 : list (nat * nat)) : list (nat * nat) := r1 ++ r2.

(** Composition distributes over union on both sides. *)

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

(** Interchange law. *)

(** This is the load-bearing coherence property:
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

(** MORPH_TENSOR is not a cert-setter. *)

Lemma instr_morph_tensor_non_cert :
  forall dst f g cost,
    is_cert_setterb (instr_morph_tensor dst f g cost) = false.
Proof. intros. exact (instr_morph_tensor_not_cert_setter dst f g cost). Qed.

(** MORPH_TENSOR keeps the plain mu_delta cost rule. *)
Lemma morph_tensor_cost_eq : forall dst f g cost,
  instruction_cost (instr_morph_tensor dst f g cost) = cost.
Proof. intros. reflexivity. Qed.

(** Tensor unit laws. *)

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

(** Summary.

  At the coupling level, tensor is just append. That gives the strict unit and
  associativity laws for free, and tensor_bifunctor gives the interchange law
  once the cross terms are empty.

  The NoFreeInsight-facing statement is narrow: MORPH_TENSOR is not a
  cert-setter, and its cost is just mu_delta. I am not claiming tensor is free.
  I am claiming it does not create certified knowledge by itself. *)
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
