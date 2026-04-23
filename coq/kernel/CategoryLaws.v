(** CategoryLaws: the raw relation algebra behind the category story

  This file is the clean mathematical core. Before I talk about morphism IDs,
  graph updates, or VM instructions, I need the relation algebra to hold on its
  own terms.

  The main facts are:
  1. relational composition is associative
  2. diagonal relations act like left and right identities
  3. composition respects the coupling-equivalence notion used in this repo

  Most of the file is standalone combinatorics on nat pairs. The short kernel
  bridge at the end only says that the same composition really is the one the
  kernel uses.
*)

Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Lia.
Import ListNotations.

(** ** Relational Composition on Nat Pairs *)

(** A coupling is just a finite binary relation written as source/target pairs. *)
Definition Coupling := list (nat * nat).

(** Relational composition: (a,c) ∈ r1;r2 iff ∃b, (a,b) ∈ r1 ∧ (b,c) ∈ r2 *)
Definition relational_compose (r1 r2 : Coupling) : Coupling :=
  flat_map (fun '(a, b) =>
    map (fun '(b', c) => (a, c))
        (filter (fun '(b', _) => Nat.eqb b b') r2)
  ) r1.

(** Diagonal relation: {(x,x) | x ∈ region} *)
Definition diagonal (region : list nat) : Coupling :=
  map (fun x => (x, x)) region.

(** ** Membership Predicates *)

Definition In_coupling (a c : nat) (r : Coupling) : Prop :=
  In (a, c) r.

Definition composable (r1 r2 : Coupling) (a b c : nat) : Prop :=
  In (a, b) r1 /\ In (b, c) r2.

(** ** Helper Lemmas *)

Lemma filter_In_iff : forall {A : Type} (f : A -> bool) (x : A) (l : list A),
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  intros A f x l.
  induction l as [| h t IH]; simpl.
  - split; intros H; [destruct H | destruct H as [[] _]].
  - destruct (f h) eqn:Hfh.
    + simpl. split.
      * intros [Heq | Hin].
        -- subst. split; [left; reflexivity | assumption].
        -- apply IH in Hin. destruct Hin as [Hin Hfx].
           split; [right; assumption | assumption].
      * intros [[Heq | Hin] Hfx].
        -- left. assumption.
        -- right. apply IH. split; assumption.
    + split.
      * intros Hin. apply IH in Hin. destruct Hin as [Hin Hfx].
        split; [right; assumption | assumption].
      * intros [[Heq | Hin] Hfx].
        -- subst. rewrite Hfx in Hfh. discriminate.
        -- apply IH. split; assumption.
Qed.

Lemma flat_map_In : forall {A B : Type} (f : A -> list B) (y : B) (l : list A),
  In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
Proof.
  intros A B f y l.
  induction l as [| h t IH]; simpl.
  - split.
    + intros [].
    + intros [x [[] _]].
  - rewrite in_app_iff. split.
    + intros [Hin_fh | Hin_flat].
      * exists h. split; [left; reflexivity | assumption].
      * apply IH in Hin_flat. destruct Hin_flat as [x [Hin_t Hin_fx]].
        exists x. split; [right; assumption | assumption].
    + intros [x [[Heq | Hin_t] Hin_fx]].
      * subst. left. assumption.
      * right. apply IH. exists x. split; assumption.
Qed.

Lemma map_In : forall {A B : Type} (f : A -> B) (y : B) (l : list A),
  In y (map f l) <-> exists x, In x l /\ y = f x.
Proof.
  intros A B f y l.
  induction l as [| h t IH]; simpl.
  - split.
    + intros [].
    + intros [x [[] _]].
  - split.
    + intros [Heq | Hin].
      * exists h. split; [left; reflexivity | symmetry; assumption].
      * apply IH in Hin. destruct Hin as [x [Hin Heq]].
        exists x. split; [right; assumption | assumption].
    + intros [x [[Heq | Hin] Hfy]].
      * subst. left. reflexivity.
      * right. apply IH. exists x. split; assumption.
Qed.

(** ** Characterization of Relational Composition *)

Theorem relational_compose_spec : forall r1 r2 a c,
  In (a, c) (relational_compose r1 r2) <->
  exists b, In (a, b) r1 /\ In (b, c) r2.
Proof.
  intros r1 r2 a c.
  unfold relational_compose.
  rewrite flat_map_In.
  split.
  - intros [[a' b] [Hin_r1 Hin_map]].
    rewrite map_In in Hin_map.
    destruct Hin_map as [[b' c'] [Hin_filter Heq]].
    injection Heq as Ha Hc. subst a' c'.
    rewrite filter_In_iff in Hin_filter.
    destruct Hin_filter as [Hin_r2 Heqb].
    apply Nat.eqb_eq in Heqb. subst b'.
    exists b. split; assumption.
  - intros [b [Hin_r1 Hin_r2]].
    exists (a, b). split; [assumption |].
    rewrite map_In.
    exists (b, c). split.
    + rewrite filter_In_iff. split; [assumption |].
      apply Nat.eqb_eq. reflexivity.
    + reflexivity.
Qed.

(** ** Associativity of Relational Composition *)

(** For category laws, literal list equality is the wrong target.
  We care about whether two coupling lists represent the same relation. *)

Definition coupling_equiv (r1 r2 : Coupling) : Prop :=
  forall a c, In (a, c) r1 <-> In (a, c) r2.

Notation "r1 ≡ r2" := (coupling_equiv r1 r2) (at level 70).

(* DEFINITIONAL LEMMA — coupling_equiv is pointwise iff, so reflexivity is immediate. *)
Lemma coupling_equiv_refl : forall r, r ≡ r.
Proof.
  intros r a c. reflexivity.
Qed.

Lemma coupling_equiv_sym : forall r1 r2, r1 ≡ r2 -> r2 ≡ r1.
Proof.
  intros r1 r2 H a c. symmetry. apply H.
Qed.

Lemma coupling_equiv_trans : forall r1 r2 r3, r1 ≡ r2 -> r2 ≡ r3 -> r1 ≡ r3.
Proof.
  intros r1 r2 r3 H12 H23 a c.
  split; intros H.
  - apply H23. apply H12. exact H.
  - apply H12. apply H23. exact H.
Qed.

(** Associativity up to equivalence *)
Theorem relational_compose_assoc : forall r1 r2 r3,
  relational_compose (relational_compose r1 r2) r3 ≡
  relational_compose r1 (relational_compose r2 r3).
Proof.
  intros r1 r2 r3 a c.
  rewrite !relational_compose_spec.
  split.
  - intros [b [Hab Hbc]].
    rewrite relational_compose_spec in Hab.
    destruct Hab as [b' [Hab' Hb'b]].
    exists b'. split; [assumption |].
    rewrite relational_compose_spec.
    exists b. split; assumption.
  - intros [b [Hab Hbc]].
    rewrite relational_compose_spec in Hbc.
    destruct Hbc as [b' [Hbb' Hb'c]].
    exists b'. split; [| assumption].
    rewrite relational_compose_spec.
    exists b. split; assumption.
Qed.

(** ** Diagonal Identity Laws *)

(** Left identity: diagonal(region) ; r = r when r's domain ⊆ region *)
Theorem relational_compose_diagonal_left : forall region r,
  (forall a b, In (a, b) r -> In a region) ->
  relational_compose (diagonal region) r ≡ r.
Proof.
  intros region r Hdomain a c.
  rewrite relational_compose_spec.
  split.
  - intros [b [Hdiag Hbc]].
    unfold diagonal in Hdiag.
    rewrite map_In in Hdiag.
    destruct Hdiag as [x [Hin_region Heq]].
    injection Heq as Ha Hb. subst a b.
    assumption.
  - intros Hac.
    exists a. split.
    + unfold diagonal. rewrite map_In.
      exists a. split; [| reflexivity].
      apply Hdomain with c. assumption.
    + assumption.
Qed.

(** Right identity: r ; diagonal(region) = r when r's codomain ⊆ region *)
Theorem relational_compose_diagonal_right : forall region r,
  (forall a b, In (a, b) r -> In b region) ->
  relational_compose r (diagonal region) ≡ r.
Proof.
  intros region r Hcodomain a c.
  rewrite relational_compose_spec.
  split.
  - intros [b [Hab Hdiag]].
    unfold diagonal in Hdiag.
    rewrite map_In in Hdiag.
    destruct Hdiag as [x [Hin_region Heq]].
    injection Heq as Hb Hc. subst b c.
    assumption.
  - intros Hac.
    exists c. split; [assumption |].
    unfold diagonal. rewrite map_In.
    exists c. split; [| reflexivity].
    apply Hcodomain with a. assumption.
Qed.

(** ** Composition Respects Equivalence *)

Theorem relational_compose_compat_l : forall r1 r1' r2,
  r1 ≡ r1' ->
  relational_compose r1 r2 ≡ relational_compose r1' r2.
Proof.
  intros r1 r1' r2 Heq a c.
  rewrite !relational_compose_spec.
  split; intros [b [H1 H2]]; exists b; split; try assumption.
  - apply Heq. assumption.
  - apply Heq. assumption.
Qed.

Theorem relational_compose_compat_r : forall r1 r2 r2',
  r2 ≡ r2' ->
  relational_compose r1 r2 ≡ relational_compose r1 r2'.
Proof.
  intros r1 r2 r2' Heq a c.
  rewrite !relational_compose_spec.
  split; intros [b [H1 H2]]; exists b; split; try assumption.
  - apply Heq. assumption.
  - apply Heq. assumption.
Qed.

Theorem relational_compose_compat : forall r1 r1' r2 r2',
  r1 ≡ r1' ->
  r2 ≡ r2' ->
  relational_compose r1 r2 ≡ relational_compose r1' r2'.
Proof.
  intros r1 r1' r2 r2' H1 H2.
  eapply coupling_equiv_trans.
  - apply relational_compose_compat_l. exact H1.
  - apply relational_compose_compat_r. exact H2.
Qed.

(** ** Empty Relation *)

Definition empty_coupling : Coupling := nil.

Theorem relational_compose_empty_l : forall r,
  relational_compose empty_coupling r ≡ empty_coupling.
Proof.
  intros r a c.
  rewrite relational_compose_spec.
  split.
  - intros [b [H _]]. destruct H.
  - intros H. destruct H.
Qed.

Theorem relational_compose_empty_r : forall r,
  relational_compose r empty_coupling ≡ empty_coupling.
Proof.
  intros r a c.
  rewrite relational_compose_spec.
  split.
  - intros [b [_ H]]. destruct H.
  - intros H. destruct H.
Qed.

(** ** Disjoint Union for Tensor Product *)

Definition coupling_union (r1 r2 : Coupling) : Coupling := r1 ++ r2.

Theorem coupling_union_spec : forall r1 r2 a c,
  In (a, c) (coupling_union r1 r2) <-> In (a, c) r1 \/ In (a, c) r2.
Proof.
  intros r1 r2 a c.
  unfold coupling_union.
  apply in_app_iff.
Qed.

(** Bifunctoriality: (f⊗g) ; (f'⊗g') = (f;f') ⊗ (g;g')
    when domains/codomains are disjoint *)

(** We state this as: if r1, r2 are disjoint (no shared endpoints)
    and r1', r2' are disjoint, then composition distributes over union. *)

Definition disjoint_couplings (r1 r2 : Coupling) : Prop :=
  (forall a b c, In (a, b) r1 -> ~ In (a, c) r2) /\
  (forall a b c, In (a, b) r1 -> ~ In (c, b) r2) /\
  (forall a b c, In (a, b) r2 -> ~ In (a, c) r1) /\
  (forall a b c, In (a, b) r2 -> ~ In (c, b) r1).

(** Summary of what is actually proved here.

  Up to coupling equivalence, this file proves the category skeleton:
  composition associates, diagonals act like identities, empty relations are
  absorbing, and the equivalence notion behaves properly.

  That is enough for the next files to stop hand-waving about category laws
  and start applying them to the kernel graph. *)

(** I keep these theorems at top level so downstream files can import them directly. *)

(** Kernel bridge.

  The abstract relational_compose above is not a parallel universe. VMState.v
  defines the same function body for kernel couplings. The lemmas below make
  that explicit so CategoryBridge.v can reuse the algebra without pretending
  the names just happen to line up. *)
From Kernel Require Import VMState VMStep MuCostModel.

(** VMState.relational_compose is definitionally identical to the relational_compose
    defined above (same flat_map/filter/map body). This lemma makes the
    connection explicit and connects this file to the kernel foundation chain. *)
Lemma kernel_relational_compose_same : forall (r1 r2 : list (nat * nat)),
  VMState.relational_compose r1 r2 = relational_compose r1 r2.
Proof.
  intros r1 r2. unfold VMState.relational_compose, relational_compose. reflexivity.
Qed.

(** The cost of a categorical composition instruction is exactly its mu_delta
    parameter — no hidden cost inflation for non-cert-setter morph operations. *)
Lemma morph_compose_cost_is_delta : forall (dst m1 m2 cost : nat),
  instruction_cost (instr_compose dst m1 m2 cost) = cost.
Proof.
  intros. reflexivity.
Qed.

(** Category law: relational composition of CouplingData pairs is associative.
    This is the kernel-facing statement of relational_compose_assoc, expressed
    using VMState.CouplingData — the kernel type for morphism couplings. *)
Lemma coupling_data_compose_assoc :
  forall (cd1 cd2 cd3 : CouplingData),
    relational_compose
      (relational_compose cd1.(coupling_pairs) cd2.(coupling_pairs))
      cd3.(coupling_pairs)
    ≡
    relational_compose
      cd1.(coupling_pairs)
      (relational_compose cd2.(coupling_pairs) cd3.(coupling_pairs)).
Proof.
  intros cd1 cd2 cd3.
  apply relational_compose_assoc.
Qed.

(** ** Separability of Couplings

    A coupling is SEPARABLE (functional) if every source maps to at most one
    target — i.e., it is the graph of a partial function from sources to
    targets. This is the computational sense of separability: the coupling
    can be described by an independent function on each dimension.

    A coupling is NON-SEPARABLE if some source maps to two different targets,
    creating a correlation that cannot be explained by independent functions.

    In the context of quantum entanglement: non-separable couplings can
    represent correlated pairs whose statistics violate Bell inequalities.
    The entanglement certification program uses morphisms with non-separable
    coupling data as certified entanglement witnesses. *)

(** A coupling is separable if it is functional: each source has at most one target. *)
Definition separable_coupling (r : Coupling) : Prop :=
  forall a c1 c2, In (a, c1) r -> In (a, c2) r -> c1 = c2.

(** A coupling is non-separable if some source maps to two distinct targets. *)
Definition non_separable_coupling (r : Coupling) : Prop :=
  exists a c1 c2, c1 <> c2 /\ In (a, c1) r /\ In (a, c2) r.

(** Separable and non-separable are mutually exclusive. *)
Lemma separable_not_non_separable : forall r,
  separable_coupling r -> ~ non_separable_coupling r.
Proof.
  intros r Hsep [a [c1 [c2 [Hneq [H1 H2]]]]].
  apply Hneq. exact (Hsep a c1 c2 H1 H2).
Qed.

(** The empty coupling is separable. *)
Lemma empty_coupling_separable : separable_coupling [].
Proof.
  intros a c1 c2 H. inversion H.
Qed.

(** The diagonal coupling is separable (it's the identity function). *)
Lemma diagonal_coupling_separable : forall region,
  separable_coupling (diagonal region).
Proof.
  intros region a c1 c2 H1 H2.
  unfold diagonal in *.
  apply in_map_iff in H1. destruct H1 as [x [Hx _]]. injection Hx; intros; subst.
  apply in_map_iff in H2. destruct H2 as [y [Hy _]]. injection Hy; intros; subst.
  reflexivity.
Qed.

(** A coupling with repeated source is non-separable. *)
Lemma coupling_non_separable_witness : forall a c1 c2,
  c1 <> c2 ->
  non_separable_coupling [(a, c1); (a, c2)].
Proof.
  intros a c1 c2 H.
  exists a, c1, c2. split. exact H.
  split. left. reflexivity. right. left. reflexivity.
Qed.

(** Projection helpers. *)
Definition coupling_sources (r : Coupling) : list nat := map fst r.
Definition coupling_targets (r : Coupling) : list nat := map snd r.

(** The XOR coupling {(0,1),(1,0)} is separable (it's a bijection: f(0)=1, f(1)=0). *)
Definition xor_coupling : Coupling := [(0,1);(1,0)].

Lemma xor_coupling_separable : separable_coupling xor_coupling.
Proof.
  intros a c1 c2 H1 H2.
  unfold xor_coupling in *.
  destruct H1 as [H1|[H1|[]]]; destruct H2 as [H2|[H2|[]]];
  inversion H1; inversion H2; subst; try reflexivity; try discriminate.
Qed.

(** Non-separable witness: source 0 maps to both 0 and 1. *)
Definition entangled_coupling : Coupling := [(0,0);(0,1)].

Lemma entangled_coupling_non_separable : non_separable_coupling entangled_coupling.
Proof.
  apply coupling_non_separable_witness. lia.
Qed.
