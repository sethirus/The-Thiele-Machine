(** CategoryBridge: take the category laws off the whiteboard and pin them to the graph

   CategoryLaws.v proves the clean relational facts first: composition is
   associative, diagonal relations act like identities, and the equivalence
   notion is the right one for coupling lists.

   This file is where those facts touch the kernel. I take the actual graph
   operations here — graph_compose_morphisms and graph_add_identity — and show
   that their couplings do what the relational story says they should do.

   The load-bearing claims are simple:
   1. composing graph morphisms really builds the relational composition
   2. the coupling-level composition law is associative
   3. graph_add_identity really builds an identity morphism
   4. MORPH_ASSERT is the only morphism opcode that the runtime policy treats
     as a cert-setter
   5. the cost equations for the seven morphism instructions are exactly the
     ones stated in VMStep.v
   6. on the records COMPOSE stores in the graph, composition is associative,
     every identity arrow is a left and right unit, and the composite of two
     identities is again an identity

   If any of that is false, the category extension is just rhetoric. This file
   is where it stops being rhetoric.
*)

From Coq Require Import List Bool Arith.PeanoNat Lia String.
Import ListNotations.
Open Scope string_scope.

From Kernel Require Import CategoryLaws.
From Kernel Require Import VMState VMStep MuCostModel NoFreeInsight.

(** When [graph_add_morphism] returns [(g', new_id)], looking up
    [new_id] in [g'] returns the newly constructed [MorphismState]. *)
Lemma graph_add_morphism_new_id_lookup :
  forall g src dst c is_id,
    let '(g', new_id) := graph_add_morphism g src dst c is_id in
    graph_lookup_morphism g' new_id =
    Some {| morph_source := src;
            morph_target := dst;
            morph_coupling := normalize_coupling c;
            morph_is_identity := is_id;
               morph_cert_cost := 0 |}.
Proof.
  intros g src dst c is_id.
  unfold graph_add_morphism. simpl.
  unfold graph_lookup_morphism. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Existing morphisms are unaffected by graph_add_morphism when mid differs
    from the newly allocated ID (which is pg_next_morph_id). *)
Lemma graph_add_morphism_old_id_lookup :
  forall g src dst c is_id mid,
    mid <> g.(pg_next_morph_id) ->
    graph_lookup_morphism (fst (graph_add_morphism g src dst c is_id)) mid =
    graph_lookup_morphism g mid.
Proof.
  intros g src dst c is_id mid Hne.
  unfold graph_add_morphism. simpl.
  unfold graph_lookup_morphism. simpl.
  destruct (Nat.eqb (pg_next_morph_id g) mid) eqn:Heq.
  - apply Nat.eqb_eq in Heq. exfalso. apply Hne. symmetry. exact Heq.
  - reflexivity.
Qed.

(** graph_compose_morphisms really builds the relational composition,
    except where the identity flags short-circuit it. *)

(** When graph_compose_morphisms g m1 m2 = Some (g', composed_id), the new
    morphism's coupling pairs are: none when both are flagged identities (the
    composite is itself a flagged identity), m2's coupling if only m1 is a
    flagged identity (id;f = f), m1's coupling if only m2 is (f;id = f), and
    the relational composition of m1 and m2's couplings otherwise. Its flag is
    set exactly when both flags are. This is the foundational correctness
    theorem for COMPOSE, including its identity law. *)
Lemma graph_compose_morphisms_coupling :
  forall g m1 m2 g' composed_id,
    graph_compose_morphisms g m1 m2 = Some (g', composed_id) ->
    exists ms1 ms2 ms_c,
      graph_lookup_morphism g m1 = Some ms1 /\
      graph_lookup_morphism g m2 = Some ms2 /\
      graph_lookup_morphism g' composed_id = Some ms_c /\
      ms_c.(morph_is_identity) = ms1.(morph_is_identity) && ms2.(morph_is_identity) /\
      ms_c.(morph_coupling).(coupling_pairs) ≡
      (if ms1.(morph_is_identity) && ms2.(morph_is_identity)
       then []
       else if ms1.(morph_is_identity)
       then ms2.(morph_coupling).(coupling_pairs)
       else if ms2.(morph_is_identity)
            then ms1.(morph_coupling).(coupling_pairs)
            else relational_compose
                   ms1.(morph_coupling).(coupling_pairs)
                   ms2.(morph_coupling).(coupling_pairs)).
Proof.
  intros g m1 m2 g' composed_id H.
  unfold graph_compose_morphisms in H.
  destruct (graph_lookup_morphism g m1) as [ms1|] eqn:Hm1; [| discriminate].
  destruct (graph_lookup_morphism g m2) as [ms2|] eqn:Hm2; [| discriminate].
  destruct (Nat.eqb (morph_target ms1) (morph_source ms2)) eqn:Heq; [| discriminate].
  injection H as Hga.
  subst g'. subst composed_id.
  eexists ms1, ms2. eexists.
  split; [reflexivity|]. split; [reflexivity|].
  split.
  - unfold graph_lookup_morphism. simpl. rewrite Nat.eqb_refl. reflexivity.
  - split; [reflexivity|].
    (* Coupling pairs: normalize_coupling wraps nodup; nodup_In gives set-eq *)
    simpl. intros a c_.
    destruct (morph_is_identity ms1), (morph_is_identity ms2); simpl;
      rewrite ?nodup_In; reflexivity.
Qed.

(** Old morphisms are still accessible in the graph produced by composition. *)
Lemma graph_compose_preserves_morphism_lookup :
  forall g m1 m2 g' new_id mid,
    graph_compose_morphisms g m1 m2 = Some (g', new_id) ->
    mid <> new_id ->
    graph_lookup_morphism g' mid = graph_lookup_morphism g mid.
Proof.
  intros g m1 m2 g' new_id mid H Hne.
  unfold graph_compose_morphisms in H.
  destruct (graph_lookup_morphism g m1) as [ms1|]; [| discriminate].
  destruct (graph_lookup_morphism g m2) as [ms2|]; [| discriminate].
  destruct (Nat.eqb (morph_target ms1) (morph_source ms2)); [| discriminate].
  injection H as Hg' Hid.
  subst new_id.
  rewrite <- Hg'.
  apply graph_add_morphism_old_id_lookup.
  intro Heq. apply Hne. exact Heq.
Qed.

(** Associativity, lifted back to the kernel setting. *)

(** Relational composition is associative (lifting CategoryLaws.relational_compose_assoc
    to the kernel setting). At the coupling level, (f;g);k = f;(g;k). *)
Theorem morph_compose_assoc_coupling :
  forall (pairs_f pairs_g pairs_k : list (nat * nat)),
    CategoryLaws.relational_compose
      (CategoryLaws.relational_compose pairs_f pairs_g)
      pairs_k
    ≡
    CategoryLaws.relational_compose
      pairs_f
      (CategoryLaws.relational_compose pairs_g pairs_k).
Proof.
  intros. apply CategoryLaws.relational_compose_assoc.
Qed.

(** If both triple-composition orderings make sense, they agree at the coupling level. *)
Theorem morph_graph_compose_assoc :
  forall g f_id g_id k_id ms_f ms_g ms_k,
    graph_lookup_morphism g f_id = Some ms_f ->
    graph_lookup_morphism g g_id = Some ms_g ->
    graph_lookup_morphism g k_id = Some ms_k ->
    Nat.eqb ms_f.(morph_target) ms_g.(morph_source) = true ->
    Nat.eqb ms_g.(morph_target) ms_k.(morph_source) = true ->
    (* Left assoc: (f;g);k *)
    CategoryLaws.relational_compose
      (CategoryLaws.relational_compose
         ms_f.(morph_coupling).(coupling_pairs)
         ms_g.(morph_coupling).(coupling_pairs))
      ms_k.(morph_coupling).(coupling_pairs)
    ≡
    (* Right assoc: f;(g;k) *)
    CategoryLaws.relational_compose
      ms_f.(morph_coupling).(coupling_pairs)
      (CategoryLaws.relational_compose
         ms_g.(morph_coupling).(coupling_pairs)
         ms_k.(morph_coupling).(coupling_pairs)).
Proof.
  intros. apply CategoryLaws.relational_compose_assoc.
Qed.

(** Identity laws. *)

(** The morphism graph_add_identity records has its identity flag set. *)
Lemma graph_add_identity_coupling :
  forall g mid g' morph_id ms_mod,
    graph_lookup g mid = Some ms_mod ->
    graph_add_identity g mid = Some (g', morph_id) ->
    exists ms_id,
      graph_lookup_morphism g' morph_id = Some ms_id /\
      ms_id.(morph_is_identity) = true.
Proof.
  intros g mid g' morph_id ms_mod Hmod Hid.
  unfold graph_add_identity in Hid.
  rewrite Hmod in Hid.
  unfold graph_add_morphism in Hid. simpl in Hid.
  injection Hid as Hg' Hmid.
  subst g' morph_id.
  eexists. split.
  - unfold graph_lookup_morphism. simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Left identity: diagonal(dom(f));f = f at coupling level.
    Requires that f's source region IS the domain of f's coupling. *)
Theorem morph_id_left_coupling :
  forall (region : list nat) (pairs_f : list (nat * nat)),
    (forall a b, In (a, b) pairs_f -> In a region) ->
    CategoryLaws.relational_compose (map (fun x => (x, x)) region) pairs_f ≡ pairs_f.
Proof.
  intros region pairs_f Hdom.
  apply CategoryLaws.relational_compose_diagonal_left.
  exact Hdom.
Qed.

(** Right identity: f;diagonal(cod(f)) = f at coupling level.
    Requires that f's target region IS the codomain of f's coupling. *)
Theorem morph_id_right_coupling :
  forall (region : list nat) (pairs_f : list (nat * nat)),
    (forall a b, In (a, b) pairs_f -> In b region) ->
    CategoryLaws.relational_compose pairs_f (map (fun x => (x, x)) region) ≡ pairs_f.
Proof.
  intros region pairs_f Hcod.
  apply CategoryLaws.relational_compose_diagonal_right.
  exact Hcod.
Qed.

(** * The category laws on stored arrows

    The laws above are about coupling lists. The ones below are about the
    arrows COMPOSE actually stores in the graph. Two stored arrows are the
    same arrow when they have the same source, the same target, the same
    identity flag, and, for arrows without the flag, the same set of coupling
    pairs. A flagged arrow denotes the identity on its object: COMPOSE never
    reads its stored pairs. Labels are debugger names and are not compared. *)

Definition stored_arrow_equiv (x y : MorphismState) : Prop :=
  morph_source x = morph_source y /\
  morph_target x = morph_target y /\
  morph_is_identity x = morph_is_identity y /\
  (morph_is_identity x = false ->
     coupling_pairs (morph_coupling x) ≡ coupling_pairs (morph_coupling y)).

(** The coupling COMPOSE stores for f;h, before normalization. *)
Definition compose_coupling (f h : MorphismState) : CouplingData :=
  if f.(morph_is_identity) && h.(morph_is_identity) then empty_coupling_data
  else {| coupling_pairs :=
            if f.(morph_is_identity)
            then h.(morph_coupling).(coupling_pairs)
            else if h.(morph_is_identity)
                 then f.(morph_coupling).(coupling_pairs)
                 else VMState.relational_compose
                        f.(morph_coupling).(coupling_pairs)
                        h.(morph_coupling).(coupling_pairs);
          coupling_label := f.(morph_coupling).(coupling_label) ++ ";" ++
                            h.(morph_coupling).(coupling_label) |}.

(** The record COMPOSE stores for f;h. *)
Definition composite_record (f h : MorphismState) : MorphismState :=
  {| morph_source := f.(morph_source);
     morph_target := h.(morph_target);
     morph_coupling := normalize_coupling (compose_coupling f h);
     morph_is_identity := f.(morph_is_identity) && h.(morph_is_identity);
     morph_cert_cost := 0 |}.

(** COMPOSE of two stored arrows with matching endpoints succeeds, stores
    [composite_record f h] under the next morphism id, and leaves every
    other morphism id where it was. *)
Lemma graph_compose_stored :
  forall g m1 m2 f h,
    graph_lookup_morphism g m1 = Some f ->
    graph_lookup_morphism g m2 = Some h ->
    morph_target f = morph_source h ->
    exists g',
      graph_compose_morphisms g m1 m2 = Some (g', pg_next_morph_id g) /\
      graph_lookup_morphism g' (pg_next_morph_id g) = Some (composite_record f h) /\
      pg_next_morph_id g' = S (pg_next_morph_id g) /\
      (forall mid, mid <> pg_next_morph_id g ->
         graph_lookup_morphism g' mid = graph_lookup_morphism g mid).
Proof.
  intros g m1 m2 f h H1 H2 Ht.
  exists (fst (graph_add_morphism g (morph_source f) (morph_target h)
                 (compose_coupling f h)
                 (morph_is_identity f && morph_is_identity h))).
  split; [|split; [|split]].
  - unfold graph_compose_morphisms. rewrite H1, H2, Ht, Nat.eqb_refl. reflexivity.
  - unfold graph_add_morphism, graph_lookup_morphism. simpl.
    rewrite Nat.eqb_refl. reflexivity.
  - reflexivity.
  - intros mid Hne. apply graph_add_morphism_old_id_lookup. exact Hne.
Qed.

(** Every morphism id that a lookup finds in a well-formed graph is below
    the next morphism id. *)
Lemma well_formed_lookup_morphism_below :
  forall g mid ms,
    well_formed_graph g ->
    graph_lookup_morphism g mid = Some ms ->
    mid < pg_next_morph_id g.
Proof.
  intros g mid ms [_ [Hids _]] Hl.
  unfold graph_lookup_morphism in Hl.
  induction (pg_morphisms g) as [|[id m] rest IH]; simpl in *.
  - discriminate.
  - destruct Hids as [Hid Hrest].
    destruct (Nat.eqb id mid) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hid.
    + exact (IH Hrest Hl).
Qed.

Lemma nodup_pairs_equiv : forall (l : list (nat * nat)),
  nodup (pair_eq_dec Nat.eq_dec Nat.eq_dec) l ≡ l.
Proof. intros l a c. apply nodup_In. Qed.

(** The composite of two identity arrows is the identity arrow of their
    shared object, stored exactly as MORPH_ID stores one: flag set, coupling
    [empty_coupling_data], certification cost 0. *)
Theorem graph_compose_identities_is_identity :
  forall g m1 m2 i j,
    graph_lookup_morphism g m1 = Some i ->
    graph_lookup_morphism g m2 = Some j ->
    morph_is_identity i = true ->
    morph_is_identity j = true ->
    morph_target i = morph_source j ->
    exists g' r,
      graph_compose_morphisms g m1 m2 = Some (g', r) /\
      graph_lookup_morphism g' r =
        Some {| morph_source := morph_source i;
                morph_target := morph_target j;
                morph_coupling := empty_coupling_data;
                morph_is_identity := true;
                morph_cert_cost := 0 |}.
Proof.
  intros g m1 m2 i j H1 H2 Hi Hj Ht.
  destruct (graph_compose_stored g m1 m2 i j H1 H2 Ht) as [g' [Hc [Hl _]]].
  exists g', (pg_next_morph_id g). split; [exact Hc|].
  rewrite Hl. unfold composite_record, compose_coupling. rewrite Hi, Hj. reflexivity.
Qed.

(** Membership in a stored composite's pairs. *)
Lemma composite_record_pairs_In :
  forall f h a c,
    In (a, c) (coupling_pairs (morph_coupling (composite_record f h))) <->
    (if morph_is_identity f && morph_is_identity h then False
     else if morph_is_identity f then In (a, c) (coupling_pairs (morph_coupling h))
     else if morph_is_identity h then In (a, c) (coupling_pairs (morph_coupling f))
     else exists b, In (a, b) (coupling_pairs (morph_coupling f)) /\
                    In (b, c) (coupling_pairs (morph_coupling h))).
Proof.
  intros f h a c.
  unfold composite_record, compose_coupling.
  destruct (morph_is_identity f), (morph_is_identity h); simpl; rewrite ?nodup_In;
    try reflexivity.
  all: rewrite ?kernel_relational_compose_same, relational_compose_spec; reflexivity.
Qed.

Lemma composite_pairs_none : forall f h,
  morph_is_identity f = false -> morph_is_identity h = false -> forall a c,
  In (a, c) (coupling_pairs (morph_coupling (composite_record f h))) <->
  exists b, In (a, b) (coupling_pairs (morph_coupling f)) /\ In (b, c) (coupling_pairs (morph_coupling h)).
Proof.
  intros f h Hf Hh a c. rewrite composite_record_pairs_In, Hf, Hh. reflexivity.
Qed.

Lemma composite_pairs_left : forall f h,
  morph_is_identity f = true -> morph_is_identity h = false -> forall a c,
  In (a, c) (coupling_pairs (morph_coupling (composite_record f h))) <->
  In (a, c) (coupling_pairs (morph_coupling h)).
Proof.
  intros f h Hf Hh a c. rewrite composite_record_pairs_In, Hf, Hh. reflexivity.
Qed.

Lemma composite_pairs_right : forall f h,
  morph_is_identity f = false -> morph_is_identity h = true -> forall a c,
  In (a, c) (coupling_pairs (morph_coupling (composite_record f h))) <->
  In (a, c) (coupling_pairs (morph_coupling f)).
Proof.
  intros f h Hf Hh a c. rewrite composite_record_pairs_In, Hf, Hh. reflexivity.
Qed.

(** Associativity on stored arrows: for three stored arrows f, k, h with
    matching endpoints, both bracketings of f;k;h succeed and the two stored
    composites are the same arrow. *)
Theorem graph_compose_assoc_stored :
  forall g fi ki hi f k h,
    well_formed_graph g ->
    graph_lookup_morphism g fi = Some f ->
    graph_lookup_morphism g ki = Some k ->
    graph_lookup_morphism g hi = Some h ->
    morph_target f = morph_source k ->
    morph_target k = morph_source h ->
    exists g1 a g2 b g1' c g2' d x y,
      graph_compose_morphisms g fi ki = Some (g1, a) /\
      graph_compose_morphisms g1 a hi = Some (g2, b) /\
      graph_compose_morphisms g ki hi = Some (g1', c) /\
      graph_compose_morphisms g1' fi c = Some (g2', d) /\
      graph_lookup_morphism g2 b = Some x /\
      graph_lookup_morphism g2' d = Some y /\
      stored_arrow_equiv x y.
Proof.
  intros g fi ki hi f k h Hwf Hf Hk Hh Hfk Hkh.
  pose proof (well_formed_lookup_morphism_below g fi f Hwf Hf) as Bf.
  pose proof (well_formed_lookup_morphism_below g hi h Hwf Hh) as Bh.
  (* (f;k);h *)
  destruct (graph_compose_stored g fi ki f k Hf Hk Hfk) as [g1 [C1 [L1 [N1 O1]]]].
  assert (Hh1 : graph_lookup_morphism g1 hi = Some h)
    by (rewrite O1 by lia; exact Hh).
  destruct (graph_compose_stored g1 (pg_next_morph_id g) hi (composite_record f k) h L1 Hh1 Hkh)
    as [g2 [C2 [L2 _]]].
  (* f;(k;h) *)
  destruct (graph_compose_stored g ki hi k h Hk Hh Hkh) as [g1' [C1' [L1' [N1' O1']]]].
  assert (Hf1 : graph_lookup_morphism g1' fi = Some f)
    by (rewrite O1' by lia; exact Hf).
  destruct (graph_compose_stored g1' fi (pg_next_morph_id g) f (composite_record k h) Hf1 L1' Hfk)
    as [g2' [C2' [L2' _]]].
  exists g1, (pg_next_morph_id g), g2, (pg_next_morph_id g1),
         g1', (pg_next_morph_id g), g2', (pg_next_morph_id g1'),
         (composite_record (composite_record f k) h),
         (composite_record f (composite_record k h)).
  split; [exact C1|]. split; [exact C2|].
  split; [exact C1'|]. split; [exact C2'|].
  split; [exact L2|]. split; [exact L2'|].
  unfold stored_arrow_equiv.
  split; [reflexivity|]. split; [reflexivity|].
  split; [simpl; symmetry; apply andb_assoc|].
  simpl. intro Hflag. intros a0 c0.
  destruct (morph_is_identity f) eqn:If, (morph_is_identity k) eqn:Ik,
           (morph_is_identity h) eqn:Ih; simpl in Hflag; try discriminate.
  all: assert (Fk : morph_is_identity (composite_record f k) =
                    morph_is_identity f && morph_is_identity k) by reflexivity.
  all: assert (Kh : morph_is_identity (composite_record k h) =
                    morph_is_identity k && morph_is_identity h) by reflexivity.
  all: rewrite If, Ik in Fk; rewrite Ik, Ih in Kh.
  - (* f, k identities *)
    rewrite (composite_pairs_left _ _ Fk Ih), (composite_pairs_left _ _ If Kh),
            (composite_pairs_left _ _ Ik Ih). reflexivity.
  - (* f, h identities *)
    rewrite (composite_pairs_right _ _ Fk Ih), (composite_pairs_left _ _ If Kh),
            (composite_pairs_left _ _ If Ik), (composite_pairs_right _ _ Ik Ih).
    reflexivity.
  - (* f identity *)
    rewrite (composite_pairs_none _ _ Fk Ih), (composite_pairs_left _ _ If Kh),
            (composite_pairs_none _ _ Ik Ih).
    setoid_rewrite (composite_pairs_left _ _ If Ik). reflexivity.
  - (* k, h identities *)
    rewrite (composite_pairs_right _ _ Fk Ih), (composite_pairs_right _ _ If Ik),
            (composite_pairs_right _ _ If Kh). reflexivity.
  - (* k identity *)
    rewrite (composite_pairs_none _ _ Fk Ih), (composite_pairs_none _ _ If Kh).
    setoid_rewrite (composite_pairs_right _ _ If Ik).
    setoid_rewrite (composite_pairs_left _ _ Ik Ih). reflexivity.
  - (* h identity *)
    rewrite (composite_pairs_right _ _ Fk Ih), (composite_pairs_none _ _ If Ik),
            (composite_pairs_none _ _ If Kh).
    setoid_rewrite (composite_pairs_right _ _ Ik Ih). reflexivity.
  - (* no identities *)
    rewrite (composite_pairs_none _ _ Fk Ih), (composite_pairs_none _ _ If Kh).
    setoid_rewrite (composite_pairs_none _ _ If Ik).
    setoid_rewrite (composite_pairs_none _ _ Ik Ih). firstorder.
Qed.

(** Left identity on stored arrows: an identity arrow i on object A composed
    before any stored arrow f out of A gives f back. *)
Theorem graph_compose_left_identity_stored :
  forall g ii fi i f,
    graph_lookup_morphism g ii = Some i ->
    graph_lookup_morphism g fi = Some f ->
    morph_is_identity i = true ->
    morph_source i = morph_target i ->
    morph_target i = morph_source f ->
    exists g' r x,
      graph_compose_morphisms g ii fi = Some (g', r) /\
      graph_lookup_morphism g' r = Some x /\
      stored_arrow_equiv x f.
Proof.
  intros g ii fi i f Hi Hf Hid Hst Ht.
  destruct (graph_compose_stored g ii fi i f Hi Hf Ht) as [g' [C [L _]]].
  exists g', (pg_next_morph_id g), (composite_record i f).
  split; [exact C|]. split; [exact L|].
  unfold stored_arrow_equiv. simpl. rewrite Hid. simpl.
  split; [congruence|]. split; [reflexivity|]. split; [reflexivity|].
  intro Hfl. unfold compose_coupling. rewrite Hid, Hfl. simpl.
  apply nodup_pairs_equiv.
Qed.

(** Right identity on stored arrows: any stored arrow f into object A
    composed before an identity arrow i on A gives f back. *)
Theorem graph_compose_right_identity_stored :
  forall g fi ii f i,
    graph_lookup_morphism g fi = Some f ->
    graph_lookup_morphism g ii = Some i ->
    morph_is_identity i = true ->
    morph_source i = morph_target i ->
    morph_target f = morph_source i ->
    exists g' r x,
      graph_compose_morphisms g fi ii = Some (g', r) /\
      graph_lookup_morphism g' r = Some x /\
      stored_arrow_equiv x f.
Proof.
  intros g fi ii f i Hf Hi Hid Hst Ht.
  destruct (graph_compose_stored g fi ii f i Hf Hi Ht) as [g' [C [L _]]].
  exists g', (pg_next_morph_id g), (composite_record f i).
  split; [exact C|]. split; [exact L|].
  unfold stored_arrow_equiv. simpl. rewrite Hid, andb_true_r.
  split; [reflexivity|]. split; [congruence|]. split; [reflexivity|].
  intro Hfl. unfold compose_coupling. rewrite Hid, Hfl. simpl.
  apply nodup_pairs_equiv.
Qed.

(** ** Every stored identity arrow is canonical

    A flagged arrow goes from an object to itself and stores no pairs. MORPH_ID
    builds such arrows, COMPOSE of two of them builds another, and no other
    step sets the flag, so every reachable graph has only canonical identity
    arrows. With this invariant the premises of the identity laws above hold
    for every flagged arrow of a reachable state. *)

Definition identity_arrows_canonical (g : PartitionGraph) : Prop :=
  forall mid ms, In (mid, ms) (pg_morphisms g) ->
    morph_is_identity ms = true ->
    morph_source ms = morph_target ms /\ coupling_pairs (morph_coupling ms) = [].

Lemma identity_arrows_canonical_lookup :
  forall g mid ms,
    identity_arrows_canonical g ->
    graph_lookup_morphism g mid = Some ms ->
    morph_is_identity ms = true ->
    morph_source ms = morph_target ms /\ coupling_pairs (morph_coupling ms) = [].
Proof.
  intros g mid ms Hc Hl Hid. apply (Hc mid ms); [|exact Hid].
  apply graph_lookup_morphism_list_In. exact Hl.
Qed.

Lemma identity_arrows_canonical_sub :
  forall g g',
    (forall p, In p (pg_morphisms g') -> In p (pg_morphisms g)) ->
    identity_arrows_canonical g -> identity_arrows_canonical g'.
Proof. intros g g' Hsub Hc mid ms Hin. apply (Hc mid ms). exact (Hsub _ Hin). Qed.

Lemma identity_arrows_canonical_same :
  forall g g',
    pg_morphisms g' = pg_morphisms g ->
    identity_arrows_canonical g -> identity_arrows_canonical g'.
Proof.
  intros g g' E. apply identity_arrows_canonical_sub. intros p Hp. rewrite <- E. exact Hp.
Qed.

Lemma identity_arrows_canonical_add :
  forall g src dst c is_id,
    identity_arrows_canonical g ->
    (is_id = true -> src = dst /\ coupling_pairs c = []) ->
    identity_arrows_canonical (fst (graph_add_morphism g src dst c is_id)).
Proof.
  intros g src dst c is_id Hc Hnew mid ms Hin Hid.
  unfold graph_add_morphism in Hin. simpl in Hin.
  destruct Hin as [Heq | Hin].
  - injection Heq as _ Hms. subst ms. simpl in *.
    destruct (Hnew Hid) as [Hsd Hp]. split; [exact Hsd|].
    unfold normalize_coupling. simpl. rewrite Hp. reflexivity.
  - exact (Hc mid ms Hin Hid).
Qed.

Lemma graph_compose_preserves_identity_arrows_canonical :
  forall g m1 m2 g' r,
    identity_arrows_canonical g ->
    graph_compose_morphisms g m1 m2 = Some (g', r) ->
    identity_arrows_canonical g'.
Proof.
  intros g m1 m2 g' r Hc H.
  unfold graph_compose_morphisms in H.
  destruct (graph_lookup_morphism g m1) as [f|] eqn:Hf; [|discriminate].
  destruct (graph_lookup_morphism g m2) as [h|] eqn:Hh; [|discriminate].
  destruct (Nat.eqb (morph_target f) (morph_source h)) eqn:Ht; [|discriminate].
  injection H as Hg _. subst g'. apply identity_arrows_canonical_add; [exact Hc|].
  intro Hboth. apply andb_true_iff in Hboth. destruct Hboth as [If Ih].
  rewrite If, Ih. simpl. split; [|reflexivity].
  apply Nat.eqb_eq in Ht.
  destruct (identity_arrows_canonical_lookup g m1 f Hc Hf If) as [Ef _].
  destruct (identity_arrows_canonical_lookup g m2 h Hc Hh Ih) as [Eh _].
  congruence.
Qed.

Lemma graph_cascade_delete_morphisms_sub : forall g mid p,
  In p (pg_morphisms (graph_cascade_delete_morphisms g mid)) -> In p (pg_morphisms g).
Proof.
  intros g mid p Hp. unfold graph_cascade_delete_morphisms in Hp. simpl in Hp.
  apply filter_In in Hp. exact (proj1 Hp).
Qed.

Lemma graph_remove_or_keep_morphisms : forall g mid,
  pg_morphisms (match graph_remove g mid with Some (g', _) => g' | None => g end) =
  pg_morphisms g.
Proof.
  intros g mid. unfold graph_remove.
  destruct (graph_remove_modules (pg_modules g) mid) as [[? ?]|]; reflexivity.
Qed.

Lemma graph_hw_psplit_morphisms_sub : forall g mid p,
  In p (pg_morphisms (graph_hw_psplit g mid)) -> In p (pg_morphisms g).
Proof.
  intros g mid p Hp. unfold graph_hw_psplit in Hp.
  destruct (graph_add_module _ (psplit_left _) []) as [g2 i2] eqn:E2.
  destruct (graph_add_module g2 (psplit_right _) []) as [g3 i3] eqn:E3.
  assert (H3 : pg_morphisms g3 = pg_morphisms g2)
    by (unfold graph_add_module in E3; injection E3 as <- _; reflexivity).
  rewrite H3 in Hp.
  unfold graph_add_module in E2. injection E2 as <- _. simpl in Hp.
  rewrite graph_remove_or_keep_morphisms in Hp.
  exact (graph_cascade_delete_morphisms_sub g mid p Hp).
Qed.

Lemma graph_hw_pmerge_morphisms_sub : forall g m1 m2 p,
  In p (pg_morphisms (graph_hw_pmerge g m1 m2)) -> In p (pg_morphisms g).
Proof.
  intros g m1 m2 p Hp. unfold graph_hw_pmerge in Hp.
  destruct (graph_add_module _ _ []) as [g3 i3] eqn:E3.
  unfold graph_add_module in E3. injection E3 as <- _. simpl in Hp.
  rewrite !graph_remove_or_keep_morphisms in Hp.
  apply graph_cascade_delete_morphisms_sub in Hp.
  exact (graph_cascade_delete_morphisms_sub g m1 p Hp).
Qed.

Lemma graph_pnew_morphisms : forall g region,
  pg_morphisms (fst (graph_pnew g region)) = pg_morphisms g.
Proof.
  intros g region. unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)); reflexivity.
Qed.

Lemma graph_update_module_tensor_morphisms : forall g mid k v,
  pg_morphisms (graph_update_module_tensor g mid k v) = pg_morphisms g.
Proof.
  intros g mid k v. unfold graph_update_module_tensor.
  destruct (graph_lookup g mid); reflexivity.
Qed.

Lemma graph_delete_morphism_sub : forall g mid g' p,
  graph_delete_morphism g mid = Some g' ->
  In p (pg_morphisms g') -> In p (pg_morphisms g).
Proof.
  intros g mid g' p H Hp. unfold graph_delete_morphism in H.
  destruct (existsb _ _); [|discriminate].
  injection H as <-. simpl in Hp. apply filter_In in Hp. exact (proj1 Hp).
Qed.

Lemma graph_tensor_preserves_identity_arrows_canonical :
  forall g f_id g_id g' r,
    identity_arrows_canonical g ->
    graph_tensor_morphisms g f_id g_id = Some (g', r) ->
    identity_arrows_canonical g'.
Proof.
  intros g f_id g_id g' r Hc H.
  unfold graph_tensor_morphisms in H.
  destruct (graph_lookup_morphism g f_id) as [f|]; [|discriminate].
  destruct (graph_lookup_morphism g g_id) as [h|]; [|discriminate].
  destruct (graph_lookup g (morph_source f)); [|discriminate].
  destruct (graph_lookup g (morph_target f)); [|discriminate].
  destruct (graph_lookup g (morph_source h)); [|discriminate].
  destruct (graph_lookup g (morph_target h)); [|discriminate].
  destruct (_ && _); [|discriminate].
  destruct (graph_find_region g _); [|discriminate].
  destruct (graph_find_region g _); [|discriminate].
  injection H as <- _. apply identity_arrows_canonical_add; [exact Hc|].
  discriminate.
Qed.

Lemma graph_add_identity_preserves_identity_arrows_canonical :
  forall g mid g' r,
    identity_arrows_canonical g ->
    graph_add_identity g mid = Some (g', r) ->
    identity_arrows_canonical g'.
Proof.
  intros g mid g' r Hc H. unfold graph_add_identity in H.
  destruct (graph_lookup g mid); [|discriminate].
  injection H as <- _. apply identity_arrows_canonical_add; [exact Hc|].
  intros _. split; reflexivity.
Qed.

(** [vm_step_preserves_identity_arrows_canonical]: no step stores a flagged
    arrow that is not the identity of an object. *)
Theorem vm_step_preserves_identity_arrows_canonical : forall s instr s',
  vm_step s instr s' ->
  identity_arrows_canonical s.(vm_graph) -> identity_arrows_canonical s'.(vm_graph).
Proof.
  intros s instr s' Hstep Hc.
  inversion Hstep; subst; simpl; try exact Hc.
  all: try (match goal with
            | |- context [if ?b then _ else _] => destruct b; simpl; try exact Hc
            end).
  all: try (apply (identity_arrows_canonical_same (vm_graph s));
            [apply graph_pnew_morphisms | exact Hc]).
  all: try (apply (identity_arrows_canonical_sub (vm_graph s));
            [intros p Hp; exact (graph_hw_psplit_morphisms_sub _ _ p Hp) | exact Hc]).
  all: try (apply (identity_arrows_canonical_sub (vm_graph s));
            [intros p Hp; exact (graph_hw_pmerge_morphisms_sub _ _ _ p Hp) | exact Hc]).
  all: try (apply (identity_arrows_canonical_same (vm_graph s));
            [apply graph_update_module_tensor_morphisms | exact Hc]).
  all: try (match goal with
            | H : (?g', ?m) = graph_add_morphism ?g ?src ?dst ?c ?b
              |- identity_arrows_canonical ?g' =>
                change g' with (fst (g', m)); rewrite H;
                apply identity_arrows_canonical_add; [exact Hc | discriminate]
            end).
  all: try (match goal with
            | H : graph_compose_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (graph_compose_preserves_identity_arrows_canonical _ _ _ _ _ Hc H)
            | H : graph_add_identity _ _ = Some (?g', _) |- _ =>
                exact (graph_add_identity_preserves_identity_arrows_canonical _ _ _ _ Hc H)
            | H : graph_delete_morphism _ _ = Some ?g' |- _ =>
                exact (identity_arrows_canonical_sub _ _
                         (fun p Hp => graph_delete_morphism_sub _ _ _ p H Hp) Hc)
            | H : graph_tensor_morphisms _ _ _ = Some (?g', _) |- _ =>
                exact (graph_tensor_preserves_identity_arrows_canonical _ _ _ _ _ Hc H)
            end).
Qed.

Theorem vm_reachable_preserves_identity_arrows_canonical : forall s s',
  vm_reachable s s' ->
  identity_arrows_canonical s.(vm_graph) -> identity_arrows_canonical s'.(vm_graph).
Proof.
  intros s s' Hr. induction Hr as [s|s instr s1 s2 Hstep Hr IH]; intro Hc.
  - exact Hc.
  - apply IH. exact (vm_step_preserves_identity_arrows_canonical s instr s1 Hstep Hc).
Qed.

(** [vm_reachable_identity_arrows_canonical]: from a state whose graph has
    no morphisms (the initial state), every reachable state stores only
    canonical identity arrows. *)
Theorem vm_reachable_identity_arrows_canonical : forall s s',
  s.(vm_graph).(pg_morphisms) = [] ->
  vm_reachable s s' ->
  identity_arrows_canonical s'.(vm_graph).
Proof.
  intros s s' H0 Hr.
  apply (vm_reachable_preserves_identity_arrows_canonical s s' Hr).
  intros mid ms Hin. rewrite H0 in Hin. destruct Hin.
Qed.

(** What the certification policy actually says about morphism opcodes. *)

(** MORPH_ASSERT is the only cert-setter among the categorical instructions.
  Be careful here: the other morphism ops are not cert-setters, but that does
  NOT mean they are free. Their cost is still mu_delta. The point proved here
  is narrower: only MORPH_ASSERT is forced onto the positive-cost certification
  track. *)
Lemma morph_assert_is_cert_setter :
  forall morph_id prop cert cost,
    is_cert_setterb (instr_morph_assert morph_id prop cert cost) = true.
Proof. intros. reflexivity. Qed.

Lemma instr_morph_not_cert_setter :
  forall dst src dst_mod coupling_idx cost,
    is_cert_setterb (instr_morph dst src dst_mod coupling_idx cost) = false.
Proof. intros. reflexivity. Qed.

Lemma instr_compose_not_cert_setter :
  forall dst m1 m2 cost,
    is_cert_setterb (instr_compose dst m1 m2 cost) = false.
Proof. intros. reflexivity. Qed.

Lemma instr_morph_id_not_cert_setter :
  forall dst mid cost,
    is_cert_setterb (instr_morph_id dst mid cost) = false.
Proof. intros. reflexivity. Qed.

Lemma instr_morph_delete_not_cert_setter :
  forall morph_id cost,
    is_cert_setterb (instr_morph_delete morph_id cost) = false.
Proof. intros. reflexivity. Qed.

Lemma instr_morph_tensor_not_cert_setter :
  forall dst f g cost,
    is_cert_setterb (instr_morph_tensor dst f g cost) = false.
Proof. intros. reflexivity. Qed.

Lemma instr_morph_get_not_cert_setter :
  forall dst morph_id selector cost,
    is_cert_setterb (instr_morph_get dst morph_id selector cost) = false.
Proof. intros. reflexivity. Qed.

(** The cost equations for morphism instructions. *)

Lemma morph_cost_morph : forall dst src dst_mod cidx cost,
  instruction_cost (instr_morph dst src dst_mod cidx cost) = cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_compose : forall dst m1 m2 cost,
  instruction_cost (instr_compose dst m1 m2 cost) = cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_morph_id : forall dst mid cost,
  instruction_cost (instr_morph_id dst mid cost) = cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_morph_delete : forall morph_id cost,
  instruction_cost (instr_morph_delete morph_id cost) = cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_morph_assert : forall morph_id prop cert cost,
  instruction_cost (instr_morph_assert morph_id prop cert cost) = S cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_morph_tensor : forall dst f g cost,
  instruction_cost (instr_morph_tensor dst f g cost) = cost.
Proof. intros. reflexivity. Qed.

Lemma morph_cost_morph_get : forall dst morph_id sel cost,
  instruction_cost (instr_morph_get dst morph_id sel cost) = cost.
Proof. intros. reflexivity. Qed.

(** MORPH_ASSERT always costs something. *)

(** MORPH_ASSERT costs S cost ≥ 1 — it is a cert-setter under NoFI policy.
    This means morphism certification (MORPH_ASSERT) always charges at least 1
    unit of μ-cost, consistent with the NoFreeInsight principle. *)
Lemma morph_assert_cost_positive : forall morph_id prop cert cost,
  0 < instruction_cost (instr_morph_assert morph_id prop cert cost).
Proof. intros. simpl. lia. Qed.

(** For non-cert morphism ops, setting mu_delta = 0 really gives zero instruction cost. *)
Lemma morph_compose_cost_zero : forall dst m1 m2,
  instruction_cost (instr_compose dst m1 m2 0) = 0.
Proof. reflexivity. Qed.

(** Summary.

    The categorical extension clears the minimum bar the kernel needs:
    MORPH_ASSERT is the only morphism instruction that is forced into the
    cert-setter bucket, and it always costs at least 1. The other morphism
    opcodes keep their declared mu_delta cost model.

    That is the exact NoFreeInsight boundary proved here. I am not claiming that
    every non-cert morphism op is free. I am claiming that certified morphism
    assertions are not free. *)
Theorem categorical_extension_nofi_consistent :
  forall (morph_id cost : nat) (prop cert : string),
    is_cert_setterb (instr_morph_assert morph_id prop cert cost) = true /\
    0 < instruction_cost (instr_morph_assert morph_id prop cert cost).
Proof.
  intros. split.
  - apply morph_assert_is_cert_setter.
  - apply morph_assert_cost_positive.
Qed.
