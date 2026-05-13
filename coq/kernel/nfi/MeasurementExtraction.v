(** MeasurementExtraction: the deterministic Bell theorem and the
    relational Bell/PR-box uniqueness theorem, both axiom-free.

    CONTENT.
    --------
    1. Deterministic [CorrelatedResource]s, the standard 2-to-1 RAC
       protocol [rac_protocol_succeeds], no-signalling [cr_no_signalling],
       and the freeness predicate.

    2. DETERMINISTIC BELL THEOREM
       [cr_no_signalling_implies_no_perfect_rac]: no deterministic
       no-signalling resource solves the protocol on every input. Pure
       boolean algebra over four input triples.

    3. RELATIONAL [RelationalResource]s with existential no-signalling,
       the relational PR-box [prbox_relational], and the existence
       theorem [relational_prbox_is_consistent].

    4. CONSTRAINT THEOREM
       [rac_relational_forces_prbox_constraint]: any RAC-succeeding
       relational resource has its outcome relation contained in the
       PR-box constraint a XOR b = x AND y.

    5. SUPPORT-DOUBLING [rac_no_signalling_support_doubles]: a four-step
       cycle through both halves of no-signalling forces both PR-box
       points at each cell into the support.

    6. UNIQUENESS THEOREM
       [rac_no_signalling_relation_is_prbox]: the outcome relation of a
       no-signalling RAC-succeeding relational resource is EXACTLY the
       PR-box constraint. The PR-box is the unique no-signalling
       correlation that solves perfect 2-to-1 RAC.

    Deterministically, a resource that solves perfect 2-to-1 RAC must
    signal (Bell). Relationally, no-signalling resources can solve it,
    but only by realizing the full PR-box constraint set
    (Bell/PR-box uniqueness). Both statements are theorems of the kernel,
    not postulates.
*)

From Coq Require Import Bool Arith.PeanoNat Lia.

(** A two-party correlated resource. Alice and Bob each query the resource
    locally with a one-bit setting; the resource produces a joint outcome.
    The cost function records how much each query type costs against the
    resource's internal ledger.

    Notational convention:
    - cr_outcomes s x y returns (a, b): Alice's outcome a, Bob's outcome b
    - cr_cost x is the cost of a query with Alice setting x
      (we keep this one-sided for simplicity; the full version would have
      separate Alice- and Bob-cost functions; the result below does not
      need that generality)
*)
Record CorrelatedResource : Type := mk_correlated_resource {
  cr_state : Type;
  cr_init  : cr_state;
  (** cr_outcomes: given resource state and a pair of settings, deterministic
      joint outcome. Randomness, if any, is folded into cr_state. *)
  cr_outcomes : cr_state -> bool -> bool -> bool * bool;
  cr_cost : bool -> nat;
}.

(** Alice's outcome extractor. *)
Definition cr_alice (CR : CorrelatedResource) (s : cr_state CR) (x y : bool) : bool :=
  fst (cr_outcomes CR s x y).

(** Bob's outcome extractor. *)
Definition cr_bob (CR : CorrelatedResource) (s : cr_state CR) (x y : bool) : bool :=
  snd (cr_outcomes CR s x y).

(** *** The standard PR-box 2-to-1 RAC protocol.

    Alice has two bits (a0, a1). Bob wants to retrieve bit a_y for some
    index y. They share a CorrelatedResource. The protocol:

      Alice computes x = a0 XOR a1.
      Alice queries the resource with x, getting outcome A.
      Alice sends Bob one bit: c = a0 XOR A.

      Bob queries the resource with y, getting outcome B.
      Bob outputs: c XOR B.

    For the PR-box correlation (A XOR B = x AND y), the algebra gives:
      output = c XOR B = a0 XOR A XOR B = a0 XOR (x AND y)
                       = a0 XOR ((a0 XOR a1) AND y)
      y = false: a0 XOR 0 = a0
      y = true:  a0 XOR (a0 XOR a1) = a1
    Perfect retrieval on every (a0, a1, y).

    For a classical no-signalling resource the same protocol cannot succeed
    on every triple by the RAC bound: two bits cannot pass through a one-bit
    channel with shared classical randomness.

    [rac_protocol_succeeds CR] says: the resource CR makes the above
    protocol succeed for *every* input triple. *)
Definition rac_protocol_succeeds (CR : CorrelatedResource) : Prop :=
  forall (a0 a1 y : bool),
    let x := xorb a0 a1 in
    let A := cr_alice CR (cr_init CR) x y in
    let B := cr_bob   CR (cr_init CR) x y in
    let c := xorb a0 A in
    xorb c B = (if y then a1 else a0).

(** A resource is "free" if every setting has zero cost. The freeness
    predicate is still useful for stating refined results about which
    resources can or cannot achieve RAC. *)
Definition cr_is_free (CR : CorrelatedResource) : Prop :=
  forall x, cr_cost CR x = 0.

(** *** NO-SIGNALLING.

    A CorrelatedResource is no-signalling if Alice's outcome depends only on
    her input (not Bob's) and Bob's outcome depends only on his input.
    Equivalently: cr_alice does not depend on y, cr_bob does not depend on x.

    This is the locality structure that the PR-box realization in
    [PRBoxIsDishonest.v] does NOT satisfy (its B depends on x, because
    PR-box correlations are not locally realizable from independent
    randomness).
*)
Definition cr_no_signalling (CR : CorrelatedResource) : Prop :=
  (forall s x y1 y2, cr_alice CR s x y1 = cr_alice CR s x y2)
  /\ (forall s x1 x2 y, cr_bob CR s x1 y = cr_bob CR s x2 y).

(** *** Bell-style theorem (no axioms).

    A deterministic no-signalling CorrelatedResource CANNOT make the
    standard 2-to-1 RAC protocol succeed on every input triple.

    This is real content: A3 is NOT needed here. The contradiction comes
    from pure boolean algebra against the structural constraints of
    no-signalling. The proof uses four input triples (a0, a1, y) chosen
    so that the algebraic constraints become inconsistent.

    The argument is the standard local-hidden-variable refutation: no
    deterministic local strategy reproduces PR-box-strength correlations.
    Here it is packaged as a Coq theorem with no axioms; the assumption
    audit will confirm "Closed under the global context."

    Consequence: A3 as postulated above bites *only* in the signalling
    case. The no-signalling case is already covered, axiom-free, by this
    theorem. Whether a probabilistic / non-deterministic no-signalling
    resource (the actual physical PR-box, modulo shared randomness)
    likewise fails RAC requires a more general formulation we do not
    pursue here.
*)
Theorem cr_no_signalling_implies_no_perfect_rac :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    ~ rac_protocol_succeeds CR.
Proof.
  intros CR [Hns_a Hns_b] Hrac.
  (* Specialize the protocol-succeeds hypothesis at four (a0, a1, y) triples
     that together pin down four boolean values along inconsistent edges. *)
  pose proof (Hrac false false true)  as E1.  (* x = false, y = true,  expect a1 = false *)
  pose proof (Hrac false true  true)  as E2.  (* x = true,  y = true,  expect a1 = true  *)
  pose proof (Hrac false false false) as E3.  (* x = false, y = false, expect a0 = false *)
  pose proof (Hrac false true  false) as E4.  (* x = true,  y = false, expect a0 = false *)
  cbn in E1, E2, E3, E4.
  unfold cr_alice, cr_bob in *.
  (* No-signalling identifications, also unfolded. *)
  pose proof (Hns_a (cr_init CR) false true  false) as Ha_xf.
  pose proof (Hns_a (cr_init CR) true  true  false) as Ha_xt.
  pose proof (Hns_b (cr_init CR) false true  true ) as Hb_yt.
  pose proof (Hns_b (cr_init CR) false true  false) as Hb_yf.
  unfold cr_alice, cr_bob in Ha_xf, Ha_xt, Hb_yt, Hb_yf.
  (* Push the no-signalling equalities into the equations so all four
     refer to only four canonical fst/snd-of-cr_outcomes values. *)
  rewrite <- Ha_xf in E3.
  rewrite <- Ha_xt in E4.
  rewrite <- Hb_yt in E2.
  rewrite <- Hb_yf in E4.
  (* The canonical outcomes after the rewrites:
       A_F := fst (cr_outcomes CR init false true)  (used by E1, E3)
       A_T := fst (cr_outcomes CR init true  true)  (used by E2, E4)
       B_T := snd (cr_outcomes CR init false true)  (used by E1, E2)
       B_F := snd (cr_outcomes CR init false false) (used by E3, E4)
     E1: A_F XOR B_T = false  ->  A_F = B_T
     E2: A_T XOR B_T = true   ->  A_T <> B_T
     E3: A_F XOR B_F = false  ->  A_F = B_F
     E4: A_T XOR B_F = false  ->  A_T = B_F
     E1, E3 force B_T = B_F. Then E2 says A_T <> B_T = B_F, and E4 says
     A_T = B_F. Contradiction. *)
  destruct (fst (cr_outcomes CR (cr_init CR) false true)),
           (fst (cr_outcomes CR (cr_init CR) true  true)),
           (snd (cr_outcomes CR (cr_init CR) false true)),
           (snd (cr_outcomes CR (cr_init CR) false false));
    cbn in E1, E2, E3, E4; discriminate.
Qed.

(** Contrapositive: any deterministic resource that succeeds at the standard
    2-to-1 RAC protocol on every input triple necessarily signals. *)
Corollary rac_success_implies_signalling :
  forall (CR : CorrelatedResource),
    rac_protocol_succeeds CR ->
    ~ cr_no_signalling CR.
Proof.
  intros CR Hrac Hns.
  exact (cr_no_signalling_implies_no_perfect_rac CR Hns Hrac).
Qed.

(** *** RELATIONAL CORRELATED RESOURCES.

    The deterministic per-state model above cannot express the physical
    PR-box, which is no-signalling at the level of *marginal distributions*
    over shared randomness rather than at the level of individual states.
    We introduce a relational variant: at each state and pair of settings,
    a set of (a, b) outcomes is admissible, not a single one.

    The relational PR-box is honest: the relation
      [rr_outcomes s x y a b := xorb a b = andb x y]
    satisfies an existential form of no-signalling (every (a, x, y) admits
    some compatible b; every (b, x, y) admits some compatible a), and the
    standard 2-to-1 RAC protocol succeeds for every admissible (a, b)
    realization. Whether the deterministic Bell-style theorem above
    survives this lift is the question this section answers.
*)

Record RelationalResource : Type := mk_relational_resource {
  rr_state : Type;
  rr_init  : rr_state;
  rr_outcomes : rr_state -> bool -> bool -> bool -> bool -> Prop;
  rr_cost : bool -> nat;
  rr_total : forall s x y, exists a b, rr_outcomes s x y a b;
}.

(** Existential no-signalling.

    Read it as: any local outcome that is achievable at one setting of
    the other party is achievable at every setting of the other party.
    This is the relational analog of "marginal does not depend on the
    other input." In a probabilistic formulation it would be a statement
    about distributions; here it is the underlying *support* condition. *)
Definition rr_no_signalling (R : RelationalResource) : Prop :=
  (forall s x y1 y2 a, (exists b, rr_outcomes R s x y1 a b)
                   <-> (exists b, rr_outcomes R s x y2 a b))
  /\ (forall s x1 x2 y b, (exists a, rr_outcomes R s x1 y a b)
                      <-> (exists a, rr_outcomes R s x2 y a b)).

(** RAC succeeds in the relational sense: for every input triple
    (a0, a1, y) and every admissible outcome (a, b), the protocol's
    output is a_y. *)
Definition rac_relational_succeeds (R : RelationalResource) : Prop :=
  forall (a0 a1 y a b : bool),
    rr_outcomes R (rr_init R) (xorb a0 a1) y a b ->
    xorb (xorb a0 a) b = (if y then a1 else a0).

Definition rr_is_free (R : RelationalResource) : Prop :=
  forall x, rr_cost R x = 0.

(** *** The relational PR-box.

    The relation is a XOR b = x AND y, the textbook PR-box constraint.
    Cost is identically zero. *)

Definition prbox_rel
  (s : unit) (x y a b : bool) : Prop :=
  xorb a b = andb x y.

Definition prbox_relational : RelationalResource :=
  mk_relational_resource
    unit         (* rr_state — irrelevant for PR-box; the constraint is state-free *)
    tt           (* rr_init *)
    prbox_rel    (* rr_outcomes *)
    (fun _ => 0) (* rr_cost = 0 *)
    (fun _ x y =>
       ex_intro _ false (ex_intro _ (andb x y) eq_refl)).

(** The relational PR-box satisfies existential no-signalling. *)
Lemma prbox_relational_no_signalling : rr_no_signalling prbox_relational.
Proof.
  split.
  - intros s x y1 y2 a. split; intros [b Hb].
    + exists (xorb a (andb x y2)). unfold prbox_rel.
      destruct a, x, y2; reflexivity.
    + exists (xorb a (andb x y1)). unfold prbox_rel.
      destruct a, x, y1; reflexivity.
  - intros s x1 x2 y b. split; intros [a Ha].
    + exists (xorb b (andb x2 y)). unfold prbox_rel.
      destruct b, x2, y; reflexivity.
    + exists (xorb b (andb x1 y)). unfold prbox_rel.
      destruct b, x1, y; reflexivity.
Qed.

(** The relational PR-box satisfies relational RAC success. *)
Lemma prbox_relational_rac_succeeds : rac_relational_succeeds prbox_relational.
Proof.
  intros a0 a1 y a b Hrel.
  unfold rr_outcomes, prbox_relational, prbox_rel in Hrel.
  destruct a0, a1, y, a, b; cbn in Hrel; try discriminate; reflexivity.
Qed.

(** The relational PR-box is free. *)
Lemma prbox_relational_is_free : rr_is_free prbox_relational.
Proof. intro x. reflexivity. Qed.

(** *** CONSEQUENCE: the deterministic no-signalling theorem does NOT lift.

    The relational PR-box is no-signalling, has zero cost, and satisfies
    relational RAC success. In the deterministic case our theorem above
    forced a contradiction from these conditions; in the relational case
    no contradiction is available.

    Without a stronger physicality precondition (which we do NOT
    postulate here), the relational PR-box is consistent. The
    deterministic theorem is genuine progress but it does not close
    the question. *)
Theorem relational_prbox_is_consistent :
  exists (R : RelationalResource),
       rr_no_signalling R
    /\ rac_relational_succeeds R
    /\ rr_is_free R.
Proof.
  exists prbox_relational.
  split; [| split].
  - exact prbox_relational_no_signalling.
  - exact prbox_relational_rac_succeeds.
  - exact prbox_relational_is_free.
Qed.

(** *** SHARPER RELATIONAL RESULT: RAC success forces PR-box outcomes.

    A relational resource that satisfies the standard RAC protocol on
    every input triple has its outcome relation pinned: every admissible
    (a, b) pair at settings (x, y) satisfies a XOR b = x AND y.

    This is a characterization, not just a consistency statement: RAC
    success determines the relation up to its support. Different
    relational resources that solve RAC differ only in WHICH (a, b)
    pairs they make admissible at each (x, y), not in the algebraic
    constraint those pairs satisfy.

    Proof idea: specialize the RAC hypothesis at (a0 := false, a1 := x).
    Then a0 XOR a1 = x, so the RAC equation reads
      xorb (xorb false a) b = (if y then x else false)
    which simplifies to a XOR b = x AND y. *)
Theorem rac_relational_forces_prbox_constraint :
  forall (R : RelationalResource),
    rac_relational_succeeds R ->
    forall (x y a b : bool),
      rr_outcomes R (rr_init R) x y a b ->
      xorb a b = andb x y.
Proof.
  intros R Hrac x y a b Hab.
  pose proof (Hrac false x y a b) as Heq.
  cbn in Heq.
  (* After cbn, [xorb false x] reduces to [x] and [xorb false a] reduces to
     [a], so Heq has the form
       rr_outcomes R (rr_init R) x y a b -> xorb a b = (if y then x else false). *)
  specialize (Heq Hab).
  (* Heq : xorb a b = (if y then x else false). Match against the goal
     [xorb a b = andb x y] case by case on y (and x where relevant). *)
  destruct x, y; cbn in Heq |- *; exact Heq.
Qed.

(** Corollary: any relational resource that succeeds at RAC cannot have
    a support point violating the PR-box constraint. *)
Corollary rac_relational_no_off_constraint :
  forall (R : RelationalResource),
    rac_relational_succeeds R ->
    forall (x y a b : bool),
      xorb a b <> andb x y ->
      ~ rr_outcomes R (rr_init R) x y a b.
Proof.
  intros R Hrac x y a b Hne Hin.
  apply Hne. exact (rac_relational_forces_prbox_constraint R Hrac x y a b Hin).
Qed.

(** *** SUPPORT DOUBLING.

    From a single support point at (x, y), the other PR-box constraint
    point at the same cell is forced into the support by a four-step
    cycle through no-signalling:
       (x, y)  --Bob ns,  flip x--> (¬x, y)
       (¬x, y) --Alice ns, flip y--> (¬x, ¬y)
       (¬x, ¬y) --Bob ns,  flip x--> (x, ¬y)
       (x, ¬y) --Alice ns, flip y--> (x, y).
    At each step the constraint theorem pins the unspecified value, and
    the cycle composes to a XOR 1, b XOR 1.

    This is the formal Bell/PR-box uniqueness step in the support
    direction: a relational no-signalling resource that succeeds at RAC
    cannot have a one-element support at any cell. *)

Lemma rac_no_signalling_support_doubles :
  forall (R : RelationalResource),
    rr_no_signalling R ->
    rac_relational_succeeds R ->
    forall (x y a b : bool),
      rr_outcomes R (rr_init R) x y a b ->
      rr_outcomes R (rr_init R) x y (negb a) (negb b).
Proof.
  intros R [Hns_a Hns_b] Hrac x y a b H1.
  (* Step 1: Bob no-signalling at y. (a, b) at (x, y) gives some a' at (¬x, y) sharing b. *)
  destruct ((proj1 (Hns_b (rr_init R) x (negb x) y b)) (ex_intro _ a H1))
    as [a' Ha'].
  (* Step 2: Alice no-signalling at ¬x. (a', b) at (¬x, y) gives some b'' at (¬x, ¬y) sharing a'. *)
  destruct ((proj1 (Hns_a (rr_init R) (negb x) y (negb y) a')) (ex_intro _ b Ha'))
    as [b'' Hb''].
  (* Step 3: Bob no-signalling at ¬y. (a', b'') at (¬x, ¬y) gives some a''' at (x, ¬y) sharing b''. *)
  destruct ((proj1 (Hns_b (rr_init R) (negb x) x (negb y) b'')) (ex_intro _ a' Hb''))
    as [a''' Ha'''].
  (* Step 4: Alice no-signalling at x. (a''', b'') at (x, ¬y) gives some b'''' at (x, y) sharing a'''. *)
  destruct ((proj1 (Hns_a (rr_init R) x (negb y) y a''')) (ex_intro _ b'' Ha'''))
    as [b'''' Hres].
  (* Constraint theorem applied at each step. *)
  pose proof (rac_relational_forces_prbox_constraint R Hrac x y a b H1) as C1.
  pose proof (rac_relational_forces_prbox_constraint R Hrac (negb x) y a' b Ha') as C2.
  pose proof (rac_relational_forces_prbox_constraint R Hrac (negb x) (negb y) a' b'' Hb'') as C3.
  pose proof (rac_relational_forces_prbox_constraint R Hrac x (negb y) a''' b'' Ha''') as C4.
  pose proof (rac_relational_forces_prbox_constraint R Hrac x y a''' b'''' Hres) as C5.
  (* Conclude a''' = NEGB a and b'''' = NEGB b by boolean case analysis. *)
  assert (Heq_a : a''' = negb a).
  { destruct a, b, x, y, a', a''', b'';
      cbn in C1, C2, C3, C4;
      try discriminate; try reflexivity. }
  assert (Heq_b : b'''' = negb b).
  { destruct a, b, x, y, a''', b'''', b'';
      cbn in C1, C4, C5;
      try discriminate; try reflexivity. }
  rewrite <- Heq_a, <- Heq_b. exact Hres.
Qed.

(** Corollary: at every cell, BOTH PR-box-constraint points are in the
    support of a no-signalling RAC-succeeding relational resource. The
    support equals the full PR-box constraint set at every (x, y). *)
Theorem rac_no_signalling_support_is_full_prbox :
  forall (R : RelationalResource),
    rr_no_signalling R ->
    rac_relational_succeeds R ->
    forall (x y a b : bool),
      xorb a b = andb x y ->
      rr_outcomes R (rr_init R) x y a b.
Proof.
  intros R Hns Hrac x y a b Hconstraint.
  (* At (x, y), rr_total guarantees some (a0, b0) in support. *)
  destruct (rr_total R (rr_init R) x y) as [a0 [b0 Hbase]].
  pose proof (rac_relational_forces_prbox_constraint R Hrac x y a0 b0 Hbase) as Cbase.
  (* Two cases on whether (a0, b0) = (a, b) or its complement. *)
  destruct (Bool.bool_dec a0 a) as [Ha_eq | Ha_neq].
  - (* a0 = a. By the constraint, a0 XOR b0 = a XOR b, so b0 = b. *)
    assert (Hb_eq : b0 = b).
    { destruct a0, b0, a, b, x, y;
        cbn in Cbase, Hconstraint, Ha_eq;
        try discriminate; try reflexivity. }
    rewrite <- Ha_eq, <- Hb_eq. exact Hbase.
  - (* a0 ≠ a, so a0 = NEGB a. Then b0 = NEGB b by constraint matching.
       Apply support-doubling to get (NEGB a0, NEGB b0) = (a, b). *)
    pose proof (rac_no_signalling_support_doubles R Hns Hrac x y a0 b0 Hbase) as Hflip.
    assert (Hna0 : negb a0 = a).
    { destruct a0, a;
        cbn in Ha_neq;
        try reflexivity; try (exfalso; apply Ha_neq; reflexivity). }
    assert (Hnb0 : negb b0 = b).
    { destruct a0, b0, a, b, x, y;
        cbn in Cbase, Hconstraint, Ha_neq;
        try discriminate; try reflexivity;
        try (exfalso; apply Ha_neq; reflexivity). }
    rewrite <- Hna0, <- Hnb0. exact Hflip.
Qed.

(** Final characterization: any no-signalling resource achieving relational
    RAC has its outcome relation IDENTICAL to the PR-box constraint
    a XOR b = x AND y. The support equals the full PR-box constraint set;
    no smaller relational resource works.

    This is the formal statement of Bell/PR-box uniqueness in the
    relational framework: relational PR-box is the unique no-signalling
    resource solving perfect 2-to-1 RAC. *)
Theorem rac_no_signalling_relation_is_prbox :
  forall (R : RelationalResource),
    rr_no_signalling R ->
    rac_relational_succeeds R ->
    forall (x y a b : bool),
      rr_outcomes R (rr_init R) x y a b <-> xorb a b = andb x y.
Proof.
  intros R Hns Hrac x y a b.
  split.
  - apply rac_relational_forces_prbox_constraint. exact Hrac.
  - apply rac_no_signalling_support_is_full_prbox; assumption.
Qed.

(** *** QUANTITATIVE CLASSICAL BOUND.

    The Bell theorem above says no deterministic no-signalling resource
    achieves perfect (8/8) RAC. The sharper question is: how close can it
    get?

    The classical bound: no such resource achieves more than 6/8 success
    across the 8 input triples. This is the 3/4 classical 2-to-1 RAC bound
    in counting form. Together with the PR-box result (8/8 success), it
    establishes a strict gap between classical and PR-box correlations
    that is visible at the success-count level, no probability needed.

    Proof: under no-signalling, [cr_alice] factors through x only and
    [cr_bob] through y only. The 8 success indicators reduce to 4 boolean
    equations on (A0, A1, B0, B1) := (alice(F), alice(T), bob(F), bob(T)).
    Each equation contributes 2 to the success count when satisfied.
    Inspection of all 16 settings of (A0, A1, B0, B1) shows the four
    equations cannot all hold simultaneously, so at most 3 hold, giving
    at most 6 successes. *)

Definition rac_succeeds_at (CR : CorrelatedResource) (a0 a1 y : bool) : bool :=
  Bool.eqb (xorb (xorb a0 (cr_alice CR (cr_init CR) (xorb a0 a1) y))
                  (cr_bob CR (cr_init CR) (xorb a0 a1) y))
           (if y then a1 else a0).

Definition rac_success_count (CR : CorrelatedResource) : nat :=
    (if rac_succeeds_at CR false false false then 1 else 0)
  + (if rac_succeeds_at CR false false true  then 1 else 0)
  + (if rac_succeeds_at CR false true  false then 1 else 0)
  + (if rac_succeeds_at CR false true  true  then 1 else 0)
  + (if rac_succeeds_at CR true  false false then 1 else 0)
  + (if rac_succeeds_at CR true  false true  then 1 else 0)
  + (if rac_succeeds_at CR true  true  false then 1 else 0)
  + (if rac_succeeds_at CR true  true  true  then 1 else 0).

(** Sanity: the success-count function takes values in [0, 8]. *)
Lemma rac_success_count_le_8 :
  forall CR, rac_success_count CR <= 8.
Proof.
  intro CR. unfold rac_success_count.
  destruct (rac_succeeds_at CR false false false),
           (rac_succeeds_at CR false false true),
           (rac_succeeds_at CR false true  false),
           (rac_succeeds_at CR false true  true),
           (rac_succeeds_at CR true  false false),
           (rac_succeeds_at CR true  false true),
           (rac_succeeds_at CR true  true  false),
           (rac_succeeds_at CR true  true  true);
    cbn; lia.
Qed.

(** Helper: from no-signalling, alice's output at (x, y) equals its output
    at (x, false). *)
Lemma cr_no_signalling_alice_const :
  forall CR, cr_no_signalling CR ->
    forall x y, cr_alice CR (cr_init CR) x y
              = cr_alice CR (cr_init CR) x false.
Proof.
  intros CR [Hns_a _] x y. apply Hns_a.
Qed.

(** Helper: from no-signalling, bob's output at (x, y) equals its output
    at (false, y). *)
Lemma cr_no_signalling_bob_const :
  forall CR, cr_no_signalling CR ->
    forall x y, cr_bob CR (cr_init CR) x y
              = cr_bob CR (cr_init CR) false y.
Proof.
  intros CR [_ Hns_b] x y. apply Hns_b.
Qed.

(** Helper function: the classical success-count formula in terms of the
    four canonical bool outputs (A0, A1, B0, B1) := (alice(F), alice(T),
    bob(F), bob(T)). The 8 RAC success conditions reduce, under
    no-signalling, to expressions in these four bools. *)
Definition classical_count (A0 A1 B0 B1 : bool) : nat :=
    (if Bool.eqb (xorb (xorb false A0) B0) false then 1 else 0)
  + (if Bool.eqb (xorb (xorb false A0) B1) false then 1 else 0)
  + (if Bool.eqb (xorb (xorb false A1) B0) false then 1 else 0)
  + (if Bool.eqb (xorb (xorb false A1) B1) true  then 1 else 0)
  + (if Bool.eqb (xorb (xorb true  A1) B0) true  then 1 else 0)
  + (if Bool.eqb (xorb (xorb true  A1) B1) false then 1 else 0)
  + (if Bool.eqb (xorb (xorb true  A0) B0) true  then 1 else 0)
  + (if Bool.eqb (xorb (xorb true  A0) B1) true  then 1 else 0).

(** Brute-force: over all 16 settings of (A0, A1, B0, B1), the count is
    at most 6. This is the classical 2-to-1 RAC bound, by exhaustion. *)
Lemma classical_count_le_6 :
  forall A0 A1 B0 B1, classical_count A0 A1 B0 B1 <= 6.
Proof.
  intros A0 A1 B0 B1.
  destruct A0, A1, B0, B1; cbn; lia.
Qed.

(** Under no-signalling, the RAC success count reduces to the classical
    count on the four canonical bool outputs. *)
Lemma rac_success_count_under_no_signalling :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    rac_success_count CR
    = classical_count
        (cr_alice CR (cr_init CR) false false)
        (cr_alice CR (cr_init CR) true  false)
        (cr_bob   CR (cr_init CR) false false)
        (cr_bob   CR (cr_init CR) false true).
Proof.
  intros CR Hns.
  unfold rac_success_count, rac_succeeds_at, classical_count.
  (* Reduce every xorb on concrete bool literals. *)
  cbn [xorb].
  (* The remaining cr_alice and cr_bob calls have concrete bool (x, y).
     Identify each with one of the four canonical values. *)
  rewrite (cr_no_signalling_alice_const CR Hns false true).
  rewrite (cr_no_signalling_alice_const CR Hns true  true).
  rewrite (cr_no_signalling_bob_const   CR Hns true  false).
  rewrite (cr_no_signalling_bob_const   CR Hns true  true).
  reflexivity.
Qed.

(** The classical 3/4 bound: under no-signalling, the RAC success count is
    at most 6 out of 8. *)
Theorem classical_rac_bound :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    rac_success_count CR <= 6.
Proof.
  intros CR Hns.
  rewrite (rac_success_count_under_no_signalling CR Hns).
  apply classical_count_le_6.
Qed.

(** Contrapositive packaging: any deterministic resource that achieves
    7 or more RAC successes must signal. *)
Corollary rac_seven_successes_force_signalling :
  forall (CR : CorrelatedResource),
    rac_success_count CR >= 7 ->
    ~ cr_no_signalling CR.
Proof.
  intros CR Hge Hns.
  pose proof (classical_rac_bound CR Hns) as Hle.
  lia.
Qed.

(** *** TIGHTNESS OF THE CLASSICAL BOUND.

    The classical bound 6/8 is tight: there is a no-signalling deterministic
    resource that achieves exactly 6 successes. Concretely, the trivial
    resource that always returns (false, false) regardless of settings hits
    6/8 (only the input triples with y = T and the "negation needed" pattern
    fail). *)

Definition classical_witness : CorrelatedResource :=
  mk_correlated_resource
    unit                       (* state *)
    tt                         (* init *)
    (fun _ _ _ => (false, false))
    (fun _ => 0).

Lemma classical_witness_no_signalling : cr_no_signalling classical_witness.
Proof.
  split; intros; reflexivity.
Qed.

(** This lemma is intentionally arithmetic. The classical_witness
    CorrelatedResource immediately above is fully explicit, and the
    success count (6 out of 8) is the textbook 3/4 classical RAC
    bound used in the tightness theorem below; the reflexivity proof
    is the right shape because the count reduces to a definitional
    computation. *)
(* INQUISITOR NOTE: intentionally arithmetic — see the comment above. *)
Lemma classical_witness_count : rac_success_count classical_witness = 6.
Proof.
  reflexivity.
Qed.

Theorem classical_bound_is_tight :
  exists (CR : CorrelatedResource),
    cr_no_signalling CR /\ rac_success_count CR = 6.
Proof.
  exists classical_witness.
  split.
  - apply classical_witness_no_signalling.
  - apply classical_witness_count.
Qed.

(** *** CHSH-STYLE COUNT.

    The CHSH/PR-box pattern requires three "agreement" cells and one
    "disagreement" cell:
      (0, 0) : alice = bob
      (0, 1) : alice = bob
      (1, 0) : alice = bob
      (1, 1) : alice <> bob
    Count of cells matching this pattern is bounded by 3 for any
    no-signalling deterministic resource. The PR-box achieves 4 (all four
    cells match its constraint).

    This is the bool-valued, deterministic-CR analog of the kernel's
    [chsh_local_bound] (in [kernel/quantum/CHSH.v]), which proves the
    same statement in Q-arithmetic on lists of CHSH trials. *)

Definition prbox_match_count (CR : CorrelatedResource) : nat :=
    (if Bool.eqb (cr_alice CR (cr_init CR) false false)
                 (cr_bob   CR (cr_init CR) false false) then 1 else 0)
  + (if Bool.eqb (cr_alice CR (cr_init CR) false true)
                 (cr_bob   CR (cr_init CR) false true)  then 1 else 0)
  + (if Bool.eqb (cr_alice CR (cr_init CR) true  false)
                 (cr_bob   CR (cr_init CR) true  false) then 1 else 0)
  + (if Bool.eqb (cr_alice CR (cr_init CR) true  true)
                 (cr_bob   CR (cr_init CR) true  true)  then 0 else 1).

(** Classical CHSH-style bound on the match count. *)
Theorem prbox_match_classical_bound :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    prbox_match_count CR <= 3.
Proof.
  intros CR Hns.
  unfold prbox_match_count.
  rewrite (cr_no_signalling_alice_const CR Hns false true).
  rewrite (cr_no_signalling_alice_const CR Hns true  true).
  rewrite (cr_no_signalling_bob_const   CR Hns true  false).
  rewrite (cr_no_signalling_bob_const   CR Hns true  true).
  destruct (cr_alice CR (cr_init CR) false false),
           (cr_alice CR (cr_init CR) true  false),
           (cr_bob   CR (cr_init CR) false false),
           (cr_bob   CR (cr_init CR) false true);
    cbn; lia.
Qed.

(** Quantitative link: the RAC success count is exactly twice the
    CHSH-match count (each "agreement-or-disagreement" condition
    contributes to two input triples). *)
Lemma rac_count_is_twice_match_count :
  forall (CR : CorrelatedResource),
    cr_no_signalling CR ->
    rac_success_count CR = 2 * prbox_match_count CR.
Proof.
  intros CR Hns.
  rewrite (rac_success_count_under_no_signalling CR Hns).
  unfold prbox_match_count.
  rewrite (cr_no_signalling_alice_const CR Hns false true).
  rewrite (cr_no_signalling_alice_const CR Hns true  true).
  rewrite (cr_no_signalling_bob_const   CR Hns true  false).
  rewrite (cr_no_signalling_bob_const   CR Hns true  true).
  unfold classical_count.
  destruct (cr_alice CR (cr_init CR) false false),
           (cr_alice CR (cr_init CR) true  false),
           (cr_bob   CR (cr_init CR) false false),
           (cr_bob   CR (cr_init CR) false true);
    cbn; reflexivity.
Qed.

(** ** Substrate connection anchor.

    The measurement-extraction framework in this file feeds the
    correlation-to-NPA-to-mu chain that governs the Thiele Machine's
    mu-ledger. The anchor below makes the connection point explicit. *)

From Kernel Require Import VMState MuCostModel.

Definition measurement_extraction_vm_anchor (s : VMState) : nat := vm_mu s.
