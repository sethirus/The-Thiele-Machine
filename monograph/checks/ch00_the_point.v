(* SCOPE NOTE: standalone proof scope.  A check written beside the book: it
   uses only the Coq standard library and does not import the foundation
   chain.  The definitions it needs from the kernel (the order, the record,
   the toll, the member predicate ax_thiele, the merge theorem and the latch)
   are restated below word for word from coq/kernel/foundation/AxCore.v,
   AxMerge.v and AxThiele.v, so "Thiele machine" here is the kernel's. *)
(** ThePoint: what a point is, held against the book's Thiele machine.

    Two pictures are worked out here.  They differ first in whether the
    inside of a point is the same place as the point, and with that in what
    the lone point is and in whether an edge records which way it went.

    The point, with one place inside.  Inside the point there is one place,
    and what is there is the same as nothing, so all there is to the point
    is its latch.  The latch is open, and then the point is both, or it is
    closed one of two ways: as that which is the point, or as that which
    isn't.  Closing it makes one distinction true, either one, and closing
    it again changes nothing; going in, to the same place, closes it, and
    going in again changes nothing.  That is the whole of the point's own
    machine: three ways to be and two moves, with no pointland drawn in it.
    It is a Thiele machine.  Its moves merge: from open and from closed,
    closing lands on closed, so two arrows meet inside the point.  With
    three ways to be there is no fresh paper, so by the kernel's merge
    theorem every move that settles something merges.  That is the book's
    chapter two, and it holds here once one place is taken as the point's
    state, as it holds for every finite machine read yes or no.  Both the
    three ways to be and its being a Thiele machine hold by construction.
    Price the merge, which is Landauer's principle on the logic and is
    assumed, and the toll follows; here the toll is exactly the price of the
    merge.

    Kept edge by edge.  The other picture keeps every edge apart, so that a
    point drawn inside a point is a new place.  An edge has two sides, that
    which is the point and that which isn't, and each side is pointland
    again.  Going into nothing is still nothing, so a move aimed past what is
    drawn lands on the nothing it reaches; no move is refused.  A move draws
    an edge around what is at a place, and what was there goes on one side
    of it or the other.  Kept this way pointland never merges: no move sends
    two pointlands to one, and no finite list holds them all.  Read by the
    number of edges and priced one a move, it is a Thiele machine with no
    point in it.  Any machine whose every move adds exactly one to a count
    is one the same way, and so is a clock.  The book makes the same point
    about the toll ("A clock passes"); read by its count, a clock meets the
    ceiling too.  The toll forces at least one on every move and the ceiling
    at most one, because every move raises the count exactly once.  Kept
    this way the toll is chosen: nothing merges, so merge pricing is met at
    price zero and the toll fails.  The kernel's latch, two states and no
    inside, is the smallest Thiele machine, and the kernel rules out a
    machine whose reading never rises.

    Where the two pictures meet.  Ask of a pointland kept edge by edge only
    whether an edge is there, and every move of it is the point's closing
    move.  Ask a clock only whether it has ticked, and it is the same
    machine.  So the one-place picture does not by itself tell a point from
    a clock, and nothing proved here does: read by its count, pointland kept
    edge by edge never merges either.  What tells them apart is a choice,
    declared below: for the point, one place is line three of the chain
    taken as its state.  At one place, empty pointland is the open latch and
    the lone point is already closed, and since an edge kept edge by edge
    records no way, its moves only ever close the latch as that which is the
    point; the other closed way has no counterpart there.  Priced by move
    names, as on page one, no Thiele machine read only yes or no meets the
    book's ceiling, so in the one-place picture the price is a floor, not an
    exact count.

    The forks, worked out.

    One of two ways.  Open, the point is both; closing it, which at one place
    is the point connecting to itself, makes it one of two ways.  The two
    closed ways are different states, and once the point closes, which one
    it is never changes, so closed as that which is the point is a record of
    its own, and so is its mirror.  The
    laws treat the two ways alike: swapping that which is the point and that
    which isn't, everywhere at once, turns the point's machine into itself,
    run for run.  So which way it closed is a fact, and the laws cannot
    tell which name goes on which way.  Read only closed or
    not, the point is the kernel's latch, which is all the picture kept edge
    by edge sees at one place, since its edges record no way.

    Where identity comes from.  Line six says the latch keeps what it makes
    true, so whatever says which is the point has to be a record that never
    falls.  The latch is one: the edge, and at one place the way it closed.
    Whether the sides differ is not.  Read by whether the outermost point's
    sides differ, or by whether any point's sides differ, a pointland kept
    edge by edge can fall, because a move can make two sides the same again.

    Connecting to itself.  At one place, going in closes the point, and
    going in again changes nothing.  Kept edge by edge, going into a drawn
    point puts an edge inside it, and every endless edge is something.  What
    connecting to itself does not give is a difference between what is on
    the sides, and that difference is not what says which is the point.

    In the picture kept edge by edge.

    The lone point is its own mirror: swap its sides and nothing changes.
    Its two sides can only differ when another edge sits on one of them.  In
    empty pointland the edge's two ways of going around give the same point.
    Among the points that are there, the one that can fail to be decided is
    the outermost, and only when its two sides are the same.

    Being told apart does not last, and neither does being decided at the
    top.  A later move can make a point's two sides the same again, while
    the count of edges never falls.

    One move in decides two points.  Before it the lone point is not decided
    and nothing is inside it.  After it the outer point is decided by what
    is inside it and the inner one by the edge around it.  However far in
    the run goes, the innermost point is the lone point again; once the run
    has gone in at all, it is decided only by the edge around it.

    Going up and going in both mean drawing around what is there, so that
    what was there ends up inside the new point.  Done that way, they give
    the same pointland exactly when nothing is on the other side, so always
    for a point alone, and which one it did is recorded nowhere.  The
    comparison uses the moves of the whole; the point alone has no move up.

    Mirroring every edge turns moves into moves and runs into runs, keeps the
    count, keeps which points are decided at every place, and keeps whether
    the outermost point is told apart.  It keeps a run's total when the price
    list prices a move and its mirror the same.  The point alone does pick a
    side: inside means the side that is the point.

    In finite pointland the only thing that is its own inside is nothing.
    With no end allowed, an edge with itself inside is its own inside too,
    but being its own inside does not tell a point apart: an edge with itself
    on both sides is its own inside and is not told apart.  The endless
    point, itself inside and nothing on its other side, is told apart by
    that nothing.  The run inward from the lone point draws it one level per
    move and never finishes.

    Chosen, not shown.  One place inside the point is lines two and three of
    the chain, taken as the point's state; so in that picture going in has
    no place of its own to go, and is closing the latch, and going in is
    the point connecting to itself.  That choice, not a
    result, is what tells the point from a clock.  Pricing merges is Landauer's
    principle on the logic, assumed.  What says which is the point is taken
    to be what the latch keeps; line six makes that a record that never
    falls.  In the picture kept edge by edge: the
    toll is chosen; the reading is the number of edges, and prices go on move
    names as on page one, and with the height as the reading the toll and the
    ceiling cannot both hold; an edge has no way of its own, since going
    around fills the new side with nothing, which is why both ways are one in
    empty pointland, and an edge that recorded its way would make the lone
    point one of two ways; decided means there is a point at the place, and
    an edge around it holds it or its own two sides differ; a draw keeps
    everything it goes around, which is why nothing merges; going into
    nothing is still nothing, and with refused moves instead no price list
    meets both the toll and the ceiling; places keep the sides apart by
    name.  Kept edge by edge the edge has no orientation, so seen at one
    place every move closes the latch the same way.  On endless pointlands,
    equal means written the same way, so two writings of one endless shape
    cannot be shown equal.

    Not modeled.  Infinite as a size, and filling it.  Not side by side, in
    the picture kept edge by edge: there an edge holds its two sides as two
    parts.  Zero dimensions, and going up in dimensions; going up here means
    drawing around everything.  The membrane, the edge and the latch as one
    thing, in the picture kept edge by edge: there the edge is part of a
    pointland and going around is a move.  A one-way edge between its
    sides: kept edge by edge, the mirror shows the edge has no direction
    between its sides.  Which the whole really is or isn't.  What picks which
    way the latch closes: the move names it.  The edge as pointland too.

    Every result about the point is printed at the end and is closed under
    the global context.  (def) marks a result that holds by the definitions, by
    computation, or by a short case check; (kernel) marks one that restates
    or applies a kernel theorem.

    Results.

      closing_again_changes_nothing (def),
      either_distinction_can_be_made_true (def),
      three_ways_to_be (def), the_point_is_a_thiele_machine (def),
      the_latch_merges_inside_the_point (def),
      the_merge_inside_the_point_is_forced (kernel),
      a_distinction_costs_because_a_merge_does (kernel),
      the_toll_inside_the_point_is_the_merge_price (def)
                                the point with one place inside: closing a
                                closed latch changes nothing; either
                                distinction can be made true; three ways to
                                be; a Thiele machine; its moves merge; a move
                                that settles it must merge (the kernel's
                                ax_growth_exit_merges); pricing merges gives
                                the toll (the kernel's
                                ax_a2_from_merge_price); there the toll is the
                                merge price.
      the_way_it_closed_is_a_record (def),
      the_two_closed_ways_are_mirror_images (def),
      every_run_of_the_point_has_a_mirror_run,
      the_point_read_closed_or_not_is_the_latch (def)
                                the two closed ways are different, and read
                                by whether it closed as that which is the
                                point it is a Thiele machine; swapping the
                                two ways everywhere turns the machine into
                                itself, run for run;
                                read only closed or not, the point is the
                                kernel's latch.
      neither_difference_reading_is_a_record (def),
      the_edge_is_a_record (def)
                                read by whether the outermost point's sides
                                differ, or whether any point's sides differ,
                                a pointland can fall; read by whether an edge
                                is there, it never falls.
      connecting_to_itself_closes_the_point (def),
      going_in_puts_an_edge_inside (def), every_endless_edge_is_something (def)
                                going in closes the point at one place; kept
                                edge by edge it puts an edge inside a drawn
                                point; an endless edge is never nothing.
      kept_pointland_at_one_place_is_the_point (def),
      a_clock_at_one_place_is_the_point_too (def),
      read_by_its_count_a_clock_never_merges (kernel)
                                asked only whether an edge is there, every
                                move of pointland kept edge by edge closes
                                the point's latch; asked only whether it has
                                ticked, so does a clock; read by its count, a
                                clock never merges and at price zero its toll
                                fails (the kernel's history_escape).
      inside_the_lone_point_is_nothing (def), the_lone_point_is_one_edge (def),
      nothing_but_edges (def)
                                kept edge by edge: the lone point holds
                                nothing on either side and is one edge; a
                                pointland with no edge is nothing.
      only_nothing_is_its_own_inside
                                in finite pointland, only nothing.
      both_ways_are_one_in_nothing (def), the_two_ways_differ_on_something (def)
                                the edge's two ways of going around, in
                                nothing and around anything else.
      the_lone_point_is_its_own_mirror (def),
      not_told_apart_iff_its_own_mirror (def),
      told_apart_needs_another_edge (def)
                                a point is not told apart exactly when its
                                sides can be swapped with nothing changing,
                                which needs no other edge.
      alone_it_is_not_decided (def), only_a_mirror_on_top_is_not_decided
                                the lone point is not decided; among points
                                that are there, only an outermost point with
                                the same on both sides is not.
      telling_apart_does_not_last (def)
                                a move can undo a point's being told apart.
      one_move_in_decides_two (def), the_innermost_is_the_lone_point,
      the_innermost_is_held_only_by_the_edge_around_it,
      every_point_of_a_tower_is_decided
                                before and after one move in; the innermost
                                point of every tower, and how it is decided;
                                every point of a tower of two or more.
      up_is_in_iff (def), for_a_point_alone_up_is_in,
      going_up_decides_everything_below (def)
                                drawn around what is there, up and in give
                                the same pointland exactly when nothing is on
                                the other side, so always for a point alone;
                                going up around anything but nothing decides
                                every point in it.
      counter_is_thiele, counter_toll_iff (def), counter_priced_exactly
                                any machine whose every move adds one to a
                                count: a Thiele machine; the toll holds
                                exactly when every move costs at least one;
                                toll and ceiling hold exactly when every move
                                costs one.
      whole_is_thiele, alone_is_thiele, the_toll_here_is_every_move_costing (def),
      a_distinction_costs_exactly_one
                                pointland kept edge by edge is such a
                                counter.
      a_clock_is_a_thiele_machine_too, a_clock_is_priced_the_same_way
                                so is a clock.
      merge_pricing_does_not_force_the_toll (kernel)
                                kept edge by edge, at price zero nothing that
                                merges goes unpriced, and the toll fails (the
                                kernel's history_escape, for pointland).
      a_latch_with_no_inside_is_a_thiele_machine (kernel),
      one_way_to_be_is_not_a_thiele_machine (kernel)
                                the kernel's latch_is_thiele restated; the
                                kernel's flat_is_not_thiele applied to one
                                single-state system (the general fact is the
                                kernel's no_one_state_member).
      no_yes_no_member_is_priced_exactly (kernel),
      the_box_cannot_price_exactly, the_height_cannot_price_exactly,
      refusing_moves_cannot_price_exactly
                                no Thiele machine read only yes or no, priced
                                by move names, meets the ceiling (from the
                                kernel's two_point_member_raising_move); read
                                as "is there a point?", or by height, or with
                                refused moves, no price list meets the toll
                                and the ceiling.
      the_inside_is_the_whole (def), going_in_forever
                                a run inside is a run of the whole on the
                                inside; n moves in give a tower of n + 1.
      nothing_merges, pointland_is_endless (kernel)
                                kept edge by edge, no move sends two
                                pointlands to one, so by the kernel's
                                ax_growth_exit_merges no finite list holds
                                them all.  A roundabout way to say pointland
                                kept this way has no end.
      seen_at_one_place_every_move_is_the_latch_move,
      merged_at_one_place_kept_apart_edge_by_edge
                                asked only whether there is a point, every
                                move is the kernel latch's move; no and yes
                                land on one while the pointlands under them
                                stay two.
      the_laws_do_not_pick_a_side, every_run_has_a_mirror_run,
      the_mirror_keeps_what_is_told_apart, the_mirror_keeps_what_is_decided,
      the_point_alone_picks_a_side (def)
                                mirroring every edge turns moves into moves
                                and runs into runs; it keeps a run's total
                                when the price list prices a move and its
                                mirror the same; it keeps whether the
                                outermost point is told apart, and what is
                                decided at every place; the point alone has a
                                move no move of its own mirrors.
      its_own_inside_iff, the_endless_point_is_its_own_inside (def),
      the_endless_point_is_not_nothing (def),
      being_its_own_inside_does_not_tell_apart (def),
      the_endless_point_is_told_apart_by_its_other_side (def),
      the_tower_is_the_endless_point_cut_off,
      the_run_inward_draws_the_endless_point
                                the endless point and what being one's own
                                inside does and does not give. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

(** * The kernel's definitions, restated word for word *)

(** * Orders given by a Boolean test *)

Record BPre (A : Type) : Type := {
  bp_leb : A -> A -> bool;
  bp_refl : forall x, bp_leb x x = true;
  bp_trans : forall x y z, bp_leb x y = true -> bp_leb y z = true ->
    bp_leb x z = true
}.

Definition bp_le {A} (P : BPre A) (x y : A) : Prop := bp_leb A P x y = true.

Lemma bp_le_refl : forall {A} (P : BPre A) x, bp_le P x x.
Proof. intros A [leb Hrefl Htrans] x. exact (Hrefl x). Qed.

Lemma bp_le_trans : forall {A} (P : BPre A) x y z,
  bp_le P x y -> bp_le P y z -> bp_le P x z.
Proof. intros A [leb Hrefl Htrans] x y z. exact (Htrans x y z). Qed.

(** Antisymmetry turns a preorder into a partial order.  It is a separate
    hypothesis because most of the toll does not use it. *)
Definition bp_antisym {A} (P : BPre A) : Prop :=
  forall x y, bp_le P x y -> bp_le P y x -> x = y.

(** The two-point order false < true. *)
Definition two_pre : BPre bool.
Proof.
  refine {| bp_leb := implb |}.
  - intros []; reflexivity.
  - intros [] [] []; simpl; auto.
Defined.

Lemma two_le : forall x y, bp_le two_pre x y <-> (x = true -> y = true).
Proof.
  intros [] []; unfold bp_le; simpl; split; intro H; auto; try discriminate;
    try (apply H; reflexivity).
Qed.

Lemma two_antisym : bp_antisym two_pre.
Proof.
  intros x y H1 H2. unfold bp_le in *.
  destruct x, y; simpl in *; try reflexivity; discriminate.
Qed.

(** The natural numbers as an infinite chain. *)
Definition nat_pre : BPre nat.
Proof.
  refine {| bp_leb := Nat.leb |}.
  - intro x. apply Nat.leb_refl.
  - intros x y z. rewrite !Nat.leb_le. apply Nat.le_trans.
Defined.

Lemma nat_pre_le : forall x y, bp_le nat_pre x y <-> x <= y.
Proof. intros x y. unfold bp_le. simpl. apply Nat.leb_le. Qed.

(** The discrete order on a type with Boolean equality: every point is
    comparable only with itself. *)
Definition disc_pre {A} (eqb : A -> A -> bool)
    (eqb_refl : forall x, eqb x x = true)
    (eqb_trans : forall x y z, eqb x y = true -> eqb y z = true -> eqb x z = true)
    : BPre A :=
  {| bp_leb := eqb; bp_refl := eqb_refl; bp_trans := eqb_trans |}.

(** * Axis systems *)

(** The fields of a certification system without its toll field (the toll
    is [ax_a2] below), with the one-bit reading replaced by a position in
    the order P.  The member predicate over these is [ax_thiele] in
    AxThiele.v. *)
Record AxSys (A : Type) (P : BPre A) : Type := mk_axsys {
  ax_state : Type;
  ax_instr : Type;
  ax_step : ax_state -> ax_instr -> ax_state;
  ax_cost : ax_instr -> nat;
  ax_rec : ax_state -> A
}.

Section Axis.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Fixpoint ax_run (tr : list (ax_instr A P X)) (s : ax_state A P X) : ax_state A P X :=
  match tr with
  | [] => s
  | i :: rest => ax_run rest (ax_step A P X s i)
  end.

Fixpoint ax_total (tr : list (ax_instr A P X)) : nat :=
  match tr with
  | [] => 0
  | i :: rest => ax_cost A P X i + ax_total rest
  end.

(** A step leaves the down-set of the current record. *)
Definition ax_exits (s : ax_state A P X) (i : ax_instr A P X) : Prop :=
  ~ bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

(** The toll: a step that leaves the down-set costs at least 1. *)
Definition ax_a2 : Prop :=
  forall s i, ax_exits s i -> ax_cost A P X i >= 1.

(** The floor: any run that ends outside the down-set of where it started
    costs at least 1. *)
Definition ax_floor : Prop :=
  forall tr s, ~ bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s) ->
    ax_total tr >= 1.

Lemma ax_run_app : forall l1 l2 s, ax_run (l1 ++ l2) s = ax_run l2 (ax_run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma ax_total_app : forall l1 l2, ax_total (l1 ++ l2) = ax_total l1 + ax_total l2.
Proof. induction l1; intros; simpl; [auto | rewrite IHl1; lia]. Qed.

(** The floor is exactly the toll, over any preorder. *)
Theorem ax_floor_iff_a2 : ax_floor <-> ax_a2.
Proof.
  split.
  - intros Hf s i Hex. specialize (Hf [i] s). simpl in Hf.
    assert (H : ax_total [i] >= 1) by (apply Hf; exact Hex).
    simpl in H. lia.
  - intros Ha tr. induction tr as [| i rest IH]; intros s Hnot.
    + simpl in Hnot. exfalso. apply Hnot. apply bp_le_refl.
    + simpl in *. destruct (bp_leb A P (ax_rec A P X (ax_step A P X s i))
                              (ax_rec A P X s)) eqn:Hle.
      * assert (Hn : ~ bp_le P (ax_rec A P X (ax_run rest (ax_step A P X s i)))
                                (ax_rec A P X (ax_step A P X s i))).
        { intro H. apply Hnot. eapply bp_le_trans; [exact H | exact Hle]. }
        specialize (IH _ Hn). lia.
      * assert (Hex : ax_exits s i) by (unfold ax_exits, bp_le; rewrite Hle; discriminate).
        specialize (Ha s i Hex). lia.
Qed.

(** The number of steps along a run that leave the down-set. *)
Fixpoint ax_exit_count (tr : list (ax_instr A P X)) (s : ax_state A P X) : nat :=
  match tr with
  | [] => 0
  | i :: rest =>
      (if bp_leb A P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s)
       then 0 else 1) + ax_exit_count rest (ax_step A P X s i)
  end.

(** The cost of a run is at least the number of its exits. *)
Theorem ax_cost_ge_exits : ax_a2 -> forall tr s, ax_total tr >= ax_exit_count tr s.
Proof.
  intros Ha tr. induction tr as [| i rest IH]; intro s; simpl; [lia |].
  specialize (IH (ax_step A P X s i)).
  destruct (bp_leb A P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s)) eqn:Hle.
  - lia.
  - assert (Hex : ax_exits s i) by (unfold ax_exits, bp_le; rewrite Hle; discriminate).
    specialize (Ha s i Hex). lia.
Qed.

(** On a growing record, leaving the down-set is a strict rise. *)
Definition ax_grows : Prop :=
  forall s i, bp_le P (ax_rec A P X s) (ax_rec A P X (ax_step A P X s i)).

Definition ax_rises (s : ax_state A P X) (i : ax_instr A P X) : Prop :=
  bp_le P (ax_rec A P X s) (ax_rec A P X (ax_step A P X s i)) /\
  ~ bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

Theorem ax_exit_is_strict_rise : ax_grows ->
  forall s i, ax_exits s i <-> ax_rises s i.
Proof.
  intros Hg s i. unfold ax_rises. split.
  - intro H. split; [apply Hg | exact H].
  - intros [_ H]. exact H.
Qed.

End Axis.

Arguments ax_run {A P X}.
Arguments ax_total {A P X}.
Arguments ax_exits {A P X}.
Arguments ax_a2 {A P X}.
Arguments ax_floor {A P X}.
Arguments ax_exit_count {A P X}.
Arguments ax_grows {A P X}.
Arguments ax_rises {A P X}.
Arguments ax_floor_iff_a2 {A P} X.
Arguments ax_cost_ge_exits {A P X} _ _ _.
Arguments ax_exit_is_strict_rise {A P X} _ _ _.


Lemma ax_NoDup_map_inj : forall {X Y : Type} (f : X -> Y) (l : list X),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros X Y f l. induction l as [| x l IH]; intros Hinj Hnd; simpl; [constructor |].
  inversion Hnd as [| ? ? Hnotin Hl]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin as [y [Hy Hyl]].
    assert (x = y) by (apply Hinj; [left; reflexivity | right; exact Hyl | symmetry; exact Hy]).
    subst y. exact (Hnotin Hyl).
  - apply IH; [| exact Hl]. intros a b Ha Hb. apply Hinj; right; assumption.
Qed.

Section Merge.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Local Notation S := (ax_state A P X).
Local Notation I := (ax_instr A P X).
Local Notation step := (ax_step A P X).
Local Notation rc := (ax_rec A P X).
Local Notation cost := (ax_cost A P X).

Definition ax_finite (all : list S) : Prop := NoDup all /\ forall s, In s all.

Definition ax_step_injective (i : I) : Prop :=
  forall a b, step a i = step b i -> a = b.

(** The states at or above the point a. *)
Definition ax_up (all : list S) (a : A) : list S :=
  filter (fun t => bp_leb A P a (rc t)) all.

Lemma ax_up_spec : forall all a, ax_finite all ->
  forall t, In t (ax_up all a) <-> bp_le P a (rc t).
Proof.
  intros all a [_ Hall] t. unfold ax_up. rewrite filter_In. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply Hall | exact H].
Qed.

Lemma ax_up_nodup : forall all a, ax_finite all -> NoDup (ax_up all a).
Proof. intros all a [Hnd _]. apply NoDup_filter. exact Hnd. Qed.

(** A move that leaves the down-set of the record merges two states, or
    takes some state out of the up-set of the threshold it crossed. *)
Theorem ax_exit_merges_or_revokes :
  forall all s i, ax_finite all -> ax_exits (X := X) s i ->
    ~ ax_step_injective i \/
    exists t, bp_le P (rc (step s i)) (rc t) /\
              ~ bp_le P (rc (step s i)) (rc (step t i)).
Proof.
  intros all s i Hfin Hex.
  set (a := rc (step s i)).
  set (T := ax_up all a).
  destruct (existsb (fun t => negb (bp_leb A P a (rc (step t i)))) T) eqn:E.
  - right. apply existsb_exists in E as [t [Ht Hneg]]. exists t. split.
    + apply (ax_up_spec all a Hfin). exact Ht.
    + intro H. unfold bp_le in H. rewrite H in Hneg. discriminate.
  - left. intro Hinj.
    assert (Hnorev : forall t, In t T -> bp_le P a (rc (step t i))).
    { intros t Ht. unfold bp_le.
      destruct (bp_leb A P a (rc (step t i))) eqn:Hb; [reflexivity |]. exfalso.
      assert (Hex' : existsb (fun t => negb (bp_leb A P a (rc (step t i)))) T = true).
      { apply existsb_exists. exists t. split; [exact Ht | rewrite Hb; reflexivity]. }
      congruence. }
    assert (Hs : ~ In s T).
    { intro H. apply (ax_up_spec all a Hfin) in H. exact (Hex H). }
    assert (HndL : NoDup (s :: T)).
    { constructor; [exact Hs | apply ax_up_nodup; exact Hfin]. }
    assert (Hndm : NoDup (map (fun t => step t i) (s :: T))).
    { apply ax_NoDup_map_inj; [| exact HndL].
      intros x y _ _ H. exact (Hinj x y H). }
    assert (Hincl : incl (map (fun t => step t i) (s :: T)) T).
    { intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. destruct Hx as [<- | Hx].
      - apply (ax_up_spec all a Hfin). apply bp_le_refl.
      - apply (ax_up_spec all a Hfin). apply Hnorev. exact Hx. }
    pose proof (NoDup_incl_length Hndm Hincl) as Hlen.
    rewrite map_length in Hlen. simpl in Hlen. lia.
Qed.

(** With growth there is nothing to revoke, so the move merges. *)
Theorem ax_growth_exit_merges :
  forall all s i, ax_finite all -> ax_grows (X := X) -> ax_exits (X := X) s i ->
    ~ ax_step_injective i.
Proof.
  intros all s i Hfin Hg Hex.
  destruct (ax_exit_merges_or_revokes all s i Hfin Hex) as [H | [t [Ht Hnot]]];
    [exact H |].
  exfalso. apply Hnot. eapply bp_le_trans; [exact Ht | apply Hg].
Qed.

(** Landauer on the logic: a move that merges two states costs at least 1. *)
Definition ax_merging_priced : Prop :=
  forall i, ~ ax_step_injective i -> cost i >= 1.

(** The axis toll is a consequence of finiteness, growth and merge pricing. *)
Theorem ax_a2_from_merge_price :
  forall all, ax_finite all -> ax_grows (X := X) -> ax_merging_priced ->
    ax_a2 (X := X).
Proof.
  intros all Hfin Hg Hp s i Hex. apply Hp. eapply ax_growth_exit_merges; eauto.
Qed.

(** Merge pricing asks for more than the toll needs: the toll is exactly
    that every move which leaves the down-set somewhere, and merges, is
    priced. *)
End Merge.

Arguments ax_finite {A P} X.
Arguments ax_step_injective {A P} X _.
Arguments ax_merging_priced {A P} X.
Arguments ax_up {A P} X.
Arguments ax_exit_merges_or_revokes {A P X} _ _ _ _ _.
Arguments ax_growth_exit_merges {A P X} _ _ _ _ _ _.
Arguments ax_a2_from_merge_price {A P X} _ _ _ _.

(** * The member *)

Section Member.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable starts : ax_state A P X -> Prop.

(** A reading no move carries out of its down-set. *)
Definition ax_flat : Prop :=
  forall s i, bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

(** From some designated start, some run carries the reading out of its
    down-set. *)
Definition ax_distinction : Prop :=
  exists s tr, starts s /\
    ~ bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s).

(** The toll, permanence, and a distinction some run makes. *)
Definition ax_thiele : Prop :=
  ax_a2 (X := X) /\ ax_grows (X := X) /\ ax_distinction.

(** The toll asks nothing of a flat reading. *)
Theorem flat_obeys_toll : ax_flat -> ax_a2 (X := X).
Proof. intros Hf s i Hex. exfalso. exact (Hex (Hf s i)). Qed.

Lemma ax_flat_run : ax_flat ->
  forall tr s, bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s).
Proof.
  intros Hf tr. induction tr as [| i rest IH]; intro s; simpl.
  - apply bp_le_refl.
  - eapply bp_le_trans; [apply IH | apply Hf].
Qed.

(** No run of a flat reading leaves the down-set of its start. *)
Theorem flat_has_no_distinction : ax_flat -> ~ ax_distinction.
Proof. intros Hf [s [tr [_ Hnot]]]. exact (Hnot (ax_flat_run Hf tr s)). Qed.

(** Flat readings are outside the class, whatever the starts. *)
Theorem flat_is_not_thiele : ax_flat -> ~ ax_thiele.
Proof. intros Hf [_ [_ Hd]]. exact (flat_has_no_distinction Hf Hd). Qed.

Lemma ax_total_pos_has_priced : forall tr,
  ax_total (X := X) tr >= 1 -> exists i, In i tr /\ ax_cost A P X i >= 1.
Proof.
  induction tr as [| i rest IH]; simpl; intro H; [lia |].
  destruct (Nat.eq_dec (ax_cost A P X i) 0) as [Hz | Hnz].
  - rewrite Hz in H. simpl in H.
    destruct (IH H) as [j [Hj Hc]]. exists j. split; [right; exact Hj | exact Hc].
  - exists i. split; [left; reflexivity | lia].
Qed.

(** Every member has a move that costs. *)
Theorem thiele_has_a_priced_move : ax_thiele -> exists i, ax_cost A P X i >= 1.
Proof.
  intros [Ha [_ [s [tr [_ Hnot]]]]].
  destruct (ax_total_pos_has_priced tr (proj2 (ax_floor_iff_a2 X) Ha tr s Hnot))
    as [i [_ Hi]].
  exists i. exact Hi.
Qed.

(** Every member has the floor: a run that leaves the down-set of its
    start costs at least 1. *)
Theorem thiele_floor : ax_thiele -> ax_floor (X := X).
Proof. intros [Ha _]. exact (proj2 (ax_floor_iff_a2 X) Ha). Qed.

End Member.

Arguments ax_flat {A P} X.
Arguments ax_distinction {A P} X starts.
Arguments ax_thiele {A P} X starts.

(** * Members over the two-point order *)

Section TwoPoint.

Variable X : AxSys bool two_pre.
Variable starts : ax_state bool two_pre X -> Prop.

Lemma two_not_le : forall a b, ~ bp_le two_pre a b -> a = true /\ b = false.
Proof.
  intros [] [] H; try (split; reflexivity); exfalso; apply H; unfold bp_le; reflexivity.
Qed.

Lemma two_point_run_crosses : forall tr s,
  ax_rec bool two_pre X s = false ->
  ax_rec bool two_pre X (ax_run tr s) = true ->
  exists i t, In i tr /\ ax_rec bool two_pre X t = false /\
    ax_rec bool two_pre X (ax_step bool two_pre X t i) = true.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in H1.
  - rewrite H0 in H1. discriminate.
  - destruct (ax_rec bool two_pre X (ax_step bool two_pre X s i)) eqn:E.
    + exists i, s. split; [left; reflexivity | split; [exact H0 | exact E]].
    + destruct (IH _ E H1) as [j [t [Hj Ht]]].
      exists j, t. split; [right; exact Hj | exact Ht].
Qed.

(** Over the two-point order a member has a move that raises the reading
    from some no-state, and that move, like every move, keeps every
    yes-state at yes. *)
Theorem two_point_member_raising_move : ax_thiele X starts ->
  exists i,
    (exists s, ax_rec bool two_pre X s = false /\
               ax_rec bool two_pre X (ax_step bool two_pre X s i) = true) /\
    (forall s, ax_rec bool two_pre X s = true ->
               ax_rec bool two_pre X (ax_step bool two_pre X s i) = true).
Proof.
  intros [_ [Hg [s [tr [_ Hnot]]]]].
  destruct (two_not_le _ _ Hnot) as [H1 H0].
  destruct (two_point_run_crosses tr s H0 H1) as [i [t [_ Hit]]].
  exists i. split; [exists t; exact Hit |].
  intros u Hu. exact (proj1 (two_le _ _) (Hg u i) Hu).
Qed.

End TwoPoint.

(** * The smallest machine *)

(** Two states, no and yes; one move that sends both to yes at price 1;
    the reading is the state.  This is [stamp_sys] of AxMerge with its
    move priced. *)
Definition latch_sys : AxSys bool two_pre :=
  mk_axsys bool two_pre bool unit (fun _ _ => true) (fun _ => 1) (fun b => b).

(** The latch is a member, started at no. *)
Theorem latch_is_thiele : ax_thiele latch_sys (fun b => b = false).
Proof.
  unfold ax_thiele. repeat split.
  - intros s i _. simpl. lia.
  - intros s i. destruct s; unfold bp_le; simpl; reflexivity.
  - exists false, [tt]. split; [reflexivity |]. unfold bp_le. simpl. discriminate.
Qed.

(** The latch's one move sends both states to one: it is not injective. *)

(** * The point *)

(** * Any counter *)

(** Any state with a move that adds one to a count. *)
Section Counter.

Variables (St I : Type) (stp : St -> I -> St) (r : St -> nat).
Hypothesis up_one : forall s i, r (stp s i) = S (r s).

Definition counter (c : I -> nat) : AxSys nat nat_pre := mk_axsys nat nat_pre St I stp c r.

Lemma counter_exits : forall c s i, ax_exits (X := counter c) s i.
Proof.
  intros c s i. unfold ax_exits. rewrite nat_pre_le.
  change (~ r (stp s i) <= r s). rewrite up_one. lia.
Qed.

Lemma counter_grows : forall c, ax_grows (X := counter c).
Proof.
  intros c s i. apply nat_pre_le. change (r s <= r (stp s i)). rewrite up_one. lia.
Qed.

Lemma counter_counts : forall c tr s, ax_exit_count (X := counter c) tr s = length tr.
Proof.
  intro c. induction tr as [| i tr IH]; intro s; [reflexivity |].
  cbn [ax_exit_count length]. rewrite IH.
  destruct (bp_leb _ _ _ _) eqn:E; [| lia].
  exfalso. change (bp_le nat_pre (r (stp s i)) (r s)) in E.
  rewrite nat_pre_le, up_one in E. lia.
Qed.

Theorem counter_is_thiele : forall (s0 : St) (i0 : I),
  ax_thiele (counter (fun _ => 1)) (fun s => s = s0).
Proof.
  intros s0 i0. split; [| split].
  - intros s i _. simpl. lia.
  - apply counter_grows.
  - exists s0, [i0]. split; [reflexivity |]. rewrite nat_pre_le.
    change (~ r (stp s0 i0) <= r s0). rewrite up_one. lia.
Qed.

Theorem counter_toll_iff : forall (s0 : St) c,
  ax_a2 (X := counter c) <-> forall i, c i >= 1.
Proof.
  intros s0 c. split.
  - intros H i. exact (H s0 i (counter_exits c s0 i)).
  - intros H s i _. exact (H i).
Qed.

Theorem counter_priced_exactly : forall (s0 : St) c,
  ax_a2 (X := counter c) /\
  (forall tr s, ax_total (X := counter c) tr <= ax_exit_count (X := counter c) tr s)
  <-> forall i, c i = 1.
Proof.
  intros s0 c. split.
  - intros [Ha Hc] i. pose proof (proj1 (counter_toll_iff s0 c) Ha i) as H1.
    specialize (Hc [i] s0). rewrite counter_counts in Hc. simpl in Hc. lia.
  - intro H. split.
    + apply (proj2 (counter_toll_iff s0 c)). intro i. rewrite H. lia.
    + intros tr s. rewrite counter_counts. clear s.
      induction tr as [| i tr IH]; [simpl; lia |].
      change (c i + ax_total (X := counter c) tr <= S (length tr)). rewrite H. lia.
Qed.

End Counter.

(** A clock: a number, and a tick that adds one. *)
Definition clock : AxSys nat nat_pre := counter nat unit (fun n _ => S n) (fun n => n) (fun _ => 1).

Theorem a_clock_is_a_thiele_machine_too : ax_thiele clock (fun n => n = 0).
Proof. exact (counter_is_thiele nat unit (fun n _ => S n) (fun n => n) (fun _ _ => eq_refl) 0 tt). Qed.

Theorem a_clock_is_priced_the_same_way : forall c,
  ax_a2 (X := counter nat unit (fun n _ => S n) (fun n => n) c) /\
  (forall tr s, ax_total (X := counter nat unit (fun n _ => S n) (fun n => n) c) tr <=
                ax_exit_count (X := counter nat unit (fun n _ => S n) (fun n => n) c) tr s)
  <-> forall i, c i = 1.
Proof. exact (counter_priced_exactly nat unit (fun n _ => S n) (fun n => n) (fun _ _ => eq_refl) 0). Qed.

(** The kernel's latch: not drawn or drawn, one move, no inside. *)
Theorem a_latch_with_no_inside_is_a_thiele_machine : ax_thiele latch_sys (fun b => b = false).
Proof. exact latch_is_thiele. Qed.

(** One way to be, and the only move stays put. *)
Definition one_way : AxSys nat nat_pre :=
  mk_axsys nat nat_pre unit unit (fun _ _ => tt) (fun _ => 1) (fun _ => 0).

Theorem one_way_to_be_is_not_a_thiele_machine : forall starts, ~ ax_thiele one_way starts.
Proof.
  intro starts. apply flat_is_not_thiele. intros s i. apply nat_pre_le. simpl. lia.
Qed.

(** * Pointland *)

(** Nothing, or an edge with that which is the point on one side and that
    which isn't on the other.  Each side is pointland again. *)
Inductive pl : Type :=
  | nothing : pl
  | edge : pl -> pl -> pl.

Lemma pl_eq_dec : forall x y : pl, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition that_is (s : pl) : pl := match s with nothing => nothing | edge a _ => a end.
Definition that_isnt (s : pl) : pl := match s with nothing => nothing | edge _ b => b end.

(** The lone point: one edge, in nothing. *)
Definition the_point : pl := edge nothing nothing.

Fixpoint edges (s : pl) : nat :=
  match s with
  | nothing => 0
  | edge a b => S (edges a + edges b)
  end.

Theorem inside_the_lone_point_is_nothing :
  that_is the_point = nothing /\ that_isnt the_point = nothing.
Proof. split; reflexivity. Qed.

Theorem the_lone_point_is_one_edge : the_point <> nothing /\ edges the_point = 1.
Proof. split; [discriminate | reflexivity]. Qed.

Theorem nothing_but_edges : forall s, edges s = 0 -> s = nothing.
Proof. intros [| a b] H; [reflexivity | discriminate]. Qed.

Theorem only_nothing_is_its_own_inside : forall s, that_is s = s -> s = nothing.
Proof.
  intros [| a b] H; [reflexivity |]. simpl in H.
  exfalso. apply (f_equal edges) in H. simpl in H. lia.
Qed.

(** * Places *)

(** A place: here, or into that which is the point, or into that which
    isn't. *)
Inductive addr : Type :=
  | here : addr
  | into : addr -> addr
  | out : addr -> addr.

Fixpoint get (p : addr) (s : pl) : pl :=
  match p, s with
  | here, _ => s
  | into q, edge a _ => get q a
  | out q, edge _ b => get q b
  | _, nothing => nothing
  end.

(** Do f at a place, and leave everything else.  Going into nothing is
    still nothing, so a place aimed past what is drawn lands on the nothing
    it reaches. *)
Fixpoint there (p : addr) (f : pl -> pl) (s : pl) : pl :=
  match p, s with
  | here, _ => f s
  | into q, edge a b => edge (there q f a) b
  | out q, edge a b => edge a (there q f b)
  | _, nothing => f nothing
  end.

Lemma there_edges : forall p f s,
  edges (there p f s) + edges (get p s) = edges s + edges (f (get p s)).
Proof.
  induction p as [| q IH | q IH]; intros f [| a b]; simpl; try lia.
  - specialize (IH f a). lia.
  - specialize (IH f b). lia.
Qed.

(** * The latch *)

(** The two ways an edge can go around what is at a place: what was there
    becomes that which is the point, or that which isn't. *)
Inductive way : Type := as_is | as_isnt.

Definition latch (w : way) (t : pl) : pl :=
  match w with
  | as_is => edge t nothing
  | as_isnt => edge nothing t
  end.

Theorem both_ways_are_one_in_nothing : latch as_is nothing = latch as_isnt nothing.
Proof. reflexivity. Qed.

Theorem the_two_ways_differ_on_something : forall t,
  t <> nothing -> latch as_is t <> latch as_isnt t.
Proof. intros t Ht H. simpl in H. injection H as E _. exact (Ht E). Qed.

Lemma latch_edges : forall w t, edges (latch w t) = S (edges t).
Proof. intros [|] t; simpl; lia. Qed.

Lemma there_latch_adds_one : forall p w s, edges (there p (latch w) s) = S (edges s).
Proof.
  intros p w s. pose proof (there_edges p (latch w) s) as E.
  rewrite latch_edges in E. lia.
Qed.

(** * Told apart *)

(** A point's own two sides differ. *)
Definition told_apart (s : pl) : Prop :=
  match s with
  | nothing => False
  | edge a b => a <> b
  end.

(** Swap that which is the point and that which isn't, at the top. *)
Definition swap (s : pl) : pl := match s with nothing => nothing | edge a b => edge b a end.

Theorem the_lone_point_is_its_own_mirror : swap the_point = the_point.
Proof. reflexivity. Qed.

Theorem not_told_apart_iff_its_own_mirror : forall a b,
  ~ told_apart (edge a b) <-> swap (edge a b) = edge a b.
Proof.
  intros a b. simpl. split.
  - intro H. destruct (pl_eq_dec a b) as [E | N]; [subst; reflexivity | contradiction].
  - intros H N. injection H as E _. apply N. symmetry. exact E.
Qed.

Theorem told_apart_needs_another_edge : forall a b,
  told_apart (edge a b) -> edges a + edges b >= 1.
Proof.
  intros [| x y] [| u v] H; simpl in *; try lia.
  exfalso. apply H. reflexivity.
Qed.

(** A point at a place is decided when there is a point there, and an edge
    outside holds it or its own two sides differ. *)
Definition decided (w : pl) (p : addr) : Prop :=
  get p w <> nothing /\ (p <> here \/ told_apart (get p w)).

Theorem alone_it_is_not_decided : ~ decided the_point here.
Proof. intros [_ [H | H]]; apply H; reflexivity. Qed.

Theorem only_a_mirror_on_top_is_not_decided : forall w p, get p w <> nothing ->
  (~ decided w p <-> p = here /\ exists a, w = edge a a).
Proof.
  intros w p Hp. split.
  - intro H. destruct p as [| q | q].
    + split; [reflexivity |]. destruct w as [| a b]; [contradiction Hp; reflexivity |].
      exists a. destruct (pl_eq_dec a b) as [E | N]; [subst; reflexivity |].
      exfalso. apply H. split; [exact Hp | right; exact N].
    + exfalso. apply H. split; [exact Hp | left; discriminate].
    + exfalso. apply H. split; [exact Hp | left; discriminate].
  - intros [-> [a ->]] [_ [H | H]]; apply H; reflexivity.
Qed.

(** * The machine *)

Definition move := (addr * way)%type.

Definition step (s : pl) (m : move) : pl := there (fst m) (latch (snd m)) s.

Lemma step_adds_one : forall s m, edges (step s m) = S (edges s).
Proof. intros s [p w]. apply there_latch_adds_one. Qed.

Definition whole : AxSys nat nat_pre := counter pl move step edges (fun _ => 1).

Theorem whole_is_thiele : ax_thiele whole (fun s => s = nothing).
Proof. exact (counter_is_thiele pl move step edges step_adds_one nothing (here, as_is)). Qed.

Lemma whole_grows : ax_grows (X := whole).
Proof. exact (counter_grows pl move step edges step_adds_one (fun _ => 1)). Qed.

Lemma whole_exits : forall s m, ax_exits (X := whole) s m.
Proof. exact (counter_exits pl move step edges step_adds_one (fun _ => 1)). Qed.

(** The lone point moves only inside itself. *)
Definition inward (m : move) : move := (into (fst m), snd m).

Definition alone : AxSys nat nat_pre :=
  counter pl move (fun s m => step s (inward m)) edges (fun _ => 1).

Theorem alone_is_thiele : ax_thiele alone (fun s => s = the_point).
Proof.
  exact (counter_is_thiele pl move (fun s m => step s (inward m)) edges
           (fun s m => step_adds_one s (inward m)) the_point (here, as_is)).
Qed.

(** The same pointland, with any price list. *)
Definition priced (c : move -> nat) : AxSys nat nat_pre := counter pl move step edges c.

Theorem the_toll_here_is_every_move_costing : forall c, ax_a2 (X := priced c) <-> forall m, c m >= 1.
Proof. exact (counter_toll_iff pl move step edges step_adds_one nothing). Qed.

Theorem a_distinction_costs_exactly_one : forall c,
  ax_a2 (X := priced c) /\
  (forall tr s, ax_total (X := priced c) tr <= ax_exit_count (X := priced c) tr s)
  <-> forall m, c m = 1.
Proof. exact (counter_priced_exactly pl move step edges step_adds_one nothing). Qed.

(** Read only as "is there a point?". *)
Definition is_something (s : pl) : bool := match s with nothing => false | edge _ _ => true end.

Definition boxed (c : move -> nat) : AxSys bool two_pre :=
  mk_axsys bool two_pre pl move step c is_something.

Theorem no_yes_no_member_is_priced_exactly : forall (X : AxSys bool two_pre) starts,
  ax_thiele X starts ->
  ~ (forall tr s, ax_total (X := X) tr <= ax_exit_count (X := X) tr s).
Proof.
  intros X starts HT Hc.
  destruct (two_point_member_raising_move _ _ HT) as [i [[s [Hs Hsi]] Hup]].
  assert (H1 : ax_cost bool two_pre X i >= 1).
  { apply (proj1 HT s i). unfold ax_exits. rewrite Hs, Hsi. unfold bp_le. simpl. discriminate. }
  specialize (Hc [i] (ax_step bool two_pre X s i)).
  cbn [ax_total ax_exit_count] in Hc.
  rewrite (Hup _ Hsi), Hsi in Hc. simpl in Hc. lia.
Qed.

Theorem the_box_cannot_price_exactly : forall c, ax_a2 (X := boxed c) ->
  ~ (forall tr s, ax_total (X := boxed c) tr <= ax_exit_count (X := boxed c) tr s).
Proof.
  intros c Ha Hc.
  assert (H1 : c (here, as_is) >= 1).
  { apply (Ha nothing (here, as_is)). unfold ax_exits, bp_le. simpl. discriminate. }
  specialize (Hc [(here, as_is)] the_point). simpl in Hc. lia.
Qed.

(** Read by height. *)
Fixpoint height (s : pl) : nat :=
  match s with nothing => 0 | edge a b => S (Nat.max (height a) (height b)) end.

Definition by_height (c : move -> nat) : AxSys nat nat_pre :=
  mk_axsys nat nat_pre pl move step c height.

(** n points, each the inside of the next. *)
Fixpoint tower (n : nat) : pl :=
  match n with
  | 0 => nothing
  | S k => edge (tower k) nothing
  end.

Theorem the_height_cannot_price_exactly : forall c, ax_a2 (X := by_height c) ->
  ~ (forall tr s, ax_total (X := by_height c) tr <= ax_exit_count (X := by_height c) tr s).
Proof.
  intros c Ha Hc.
  assert (H1 : c (out here, as_is) >= 1).
  { apply (Ha the_point (out here, as_is)). unfold ax_exits. rewrite nat_pre_le.
    simpl. lia. }
  specialize (Hc [(out here, as_is)] (tower 3)). simpl in Hc. lia.
Qed.

(** If a move aimed past what is drawn were refused, it would raise
    nothing. *)
Fixpoint there_refused (p : addr) (f : pl -> pl) (s : pl) : pl :=
  match p, s with
  | here, _ => f s
  | into q, edge a b => edge (there_refused q f a) b
  | out q, edge a b => edge a (there_refused q f b)
  | _, nothing => nothing
  end.

Definition refusing (c : move -> nat) : AxSys nat nat_pre :=
  mk_axsys nat nat_pre pl move (fun s m => there_refused (fst m) (latch (snd m)) s) c edges.

Theorem refusing_moves_cannot_price_exactly : forall c, ax_a2 (X := refusing c) ->
  ~ (forall tr s, ax_total (X := refusing c) tr <= ax_exit_count (X := refusing c) tr s).
Proof.
  intros c Ha Hc.
  assert (H1 : c (into here, as_is) >= 1).
  { apply (Ha the_point (into here, as_is)). unfold ax_exits. rewrite nat_pre_le.
    simpl. lia. }
  specialize (Hc [(into here, as_is)] nothing). simpl in Hc. lia.
Qed.

(** * Going in *)

Theorem the_inside_is_the_whole : forall tr a b,
  ax_run (X := alone) tr (edge a b) = edge (ax_run (X := whole) tr a) b.
Proof.
  induction tr as [| m tr IH]; intros a b; [reflexivity |].
  simpl. unfold step at 1. simpl. apply IH.
Qed.

Lemma tower_run_from : forall n k,
  ax_run (X := alone) (repeat (here, as_is) n) (tower (S k)) = tower (S (n + k)).
Proof.
  induction n as [| n IH]; intro k; [reflexivity |].
  change (ax_run (X := alone) (repeat (here, as_is) n) (tower (S (S k))) =
          tower (S (S n + k))).
  rewrite IH. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem going_in_forever : forall n,
  ax_run (X := alone) (repeat (here, as_is) n) the_point = tower (S n).
Proof.
  intro n. change the_point with (tower 1).
  rewrite (tower_run_from n 0). rewrite Nat.add_0_r. reflexivity.
Qed.

Definition one_move_in : pl := step the_point (into here, as_is).

Theorem one_move_in_decides_two :
  one_move_in = edge the_point nothing /\
  ~ decided the_point here /\ ~ decided the_point (into here) /\
  decided one_move_in here /\ decided one_move_in (into here).
Proof.
  split; [reflexivity |]. split; [exact alone_it_is_not_decided |].
  split; [intros [H _]; apply H; reflexivity |]. split.
  - split; [simpl; discriminate | right; simpl; discriminate].
  - split; [simpl; discriminate | left; discriminate].
Qed.

(** The place n levels in. *)
Fixpoint deep (j : nat) : addr := match j with 0 => here | S k => into (deep k) end.

Lemma get_deep_tower : forall j k, j <= k -> get (deep j) (tower k) = tower (k - j).
Proof.
  induction j as [| j IH]; intros k H.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct k as [| k]; [lia |]. simpl. apply IH. lia.
Qed.

Theorem the_innermost_is_the_lone_point : forall n,
  get (deep n) (tower (S n)) = the_point /\ ~ told_apart (get (deep n) (tower (S n))).
Proof.
  intro n. rewrite get_deep_tower by lia. replace (S n - n) with 1 by lia.
  split; [reflexivity | simpl; intro H; apply H; reflexivity].
Qed.

Theorem the_innermost_is_held_only_by_the_edge_around_it : forall n, 1 <= n ->
  decided (tower (S n)) (deep n) /\ ~ told_apart (get (deep n) (tower (S n))).
Proof.
  intros n Hn. destruct (the_innermost_is_the_lone_point n) as [E N]. split; [| exact N].
  split; [rewrite E; discriminate |]. left. destruct n as [| k]; [lia | discriminate].
Qed.

Theorem every_point_of_a_tower_is_decided : forall n p,
  2 <= n -> get p (tower n) <> nothing -> decided (tower n) p.
Proof.
  intros n p Hn Hp. split; [exact Hp |].
  destruct p as [| q | q]; [| left; discriminate | left; discriminate].
  right. destruct n as [| [| k]]; [lia | lia |]. simpl. discriminate.
Qed.

(** A move can undo a point's being told apart. *)
Theorem telling_apart_does_not_last :
  decided (edge nothing the_point) here /\
  step (edge nothing the_point) (into here, as_is) = edge the_point the_point /\
  ~ decided (edge the_point the_point) here.
Proof.
  split; [split; [simpl; discriminate | right; simpl; discriminate] |].
  split; [reflexivity |]. intros [_ [H | H]]; apply H; reflexivity.
Qed.

(** * Up and in *)

Definition go_up : move := (here, as_is).
Definition go_in : move := (into here, as_is).

Theorem up_is_in_iff : forall s, step s go_up = step s go_in <-> that_isnt s = nothing.
Proof.
  intros [| a b]; simpl; split.
  - intros _. reflexivity.
  - intros _. reflexivity.
  - unfold step, go_up, go_in. simpl. intro H. injection H. intros. subst. reflexivity.
  - intros ->. reflexivity.
Qed.

Lemma alone_keeps_nothing_outside : forall tr,
  that_isnt (ax_run (X := alone) tr the_point) = nothing.
Proof. intro tr. unfold the_point. rewrite the_inside_is_the_whole. reflexivity. Qed.

Theorem for_a_point_alone_up_is_in : forall tr,
  let s := ax_run (X := alone) tr the_point in step s go_up = step s go_in.
Proof. intro tr. simpl. apply up_is_in_iff. apply alone_keeps_nothing_outside. Qed.

Theorem going_up_decides_everything_below : forall w p,
  w <> nothing -> get p (step w go_up) <> nothing -> decided (step w go_up) p.
Proof.
  intros w p Hw Hp. split; [exact Hp |].
  destruct p as [| q | q]; [| left; discriminate | left; discriminate].
  right. change (w <> nothing). exact Hw.
Qed.

(** * Nothing merges, and the window *)

Lemma there_latch_injective : forall p w s1 s2,
  there p (latch w) s1 = there p (latch w) s2 -> s1 = s2.
Proof.
  induction p as [| q IH | q IH]; intros w s1 s2 H.
  - destruct w; simpl in H; injection H; auto.
  - destruct s1 as [| a1 b1], s2 as [| a2 b2]; simpl in H.
    + reflexivity.
    + exfalso. apply (f_equal edges) in H. rewrite latch_edges in H. simpl in H.
      rewrite there_latch_adds_one in H. lia.
    + exfalso. apply (f_equal edges) in H. rewrite latch_edges in H. simpl in H.
      rewrite there_latch_adds_one in H. lia.
    + injection H as Ha Hb. subst b2. f_equal. exact (IH w a1 a2 Ha).
  - destruct s1 as [| a1 b1], s2 as [| a2 b2]; simpl in H.
    + reflexivity.
    + exfalso. apply (f_equal edges) in H. rewrite latch_edges in H. simpl in H.
      rewrite there_latch_adds_one in H. lia.
    + exfalso. apply (f_equal edges) in H. rewrite latch_edges in H. simpl in H.
      rewrite there_latch_adds_one in H. lia.
    + injection H as Ha Hb. subst a2. f_equal. exact (IH w b1 b2 Hb).
Qed.

Theorem nothing_merges : forall m, ax_step_injective whole m.
Proof. intros [p w] s1 s2 H. exact (there_latch_injective p w s1 s2 H). Qed.

Theorem merge_pricing_does_not_force_the_toll :
  ax_merging_priced (priced (fun _ => 0)) /\ ~ ax_a2 (X := priced (fun _ => 0)).
Proof.
  split.
  - intros [p w] H. exfalso. apply H. intros s1 s2 E.
    exact (there_latch_injective p w s1 s2 E).
  - intro H. pose proof (proj1 (the_toll_here_is_every_move_costing (fun _ => 0)) H (here, as_is)) as H1.
    simpl in H1. lia.
Qed.

Theorem pointland_is_endless : forall all, ~ ax_finite whole all.
Proof.
  intros all Hfin.
  exact (ax_growth_exit_merges all nothing (here, as_is) Hfin whole_grows
           (whole_exits nothing (here, as_is)) (nothing_merges (here, as_is))).
Qed.

Theorem seen_at_one_place_every_move_is_the_latch_move : forall s m,
  is_something (step s m) = ax_step bool two_pre latch_sys (is_something s) tt.
Proof.
  intros s m. change (ax_step bool two_pre latch_sys (is_something s) tt) with true.
  destruct (step s m) eqn:E; [| reflexivity].
  exfalso. apply (f_equal edges) in E. rewrite step_adds_one in E. discriminate.
Qed.

Theorem merged_at_one_place_kept_apart_edge_by_edge : forall m,
  is_something nothing <> is_something the_point /\
  is_something (step nothing m) = is_something (step the_point m) /\
  step nothing m <> step the_point m.
Proof.
  intro m. split; [discriminate |]. split.
  - rewrite !seen_at_one_place_every_move_is_the_latch_move. reflexivity.
  - intro H. pose proof (nothing_merges m nothing the_point H). discriminate.
Qed.

(** * The mirror *)

Fixpoint mirror (s : pl) : pl :=
  match s with
  | nothing => nothing
  | edge a b => edge (mirror b) (mirror a)
  end.

Fixpoint mirror_addr (p : addr) : addr :=
  match p with
  | here => here
  | into q => out (mirror_addr q)
  | out q => into (mirror_addr q)
  end.

Definition flip (w : way) : way := match w with as_is => as_isnt | as_isnt => as_is end.

Definition mirror_move (m : move) : move := (mirror_addr (fst m), flip (snd m)).

Lemma mirror_mirror : forall s, mirror (mirror s) = s.
Proof. induction s as [| a IHa b IHb]; simpl; [reflexivity | rewrite IHa, IHb; reflexivity]. Qed.

Lemma mirror_edges : forall s, edges (mirror s) = edges s.
Proof. induction s as [| a IHa b IHb]; simpl; [reflexivity | rewrite IHa, IHb; lia]. Qed.

Lemma mirror_latch : forall w t, mirror (latch w t) = latch (flip w) (mirror t).
Proof. intros [|] t; reflexivity. Qed.

Lemma mirror_there : forall p w s,
  mirror (there p (latch w) s) = there (mirror_addr p) (latch (flip w)) (mirror s).
Proof.
  induction p as [| q IH | q IH]; intros w [| a b]; simpl;
    try (rewrite IH; reflexivity); apply mirror_latch.
Qed.

Theorem the_laws_do_not_pick_a_side : forall s m,
  mirror (step s m) = step (mirror s) (mirror_move m) /\
  edges (mirror s) = edges s /\ mirror (mirror s) = s.
Proof.
  intros s [p w]. split; [| split; [apply mirror_edges | apply mirror_mirror]].
  unfold step, mirror_move. simpl. apply mirror_there.
Qed.

Theorem every_run_has_a_mirror_run : forall c tr s, (forall m, c (mirror_move m) = c m) ->
  mirror (ax_run (X := priced c) tr s) = ax_run (X := priced c) (map mirror_move tr) (mirror s) /\
  ax_total (X := priced c) (map mirror_move tr) = ax_total (X := priced c) tr.
Proof.
  intros c tr. induction tr as [| m tr IH]; intros s Hc; [split; reflexivity |].
  destruct (IH (step s m) Hc) as [IH1 IH2]. split.
  - change (mirror (ax_run (X := priced c) tr (step s m)) =
            ax_run (X := priced c) (map mirror_move tr) (step (mirror s) (mirror_move m))).
    rewrite IH1. f_equal. apply (proj1 (the_laws_do_not_pick_a_side s m)).
  - change (c (mirror_move m) + ax_total (X := priced c) (map mirror_move tr) =
            c m + ax_total (X := priced c) tr).
    rewrite Hc, IH2. reflexivity.
Qed.

Theorem the_mirror_keeps_what_is_told_apart : forall s, told_apart (mirror s) <-> told_apart s.
Proof.
  intros [| a b]; simpl; [tauto |]. split; intros H E; apply H.
  - rewrite E. reflexivity.
  - apply (f_equal mirror) in E. rewrite !mirror_mirror in E. symmetry. exact E.
Qed.

Lemma get_mirror : forall p s, get (mirror_addr p) (mirror s) = mirror (get p s).
Proof. induction p as [| q IH | q IH]; intros [| a b]; simpl; auto. Qed.

Lemma mirror_nothing_iff : forall s, mirror s = nothing <-> s = nothing.
Proof. intros [| a b]; simpl; split; intro H; try reflexivity; discriminate. Qed.

Theorem the_mirror_keeps_what_is_decided : forall s p,
  decided (mirror s) (mirror_addr p) <-> decided s p.
Proof.
  intros s p. unfold decided. rewrite get_mirror.
  pose proof (mirror_nothing_iff (get p s)) as M.
  pose proof (the_mirror_keeps_what_is_told_apart (get p s)) as T.
  assert (Hh : mirror_addr p <> here <-> p <> here)
    by (destruct p; simpl; [tauto | split; intros _ E; discriminate E | split; intros _ E; discriminate E]).
  tauto.
Qed.

Theorem the_point_alone_picks_a_side : forall m',
  ax_step nat nat_pre alone the_point m' <> mirror (ax_step nat nat_pre alone the_point (here, as_is)).
Proof.
  intros [p w] H.
  change (step the_point (into p, w) = mirror (step the_point (into here, as_is))) in H.
  unfold step in H. simpl in H. injection H as E1 E2. discriminate E2.
Qed.

(** * The endless point *)

(** Pointland without an end: an edge may have edges inside it forever. *)
CoInductive epl : Type :=
  | enothing : epl
  | eedge : epl -> epl -> epl.

Definition e_is (s : epl) : epl := match s with enothing => enothing | eedge a _ => a end.

Definition e_told_apart (s : epl) : Prop :=
  match s with enothing => False | eedge a b => a <> b end.

Definition e_unfold (s : epl) : epl := match s with enothing => enothing | eedge a b => eedge a b end.

Lemma e_unfold_eq : forall s, s = e_unfold s.
Proof. intros [| a b]; reflexivity. Qed.

Theorem its_own_inside_iff : forall s,
  e_is s = s <-> s = enothing \/ exists b, s = eedge s b.
Proof.
  intros [| a b]; simpl; split.
  - intros _. left. reflexivity.
  - intros _. reflexivity.
  - intro H. right. exists b. f_equal. exact H.
  - intros [H | [b' H]]; [discriminate | injection H as H1 _; exact H1].
Qed.

(** An edge with itself inside and nothing outside. *)
CoFixpoint endless : epl := eedge endless enothing.

Lemma endless_unfold : endless = eedge endless enothing.
Proof. rewrite (e_unfold_eq endless) at 1. reflexivity. Qed.

Theorem the_endless_point_is_its_own_inside : e_is endless = endless.
Proof. rewrite endless_unfold at 1. reflexivity. Qed.

Theorem the_endless_point_is_not_nothing : endless <> enothing.
Proof. rewrite endless_unfold. discriminate. Qed.

(** An edge with itself on both sides. *)
CoFixpoint twin : epl := eedge twin twin.

Lemma twin_unfold : twin = eedge twin twin.
Proof. rewrite (e_unfold_eq twin) at 1. reflexivity. Qed.

Theorem being_its_own_inside_does_not_tell_apart : e_is twin = twin /\ ~ e_told_apart twin.
Proof.
  split.
  - rewrite twin_unfold at 1. reflexivity.
  - rewrite twin_unfold at 1. simpl. intro H. apply H. reflexivity.
Qed.

Theorem the_endless_point_is_told_apart_by_its_other_side :
  e_told_apart endless /\ e_is endless = endless.
Proof.
  split; [| exact the_endless_point_is_its_own_inside].
  rewrite endless_unfold at 1. exact the_endless_point_is_not_nothing.
Qed.

(** An endless pointland seen n levels in. *)
Fixpoint cut_at (n : nat) (s : epl) : pl :=
  match n with
  | 0 => nothing
  | S k => match s with enothing => nothing | eedge a b => edge (cut_at k a) (cut_at k b) end
  end.

Lemma cut_nothing : forall n, cut_at n enothing = nothing.
Proof. intros [| n]; reflexivity. Qed.

Theorem the_tower_is_the_endless_point_cut_off : forall n, cut_at n endless = tower n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  rewrite endless_unfold. simpl. rewrite IH, cut_nothing. reflexivity.
Qed.

Theorem the_run_inward_draws_the_endless_point : forall n,
  ax_run (X := alone) (repeat (here, as_is) n) the_point = cut_at (S n) endless.
Proof. intro n. rewrite going_in_forever, the_tower_is_the_endless_point_cut_off. reflexivity. Qed.

(** * The point, with one place inside *)

(** Inside the point there is one place, and what is there is the same as
    nothing, so a point differs from nothing only by its latch: open, or
    closed as that which is the point, or closed as that which isn't. *)
Inductive latch_state : Type := open_both | closed_is | closed_isnt.

Inductive closing : Type := close_is | close_isnt.

(** Closing an open latch makes one distinction true; closing a closed latch
    again changes nothing. *)
Definition close (s : latch_state) (c : closing) : latch_state :=
  match s with
  | open_both => match c with close_is => closed_is | close_isnt => closed_isnt end
  | _ => s
  end.

Definition is_closed (s : latch_state) : bool := match s with open_both => false | _ => true end.

Definition the_point_machine (price : closing -> nat) : AxSys bool two_pre :=
  mk_axsys bool two_pre latch_state closing close price is_closed.

Definition point_one : AxSys bool two_pre := the_point_machine (fun _ => 1).

Theorem closing_again_changes_nothing : forall s c, s <> open_both -> close s c = s.
Proof. intros [| |] c H; [contradiction H; reflexivity | reflexivity | reflexivity]. Qed.

Theorem either_distinction_can_be_made_true :
  close open_both close_is = closed_is /\ close open_both close_isnt = closed_isnt /\
  closed_is <> closed_isnt.
Proof. split; [reflexivity | split; [reflexivity | discriminate]]. Qed.

Theorem three_ways_to_be : ax_finite point_one [open_both; closed_is; closed_isnt].
Proof.
  split.
  - constructor; [simpl; intuition discriminate |].
    constructor; [simpl; intuition discriminate |].
    constructor; [simpl; intuition discriminate | constructor].
  - intros [| |]; simpl; [left | right; left | right; right; left]; reflexivity.
Qed.

Lemma point_grows : forall price, ax_grows (X := the_point_machine price).
Proof. intros price [| |] [|]; unfold bp_le; simpl; reflexivity. Qed.

Theorem the_point_is_a_thiele_machine : ax_thiele point_one (fun s => s = open_both).
Proof.
  split; [| split].
  - intros s i _. simpl. lia.
  - apply point_grows.
  - exists open_both, [close_is]. split; [reflexivity |]. unfold bp_le. simpl. discriminate.
Qed.

Theorem the_latch_merges_inside_the_point : forall c, ~ ax_step_injective point_one c.
Proof.
  intros [|] H.
  - specialize (H open_both closed_is eq_refl). discriminate.
  - specialize (H open_both closed_isnt eq_refl). discriminate.
Qed.

Theorem the_merge_inside_the_point_is_forced : forall s c,
  ax_exits (X := point_one) s c -> ~ ax_step_injective point_one c.
Proof.
  intros s c Hex.
  exact (ax_growth_exit_merges (X := point_one) [open_both; closed_is; closed_isnt] s c
           three_ways_to_be (point_grows _) Hex).
Qed.

Theorem a_distinction_costs_because_a_merge_does : forall price,
  ax_merging_priced (the_point_machine price) -> ax_a2 (X := the_point_machine price).
Proof.
  intros price Hm.
  apply (ax_a2_from_merge_price (X := the_point_machine price)
           [open_both; closed_is; closed_isnt]);
    [exact three_ways_to_be | apply point_grows | exact Hm].
Qed.

Theorem the_toll_inside_the_point_is_the_merge_price : forall price,
  ax_a2 (X := the_point_machine price) <-> ax_merging_priced (the_point_machine price).
Proof.
  intro price. split.
  - intros Ha c _. apply (Ha open_both c). unfold ax_exits, bp_le.
    destruct c; simpl; discriminate.
  - apply a_distinction_costs_because_a_merge_does.
Qed.

(** * Where the two pictures meet *)

(** A pointland kept edge by edge, asked only whether an edge is there. *)
Definition at_one_place (s : pl) : latch_state := if is_something s then closed_is else open_both.

Theorem kept_pointland_at_one_place_is_the_point : forall s m,
  at_one_place (step s m) = close (at_one_place s) close_is.
Proof.
  intros s m. unfold at_one_place.
  rewrite seen_at_one_place_every_move_is_the_latch_move. simpl.
  destruct (is_something s); reflexivity.
Qed.

(** A clock, asked only whether it has ticked. *)
Definition ticked (n : nat) : latch_state := match n with 0 => open_both | S _ => closed_is end.

Theorem a_clock_at_one_place_is_the_point_too : forall n,
  ticked (S n) = close (ticked n) close_is.
Proof. intros [| n]; reflexivity. Qed.

Theorem read_by_its_count_a_clock_never_merges :
  ax_merging_priced (counter nat unit (fun n _ => S n) (fun n => n) (fun _ => 0)) /\
  ~ ax_a2 (X := counter nat unit (fun n _ => S n) (fun n => n) (fun _ => 0)).
Proof.
  split.
  - intros i H. exfalso. apply H. intros a b E. simpl in E. injection E as E. exact E.
  - intro H.
    pose proof (proj1 (counter_toll_iff nat unit (fun n _ => S n) (fun n => n)
                         (fun _ _ => eq_refl) 0 (fun _ => 0)) H tt) as H1.
    simpl in H1. lia.
Qed.

(** * The forks, worked out *)

(** Which way the point closed is a record of its own. *)
Definition closed_as_the_point (s : latch_state) : bool :=
  match s with closed_is => true | _ => false end.

Theorem the_way_it_closed_is_a_record :
  closed_is <> closed_isnt /\
  ax_thiele (mk_axsys bool two_pre latch_state closing close (fun _ => 1) closed_as_the_point)
            (fun s => s = open_both).
Proof.
  split; [discriminate |]. split; [| split].
  - intros s c _. simpl. lia.
  - intros [| |] [|]; unfold bp_le; simpl; reflexivity.
  - exists open_both, [close_is]. split; [reflexivity |]. unfold bp_le. simpl. discriminate.
Qed.

(** Swap that which is the point and that which isn't, in the point's own
    machine. *)
Definition mirror_state (s : latch_state) : latch_state :=
  match s with open_both => open_both | closed_is => closed_isnt | closed_isnt => closed_is end.

Definition mirror_closing (c : closing) : closing :=
  match c with close_is => close_isnt | close_isnt => close_is end.

Theorem the_two_closed_ways_are_mirror_images : forall s c,
  close (mirror_state s) (mirror_closing c) = mirror_state (close s c) /\
  is_closed (mirror_state s) = is_closed s /\
  mirror_state (mirror_state s) = s /\
  mirror_state closed_is = closed_isnt.
Proof. intros [| |] [|]; repeat split; reflexivity. Qed.

Theorem every_run_of_the_point_has_a_mirror_run : forall tr s,
  mirror_state (ax_run (X := point_one) tr s) =
  ax_run (X := point_one) (map mirror_closing tr) (mirror_state s).
Proof.
  induction tr as [| c tr IH]; intro s; [reflexivity |].
  simpl. rewrite IH. f_equal. destruct s, c; reflexivity.
Qed.

(** Read only closed or not, which puts each closed way with its mirror. *)
Theorem the_point_read_closed_or_not_is_the_latch : forall s c,
  is_closed (close s c) = ax_step bool two_pre latch_sys (is_closed s) tt.
Proof. intros [| |] [|]; reflexivity. Qed.

(** The outermost point's sides differ. *)
Definition told_apartb (s : pl) : bool :=
  match s with nothing => false | edge a b => if pl_eq_dec a b then false else true end.

(** Some point's sides differ. *)
Fixpoint any_told_apartb (s : pl) : bool :=
  match s with
  | nothing => false
  | edge a b =>
      orb (if pl_eq_dec a b then false else true) (orb (any_told_apartb a) (any_told_apartb b))
  end.

Theorem neither_difference_reading_is_a_record :
  ~ ax_grows (X := mk_axsys bool two_pre pl move step (fun _ => 1) told_apartb) /\
  ~ ax_grows (X := mk_axsys bool two_pre pl move step (fun _ => 1) any_told_apartb).
Proof.
  split; intro H; specialize (H (edge nothing the_point) (into here, as_is));
    vm_compute in H; discriminate H.
Qed.

Theorem the_edge_is_a_record : ax_grows (X := boxed (fun _ => 1)).
Proof.
  intros s m. unfold bp_le.
  change (implb (is_something s) (is_something (step s m)) = true).
  rewrite seen_at_one_place_every_move_is_the_latch_move.
  destruct (is_something s); reflexivity.
Qed.

Theorem connecting_to_itself_closes_the_point : forall c,
  is_closed (close open_both c) = true /\ close (close open_both c) c = close open_both c.
Proof. intros [|]; split; reflexivity. Qed.

Theorem going_in_puts_an_edge_inside : forall s, s <> nothing ->
  get (into here) (step s go_in) <> nothing.
Proof. intros [| a b] H; [contradiction H; reflexivity | simpl; discriminate]. Qed.

Theorem every_endless_edge_is_something : forall a b, eedge a b <> enothing.
Proof. intros a b H. discriminate H. Qed.

(** * Every result, checked *)
Print Assumptions counter_is_thiele.
Print Assumptions counter_toll_iff.
Print Assumptions counter_priced_exactly.
Print Assumptions a_clock_is_a_thiele_machine_too.
Print Assumptions a_clock_is_priced_the_same_way.
Print Assumptions a_latch_with_no_inside_is_a_thiele_machine.
Print Assumptions one_way_to_be_is_not_a_thiele_machine.
Print Assumptions inside_the_lone_point_is_nothing.
Print Assumptions the_lone_point_is_one_edge.
Print Assumptions nothing_but_edges.
Print Assumptions only_nothing_is_its_own_inside.
Print Assumptions both_ways_are_one_in_nothing.
Print Assumptions the_two_ways_differ_on_something.
Print Assumptions the_lone_point_is_its_own_mirror.
Print Assumptions not_told_apart_iff_its_own_mirror.
Print Assumptions told_apart_needs_another_edge.
Print Assumptions alone_it_is_not_decided.
Print Assumptions only_a_mirror_on_top_is_not_decided.
Print Assumptions whole_is_thiele.
Print Assumptions alone_is_thiele.
Print Assumptions the_toll_here_is_every_move_costing.
Print Assumptions a_distinction_costs_exactly_one.
Print Assumptions no_yes_no_member_is_priced_exactly.
Print Assumptions the_box_cannot_price_exactly.
Print Assumptions the_height_cannot_price_exactly.
Print Assumptions refusing_moves_cannot_price_exactly.
Print Assumptions the_inside_is_the_whole.
Print Assumptions going_in_forever.
Print Assumptions one_move_in_decides_two.
Print Assumptions the_innermost_is_the_lone_point.
Print Assumptions the_innermost_is_held_only_by_the_edge_around_it.
Print Assumptions every_point_of_a_tower_is_decided.
Print Assumptions telling_apart_does_not_last.
Print Assumptions up_is_in_iff.
Print Assumptions for_a_point_alone_up_is_in.
Print Assumptions going_up_decides_everything_below.
Print Assumptions nothing_merges.
Print Assumptions merge_pricing_does_not_force_the_toll.
Print Assumptions pointland_is_endless.
Print Assumptions seen_at_one_place_every_move_is_the_latch_move.
Print Assumptions merged_at_one_place_kept_apart_edge_by_edge.
Print Assumptions the_laws_do_not_pick_a_side.
Print Assumptions every_run_has_a_mirror_run.
Print Assumptions the_mirror_keeps_what_is_told_apart.
Print Assumptions the_mirror_keeps_what_is_decided.
Print Assumptions the_point_alone_picks_a_side.
Print Assumptions its_own_inside_iff.
Print Assumptions the_endless_point_is_its_own_inside.
Print Assumptions the_endless_point_is_not_nothing.
Print Assumptions being_its_own_inside_does_not_tell_apart.
Print Assumptions the_endless_point_is_told_apart_by_its_other_side.
Print Assumptions the_tower_is_the_endless_point_cut_off.
Print Assumptions the_run_inward_draws_the_endless_point.
Print Assumptions closing_again_changes_nothing.
Print Assumptions either_distinction_can_be_made_true.
Print Assumptions three_ways_to_be.
Print Assumptions the_point_is_a_thiele_machine.
Print Assumptions the_latch_merges_inside_the_point.
Print Assumptions the_merge_inside_the_point_is_forced.
Print Assumptions a_distinction_costs_because_a_merge_does.
Print Assumptions the_toll_inside_the_point_is_the_merge_price.
Print Assumptions kept_pointland_at_one_place_is_the_point.
Print Assumptions a_clock_at_one_place_is_the_point_too.
Print Assumptions read_by_its_count_a_clock_never_merges.
Print Assumptions the_way_it_closed_is_a_record.
Print Assumptions the_two_closed_ways_are_mirror_images.
Print Assumptions every_run_of_the_point_has_a_mirror_run.
Print Assumptions the_point_read_closed_or_not_is_the_latch.
Print Assumptions neither_difference_reading_is_a_record.
Print Assumptions the_edge_is_a_record.
Print Assumptions connecting_to_itself_closes_the_point.
Print Assumptions going_in_puts_an_edge_inside.
Print Assumptions every_endless_edge_is_something.
