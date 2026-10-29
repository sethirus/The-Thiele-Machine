(* SCOPE NOTE: standalone proof scope. the sliced definition is built from the
   slice core, not from the record system itself. *)
From Coq Require Import List Bool Arith Lia.
From Minimal Require Import SliceCore CompleteHost Representation.
Import ListNotations.

(* The user-selected Option 2. A Boolean permanent verdict is explicit;
   current-edition query vectors are a separate observation below. *)
Record SlicedInterface (State Base Horizontal Vertical : Type) := {
  view : State -> Base;
  view_onto : forall b, exists s, view s = b;
  verdict : State -> bool;
  horizontal : Horizontal -> State -> State;
  vertical : Vertical -> State -> State;
  shadow_step : Horizontal -> Base -> Base;
  vertical_price : Vertical -> nat;
  horizontal_projects : forall i s,
    view (horizontal i s) = shadow_step i (view s);
  horizontal_preserves_verdict : forall i s,
    verdict (horizontal i s) = verdict s;
  vertical_preserves_view : forall i s, view (vertical i s) = view s;
  vertical_preserves_yes : forall i s,
    verdict s = true -> verdict (vertical i s) = true;
  vertical_raise_pays : forall i s,
    verdict s = false -> verdict (vertical i s) = true ->
    1 <= vertical_price i
}.
Arguments view {State Base Horizontal Vertical} _ _.
Arguments verdict {State Base Horizontal Vertical} _ _.
Arguments horizontal {State Base Horizontal Vertical} _ _ _.
Arguments vertical {State Base Horizontal Vertical} _ _ _.
Arguments shadow_step {State Base Horizontal Vertical} _ _ _.
Arguments vertical_price {State Base Horizontal Vertical} _ _.

Section InterfaceResults.
  Context {State Base Horizontal Vertical : Type}.
  Variable M : SlicedInterface State Base Horizontal Vertical.

  Definition instruction := (Horizontal + Vertical)%type.
  Definition transition (i : instruction) (s : State) :=
    match i with inl h => horizontal M h s | inr v => vertical M v s end.
  Definition price (i : instruction) :=
    match i with inl _ => 0 | inr v => vertical_price M v end.
  Definition hrun := SliceCore.run (horizontal M).
  Definition execute := SliceCore.allrun (horizontal M) (vertical M).
  Definition shadow_run := SliceCore.run (shadow_step M).

  Theorem horizontal_trace_projects : forall w s,
    view M (hrun w s) = shadow_run w (view M s).
  Proof.
    induction w as [|i w IH]; intro s; simpl; [reflexivity|].
    unfold hrun in IH; rewrite IH, horizontal_projects; reflexivity.
  Qed.

  Theorem horizontal_trace_preserves_verdict : forall w s,
    verdict M (hrun w s) = verdict M s.
  Proof.
    induction w as [|i w IH]; intro s; simpl; [reflexivity|].
    unfold hrun in IH; rewrite IH; apply horizontal_preserves_verdict.
  Qed.

  Theorem universal_window_blindness : forall s t,
    view M s = view M t -> forall w,
    view M (hrun w s) = view M (hrun w t).
  Proof. intros s t E w; rewrite !horizontal_trace_projects, E; reflexivity. Qed.

  Theorem mixed_trace_projects_after_erasure : forall w s,
    view M (execute w s) = shadow_run (SliceCore.purge w) (view M s).
  Proof.
    intros w s. unfold execute.
    rewrite (SliceCore.invisible_marks_allow_purge
      (horizontal M) (vertical M) (view M)).
    - apply horizontal_trace_projects.
    - intros x p cs. change (view M (hrun cs x) = view M (hrun cs (vertical M p x))).
      rewrite !horizontal_trace_projects, vertical_preserves_view; reflexivity.
  Qed.

  Theorem vertical_raise_forces_hidden_pair : forall v s,
    verdict M s = false -> verdict M (vertical M v s) = true ->
    s <> vertical M v s /\ view M s = view M (vertical M v s).
  Proof.
    intros v s H0 H1; split.
    - intro E; rewrite E in H0; congruence.
    - symmetry; apply vertical_preserves_view.
  Qed.

  Theorem vertical_raise_fibre_capacity : forall v s fibre,
    verdict M s = false -> verdict M (vertical M v s) = true ->
    (forall x, view M x = view M s -> In x fibre) -> 2 <= length fibre.
  Proof.
    intros v s fibre H0 H1 Hcover.
    destruct (vertical_raise_forces_hidden_pair v s H0 H1) as [Hneq Hsame].
    assert (Hnd : NoDup [s;vertical M v s]).
    { repeat constructor; simpl; intuition. }
    apply (NoDup_incl_length Hnd).
    intros x [<-|[<-|[]]]; apply Hcover; [reflexivity|symmetry; exact Hsame].
  Qed.

  (* The subset may be smaller than the entire accepting fibre. It must
     contain the entering successor and be closed under this vertical move. *)
  Theorem finite_vertical_establishment_collision
    (eq_dec : forall x y : State, {x=y}+{x<>y}) : forall v s held,
    verdict M s = false -> In (vertical M v s) held -> NoDup held ->
    (forall x, In x held -> view M x = view M s /\ verdict M x = true) ->
    (forall x, In x held -> In (vertical M v x) held) ->
    exists x y, view M x = view M s /\ view M y = view M s /\
      x <> y /\ vertical M v x = vertical M v y.
  Proof.
    intros v s held Hno Hentry Hnd Hspec Hclosed.
    assert (Houtside : ~ In s held).
    { intro H; destruct (Hspec s H); congruence. }
    destruct (@CompleteHost.finite_hold_collision State (vertical M v)
      (fun x => In x held) s Houtside Hentry Hclosed eq_dec held Hnd
      (fun x => iff_refl _)) as [x [y [Hx [Hy [Hneq Heq]]]]].
    exists x,y; repeat split; try assumption.
    - destruct Hx as [<-|Hx]; [reflexivity|apply Hspec; assumption].
    - destruct Hy as [<-|Hy]; [reflexivity|apply Hspec; assumption].
  Qed.

  (* The trace hypotheses specify the required history distinction; their
     semantic meaning is not inferred from a bare Boolean field. *)
  Theorem abstract_establishment_necessity : forall start raw checked b,
    view M (hrun raw start) = b -> view M (execute checked start) = b ->
    verdict M (hrun raw start) = false -> verdict M (execute checked start) = true ->
    hrun raw start <> execute checked start /\
    (forall continuation,
      view M (hrun continuation (hrun raw start)) =
        view M (hrun continuation (execute checked start)) /\
      verdict M (hrun continuation (hrun raw start)) = false /\
      verdict M (hrun continuation (execute checked start)) = true) /\
    ~ exists decode : Base -> bool, forall s, decode (view M s) = verdict M s.
  Proof.
    intros start raw checked b Hr Hc H0 H1.
    assert (Hsame : view M (hrun raw start) = view M (execute checked start)) by congruence.
    split; [intro E; rewrite E in H0; congruence|].
    split.
    - intro w; split; [apply universal_window_blindness; exact Hsame|].
      rewrite (horizontal_trace_preserves_verdict w (hrun raw start)),
        (horizontal_trace_preserves_verdict w (execute checked start)); auto.
    - apply (SliceCore.factorization_obstruction (view M) (verdict M)).
      exists (hrun raw start), (execute checked start); split; [exact Hsame|congruence].
  Qed.

  Fixpoint trace_price (w : list instruction) :=
    match w with [] => 0 | i::rest => price i + trace_price rest end.

  Theorem supplied_toll : forall i s,
    verdict M s = false -> verdict M (transition i s) = true -> 1 <= price i.
  Proof.
    intros [h|v] s H0 H1; simpl in *.
    - rewrite horizontal_preserves_verdict in H1; congruence.
    - eapply vertical_raise_pays; eassumption.
  Qed.

  Theorem supplied_toll_run_floor : forall w s,
    verdict M s = false -> verdict M (execute w s) = true -> 1 <= trace_price w.
  Proof.
    induction w as [|[h|v] w IH]; intros s H0 H1; simpl in *.
    - congruence.
    - eapply IH; [rewrite horizontal_preserves_verdict; exact H0|exact H1].
    - destruct (verdict M (vertical M v s)) eqn:E.
      + pose proof (vertical_raise_pays _ _ _ _ M v s H0 E); lia.
      + specialize (IH _ E H1); lia.
  Qed.

  Record InternalLedger := {
    ledger : State -> nat;
    ledger_update : forall i s, ledger (transition i s) = ledger s + price i
  }.

  Theorem horizontal_ledger_preserved (L : InternalLedger) : forall h s,
    ledger L (horizontal M h s) = ledger L s.
  Proof.
    intros h s; pose proof (ledger_update L (inl h) s) as H.
    simpl in H; lia.
  Qed.

  (* Current-edition profiles require a separate exact query observation.
     Every legal profile is supplied with a realizing instruction word. *)
  Theorem independent_current_profiles_capacity
    (truth : Base -> list bool) (queries : State -> list bool)
    (program_for : Base * list bool -> list instruction) : forall start bases reachable,
    NoDup bases ->
    (forall d, In d (Representation.descriptions truth bases) ->
      (view M (execute (program_for d) start), queries (execute (program_for d) start)) = d) ->
    (forall d, In d (Representation.descriptions truth bases) ->
      In (execute (program_for d) start) reachable) ->
    Representation.capacity truth bases <= length reachable.
  Proof.
    intros start bases reachable Hnd Hreal Hreach.
    eapply (Representation.exact_profile_representation_lower_bound truth
      (fun s => (view M s, queries s)) (fun d => execute (program_for d) start));
      eassumption.
  Qed.
End InterfaceResults.

(* A nonvacuous implementation for any supplied base and Boolean checker.
   A product is used for this witness only; it is not an interface axiom. *)
Module Witness.
Section Construction.
  Context {B C : Type}.
  Variable base : C -> B -> B.
  Variable predicate : B -> bool.

  Definition compute (c : C) (s : B * bool) := (base c (fst s), snd s).
  Definition check (_ : unit) (s : B * bool) :=
    (fst s, orb (snd s) (predicate (fst s))).

  Definition machine : SlicedInterface (B * bool) B C unit.
  Proof.
    refine {| view := @fst B bool; verdict := @snd B bool;
              horizontal := compute; vertical := check; shadow_step := base;
              vertical_price := fun _ => 1 |}.
    - intro b; exists (b,false); reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros [] [b r]; simpl; intro E; rewrite E; reflexivity.
    - intros; lia.
  Defined.

  Fixpoint successful_check_occurred (w : list (C + unit)) (b : B) : bool :=
    match w with
    | [] => false
    | inl c :: rest => successful_check_occurred rest (base c b)
    | inr _ :: rest => predicate b || successful_check_occurred rest b
    end.

  Theorem exact_ever_checked_meaning : forall w b r,
    verdict machine (execute machine w (b,r)) =
    r || successful_check_occurred w b.
  Proof.
    induction w as [|[c|[]] w IH]; intros b r.
    - simpl; rewrite orb_false_r; reflexivity.
    - change (snd (execute machine w (base c b,r)) =
        r || successful_check_occurred w (base c b)). apply IH.
    - change (verdict machine (execute machine w (b,r || predicate b)) =
        r || (predicate b || successful_check_occurred w b)).
      rewrite IH. destruct r, (predicate b), (successful_check_occurred w b); reflexivity.
  Qed.

  Theorem clean_start_exact_history : forall w b,
    verdict machine (execute machine w (b,false)) = successful_check_occurred w b.
  Proof. intros; rewrite exact_ever_checked_meaning; reflexivity. Qed.

  Theorem passing_check_realizes_hidden_pair : forall b, predicate b = true ->
    view machine (execute machine [] (b,false)) = b /\
    view machine (execute machine [inr tt] (b,false)) = b /\
    verdict machine (execute machine [] (b,false)) = false /\
    verdict machine (execute machine [inr tt] (b,false)) = true.
  Proof. intros b Hb; simpl; rewrite Hb; repeat split. Qed.
End Construction.
End Witness.
