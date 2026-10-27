(* Universal property of NeutralComplete.nlift under fixed base/event,
   exact latch and unit accounting laws. The map forgets implementation
   history. Minimality observes the base, reading AND ledger on reachable
   states. Least unit pricing requires every mark event to be possible. *)
From Coq Require Import List Bool Arith Lia.
From Kernel Require Import CostSemanticsComparison.
From Audit Require Import CanonicalObservation.
From Audit Require Import LeastToll.
Require Minimal.ThieleComplete Minimal.NeutralComplete.
Import ListNotations.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.
Module O := CanonicalObservation.

Section TerminalLift.
Variable base : T.machine.
Variable K : Type.
Variable event : K -> T.m_state base -> bool.
Definition C := N.nstate base.
Definition I := N.nmove base K.
Definition canonical := N.nlift base K event.

Variable X : Type.
Variable horizontal : T.m_move base -> X -> X.
Variable vertical : K -> X -> X.
Variable view : X -> T.m_state base.
Variable reading : X -> bool.
Variable ledger : X -> nat.
Definition transition (i : I) (x : X) :=
  match i with N.NBase h => horizontal h x | N.NMark k => vertical k x end.
Definition project (x : X) : C := (view x, reading x, ledger x).

Hypothesis hbase : forall h x, view (horizontal h x) = T.m_step base (view x) h.
Hypothesis vbase : forall k x, view (vertical k x) = view x.
Hypothesis vlatch : forall k x,
  reading (vertical k x) = orb (reading x) (event k (view x)).
Hypothesis toll : a2 X I (fun x i => transition i x) (N.ncost base K) reading.
Hypothesis permanent : forall x i, reading x = true -> reading (transition i x) = true.
Hypothesis accounting : forall x i,
  ledger (transition i x) = ledger x + N.ncost base K i.

Lemma horizontal_reading_derived : forall h x,
  reading (horizontal h x) = reading x.
Proof.
  intros h x; apply (free_reading_invariance X I
    (fun x i => transition i x) (N.ncost base K) reading toll permanent
    x (@N.NBase base K h)); reflexivity.
Qed.

Theorem projection_commutes : forall i x,
  project (transition i x) = T.m_step canonical (project x) i.
Proof.
  intros [h|k] x; unfold project, transition; cbn.
  - rewrite hbase, horizontal_reading_derived.
    pose proof (accounting x (@N.NBase base K h)) as H; cbn in H.
    replace (ledger (horizontal h x)) with (ledger x) by lia; reflexivity.
  - rewrite vbase, vlatch.
    pose proof (accounting x (@N.NMark base K k)) as H; cbn in H.
    replace (ledger (vertical k x)) with (S (ledger x)) by lia; reflexivity.
Qed.

Theorem projection_preserves_runs : forall w x,
  project (O.run transition w x) = T.run canonical w (project x).
Proof.
  induction w as [|i w IH]; intro x; cbn; [reflexivity|].
  rewrite IH, projection_commutes; reflexivity.
Qed.

(* Coordinate preservation determines the map on all states, even before
   a start or reachability is selected. *)
Theorem projection_unique_over_coordinates : forall f : X -> C,
  (forall x, fst (fst (f x)) = view x) ->
  (forall x, snd (fst (f x)) = reading x) ->
  (forall x, snd (f x) = ledger x) ->
  forall x, f x = project x.
Proof.
  intros f Hb Hr Hl x; specialize (Hb x); specialize (Hr x); specialize (Hl x).
  destruct (f x) as [[b r] l]; cbn in *; subst; reflexivity.
Qed.

Theorem lift_terminal_over_exact_coordinates :
  exists f : X -> C,
    (forall i x, f (transition i x) = T.m_step canonical (f x) i) /\
    (forall x, fst (fst (f x)) = view x) /\
    (forall x, snd (fst (f x)) = reading x) /\
    (forall x, snd (f x) = ledger x) /\
    (forall g : X -> C,
      (forall x, fst (fst (g x)) = view x) ->
      (forall x, snd (fst (g x)) = reading x) ->
      (forall x, snd (g x) = ledger x) -> forall x, g x = f x).
Proof.
  exists project; repeat split; try reflexivity.
  - apply projection_commutes.
  - apply projection_unique_over_coordinates.
Qed.

Theorem observable_equivalence_exactly_projection_kernel : forall x y,
  (forall w, project (O.run transition w x) = project (O.run transition w y))
    <-> project x = project y.
Proof.
  intros x y; split.
  - intro H; exact (H []).
  - intros H w; rewrite !projection_preserves_runs, H; reflexivity.
Qed.

Variable start : X.
Hypothesis clean_reading : reading start = false.
Hypothesis clean_ledger : ledger start = 0.
Definition cstart : C := (view start, false, 0).

Lemma projection_clean_start : project start = cstart.
Proof. unfold project, cstart; rewrite clean_reading, clean_ledger; reflexivity. Qed.

Theorem projection_onto_reachable : forall c,
  (exists w, T.run canonical w cstart = c) ->
  exists x, (exists w, O.run transition w start = x) /\ project x = c.
Proof.
  intros c [w E]; exists (O.run transition w start); split.
  - exists w; reflexivity.
  - rewrite projection_preserves_runs, projection_clean_start; exact E.
Qed.

Theorem reachable_maps_pointwise_unique : forall f : X -> C,
  f start = cstart ->
  (forall i x, f (transition i x) = T.m_step canonical (f x) i) ->
  forall x, (exists w, O.run transition w start = x) -> f x = project x.
Proof.
  intros f H0 Hs.
  assert (Hrun : forall w x, f (O.run transition w x) = T.run canonical w (f x)).
  { induction w as [|i w IH]; intro x; cbn; [reflexivity|].
    rewrite IH, Hs; reflexivity. }
  intros x [w <-]; rewrite Hrun, projection_preserves_runs, H0, projection_clean_start.
  reflexivity.
Qed.

Theorem trace_extension_factorization :
  exists eval : list I -> X,
    eval [] = start /\
    (forall w i, eval (w ++ [i]) = transition i (eval w)) /\
    (forall w, project (eval w) = T.run canonical w cstart) /\
    (forall f : list I -> X, f [] = start ->
      (forall w i, f (w ++ [i]) = transition i (f w)) ->
      forall w, f w = eval w).
Proof.
  exists (fun w => O.run transition w start); repeat split.
  - intros w i; rewrite O.run_append; reflexivity.
  - intro w; rewrite projection_preserves_runs, projection_clean_start; reflexivity.
  - intros f H0 Hs w; induction w using rev_ind.
    + exact H0.
    + rewrite Hs, IHw, O.run_append; reflexivity.
Qed.

Theorem separated_reachable_extension_has_no_projection_collisions :
  (forall x y,
    (exists w, O.run transition w start = x) ->
    (exists w, O.run transition w start = y) ->
    (forall w, project (O.run transition w x) = project (O.run transition w y)) ->
    x = y) ->
  forall x y,
    (exists w, O.run transition w start = x) ->
    (exists w, O.run transition w start = y) -> project x = project y -> x = y.
Proof.
  intros H x y Hx Hy E; apply H; try assumption.
  apply observable_equivalence_exactly_projection_kernel; exact E.
Qed.

Theorem reachable_minimal_realization :
  (forall x y,
    (exists w, O.run transition w start = x) ->
    (exists w, O.run transition w start = y) ->
    (forall w, project (O.run transition w x) = project (O.run transition w y)) ->
    x = y) ->
  project start = cstart /\
  (forall i x, project (transition i x) = T.m_step canonical (project x) i) /\
  (forall c, (exists w, T.run canonical w cstart = c) ->
    exists x, (exists w, O.run transition w start = x) /\ project x = c) /\
  (forall x y,
    (exists w, O.run transition w start = x) ->
    (exists w, O.run transition w start = y) -> project x = project y -> x = y) /\
  (forall f : X -> C, f start = cstart ->
    (forall i x, f (transition i x) = T.m_step canonical (f x) i) ->
    forall x, (exists w, O.run transition w start = x) -> f x = project x).
Proof.
  intro H; repeat split.
  - apply projection_clean_start.
  - apply projection_commutes.
  - apply projection_onto_reachable.
  - apply separated_reachable_extension_has_no_projection_collisions; exact H.
  - apply reachable_maps_pointwise_unique.
Qed.
End TerminalLift.

Section CanonicalWitness.
Variable base : T.machine.
Variable K : Type.
Variable event : K -> T.m_state base -> bool.

Theorem canonical_satisfies_contract :
  (forall h s, fst (fst (N.nstep base K event s (@N.NBase base K h))) =
    T.m_step base (fst (fst s)) h) /\
  (forall k s, fst (fst (N.nstep base K event s (@N.NMark base K k))) = fst (fst s)) /\
  (forall k s, snd (fst (N.nstep base K event s (@N.NMark base K k))) =
    orb (snd (fst s)) (event k (fst (fst s)))) /\
  a2 (N.nstate base) (N.nmove base K) (N.nstep base K event)
    (N.ncost base K) (fun s => snd (fst s)) /\
  (forall s i, snd (fst s) = true -> snd (fst (N.nstep base K event s i)) = true) /\
  (forall s i, snd (N.nstep base K event s i) = snd s + N.ncost base K i).
Proof.
  repeat split.
  - intros h [[b r] l]; reflexivity.
  - intros k [[b r] l]; reflexivity.
  - intros k [[b r] l]; reflexivity.
  - intros [[b r] l] [h|k] H0 H1; cbn in *; [congruence|lia].
  - intros [[b r] l] [h|k] H; cbn in *; rewrite H; reflexivity.
  - intros [[b r] l] [h|k]; cbn; lia.
Qed.

Theorem canonical_unit_price_is_least_when_events_possible :
  (forall k, exists b, event k b = true) ->
  forall cost, a2 (N.nstate base) (N.nmove base K) (N.nstep base K event)
    cost (fun s => snd (fst s)) ->
  forall i, N.ncost base K i <= cost i.
Proof.
  intros possible cost H [h|k]; cbn; [lia|].
  destruct (possible k) as [b E].
  apply (H (b,false,0) (@N.NMark base K k)); cbn; [reflexivity|exact E].
Qed.
End CanonicalWitness.
