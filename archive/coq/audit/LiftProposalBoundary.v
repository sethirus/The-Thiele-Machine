(* The actual neutral lift can forget a competitor's horizontal history.
   The reverse step-preserving map need not exist, even on reachable states.
   The competitor obeys exact latch, unit accounting, permanence and a2.
   LiftTerminal supplies the positive universal property in the other direction. *)
From Coq Require Import List Bool Arith Lia.
From Kernel Require Import CostSemanticsComparison.
From Audit Require Import LeastToll.
Require Minimal.ThieleComplete Minimal.NeutralComplete.
Import ListNotations.
Module T := Minimal.ThieleComplete.
Module N := Minimal.NeutralComplete.


Definition base : T.machine :=
  T.mk_machine bool unit (fun b _ => negb b) (fun _ => 0) (fun _ => false).
(* Every mark is enabled in this counterexample. *)
Definition canonical := N.nlift base unit (fun _ _ => true).
Definition C := T.m_state canonical.
Definition h : T.m_move canonical := @N.NBase base unit tt.
Definition v : T.m_move canonical := @N.NMark base unit tt.
Definition start : C := (false, false, 0).

(* The extra coordinate counts horizontal moves, which have cost zero.
   It is independent of the exact priced ledger. *)
Definition X := (C * nat)%type.
Definition xstep (x : X) (i : T.m_move canonical) : X :=
  (T.m_step canonical (fst x) i,
   match i with N.NBase _ => S (snd x) | N.NMark _ => snd x end).
Definition xview (x : X) := fst (fst (fst x)).
Definition xread (x : X) := snd (fst (fst x)).
Definition xledger (x : X) := snd (fst x).
Definition xstart : X := (start, 0).

Theorem competing_extension_laws :
  (forall b, exists x, xview x = b) /\
  xread xstart = false /\ xledger xstart = 0 /\
  (forall x, xview (xstep x h) = negb (xview x)) /\
  T.m_cost canonical h = 0 /\
  (forall x, xview (xstep x v) = xview x) /\
  (forall x, xread (xstep x v) = orb (xread x) true) /\
  (forall x i, xread x = true -> xread (xstep x i) = true) /\
  a2 X (T.m_move canonical) xstep (T.m_cost canonical) xread /\
  (forall x i, xledger (xstep x i) = xledger x + T.m_cost canonical i).
Proof.
  repeat split.
  - intro b; exists ((b, false, 0), 0); reflexivity.
  - intros [[[b r] l] n]; reflexivity.
  - intros [[[b r] l] n]; reflexivity.
  - intros [[[b r] l] n]; reflexivity.
  - intros [[[b r] l] n] [u|u] H; cbn in *; [exact H|apply orb_true_r].
  - intros [[[b r] l] n] [u|u] H0 H1; cbn in *; [congruence|lia].
  - intros [[[b r] l] n] [u|u]; cbn; lia.
Qed.

Theorem canonical_horizontal_loop : forall c,
  T.m_step canonical (T.m_step canonical c h) h = c.
Proof. intros [[b r] l]; cbn; rewrite negb_involutive; reflexivity. Qed.

Theorem competing_horizontal_loop_never_closes : forall x,
  xstep (xstep x h) h <> x.
Proof.
  intros [[[b r] l] n] E.
  apply (f_equal (@snd C nat)) in E; cbn in E; lia.
Qed.

(* Even horizontal commutation on reachable canonical states is impossible.
   Adding start, view, reading or ledger requirements cannot restore a map. *)
Theorem no_map_even_on_reachable_states :
  ~ exists f : C -> X, forall w,
    f (T.m_step canonical (T.run canonical w start) h) =
    xstep (f (T.run canonical w start)) h.
Proof.
  intros [f H].
  pose proof (H []) as H0; pose proof (H [h]) as H1.
  change (f (T.m_step canonical start h) = xstep (f start) h) in H0.
  change (f (T.m_step canonical (T.m_step canonical start h) h) =
    xstep (f (T.m_step canonical start h)) h) in H1.
  rewrite canonical_horizontal_loop, H0 in H1.
  apply (competing_horizontal_loop_never_closes (f start)); symmetry; exact H1.
Qed.

Theorem forgetting_extra_history_commutes : forall x i,
  fst (xstep x i) = T.m_step canonical (fst x) i.
Proof. reflexivity. Qed.
